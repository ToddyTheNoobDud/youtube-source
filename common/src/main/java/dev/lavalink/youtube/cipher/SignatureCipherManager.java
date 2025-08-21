package dev.lavalink.youtube.cipher;

import com.sedmelluq.discord.lavaplayer.tools.DataFormatTools;
import com.sedmelluq.discord.lavaplayer.tools.ExceptionTools;
import com.sedmelluq.discord.lavaplayer.tools.io.HttpClientTools;
import com.sedmelluq.discord.lavaplayer.tools.io.HttpInterface;
import dev.lavalink.youtube.YoutubeSource;
import dev.lavalink.youtube.cipher.ScriptExtractionException.ExtractionFailureType;
import dev.lavalink.youtube.track.format.StreamFormat;
import org.apache.http.client.methods.CloseableHttpResponse;
import org.apache.http.client.methods.HttpGet;
import org.apache.http.client.utils.URIBuilder;
import org.apache.http.util.EntityUtils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.mozilla.javascript.engine.RhinoScriptEngineFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.script.ScriptEngine;
import javax.script.ScriptException;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.atomic.LongAdder;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.sedmelluq.discord.lavaplayer.tools.ExceptionTools.throwWithDebugInfo;

@SuppressWarnings({"RegExpRedundantEscape", "RegExpUnnecessaryNonCapturingGroup"})
public class SignatureCipherManager {
  private static final Logger log = LoggerFactory.getLogger(SignatureCipherManager.class);

  private static final RhinoScriptEngineFactory RHINO_FACTORY = new RhinoScriptEngineFactory();
  private static final String YOUTUBE_EMBED_URL = "https://www.youtube.com/embed/";
  private static final String YOUTUBE_HOST = "https://www.youtube.com";
  private static final String JSURL_PREFIX = "\"jsUrl\":\"";

  private static final int MAX_CACHE_SIZE = 200;
  private static final int MAX_DUMPED_SCRIPTS = 100;
  private static final int CACHE_CLEANUP_THRESHOLD = 250;
  private static final long SCRIPT_CACHE_TTL_MS = TimeUnit.DAYS.toMillis(1);

  private static final String VARIABLE_PART = "[\\w$]+";
  private static final String VAR_DECL = "[\"']?[\\w$]+[\"']?";

  private static final Pattern TIMESTAMP_PATTERN = Pattern.compile("(?:signatureTimestamp|sts):(\\d+)");

  private static final Pattern GLOBAL_VARS_PATTERN = Pattern.compile(
      "(?:'use\\s*strict';)?(?<code>var\\s*(?<varname>[\\w$]+)\\s*=\\s*" +
      "(?:(?<strval>[\"'][^\"']*[\"'])(?:\\.split\\([\"'][^\"']*[\"']\\))?|" +
      "\\[(?:[\"'][^\"']*[\"']\\s*,?\\s*)*\\]))"
  );

  private static final Pattern ACTIONS_PATTERN = Pattern.compile(
      "var\\s+([\\w$]+)\\s*=\\s*\\{(?:\\s*" + VAR_DECL + "\\s*:\\s*function\\s*\\([^)]*\\)\\s*\\{[^}]*\\}\\s*,?){3}\\s*\\};"
  );

  private static final Pattern SIG_FUNCTION_PATTERN = Pattern.compile(
      "function(?:\\s+" + VARIABLE_PART + ")?\\((" + VARIABLE_PART + ")\\)\\{[^}]*\\(\\1,\\d+\\);return\\s*\\1[^}]*\\};"
  );

  private static final Pattern N_FUNCTION_PATTERN = Pattern.compile(
      "function\\([^)]+\\)\\{[^}]*catch\\([^)]+\\)\\{[^}]*return[^}]+\\}[^}]*return[^}]+\\};",
      Pattern.DOTALL
  );

  private final ConcurrentMap<String, SignatureCipher> cipherCache;
  private final ConcurrentMap<String, Boolean> dumpedScriptUrls;
  private final ThreadLocal<ScriptEngine> scriptEngineThreadLocal;
  private final AtomicReference<CachedPlayerScript> cachedPlayerScriptRef;
  private final LongAdder cacheHitCounter;
  private final LongAdder cacheMissCounter;

  private volatile boolean cacheCleanupInProgress = false;

  public SignatureCipherManager() {
    this.cipherCache = new ConcurrentHashMap<>(64, 0.75f, 16);
    this.dumpedScriptUrls = new ConcurrentHashMap<>(32, 0.75f, 8);
    this.scriptEngineThreadLocal = ThreadLocal.withInitial(RHINO_FACTORY::getScriptEngine);
    this.cachedPlayerScriptRef = new AtomicReference<>();
    this.cacheHitCounter = new LongAdder();
    this.cacheMissCounter = new LongAdder();
  }

  @NotNull
  public URI resolveFormatUrl(@NotNull HttpInterface httpInterface,
                              @NotNull String playerScript,
                              @NotNull StreamFormat format) throws IOException {
    final String signature = format.getSignature();
    final String nParameter = format.getNParameter();
    final URI initialUrl = format.getUrl();

    if ((signature == null || signature.isEmpty()) &&
        (nParameter == null || nParameter.isEmpty())) {
      return initialUrl;
    }

    final URIBuilder uri = new URIBuilder(initialUrl);
    final SignatureCipher cipher = getCipherScript(httpInterface, playerScript);
    final ScriptEngine engine = scriptEngineThreadLocal.get();

    if (signature != null && !signature.isEmpty()) {
      try {
        uri.setParameter(format.getSignatureKey(), cipher.apply(signature, engine));
      } catch (ScriptException | NoSuchMethodException e) {
        handleScriptError(cipher.rawScript, playerScript, "signature", signature, e);
      }
    }

    if (nParameter != null && !nParameter.isEmpty()) {
      try {
        final String transformed = cipher.transform(nParameter, engine);

        if (isTransformationProblematic(nParameter, transformed)) {
          if (log.isWarnEnabled()) {
            log.warn("N parameter transformation issue (in: {}, out: {}, script: {})",
                nParameter, transformed, playerScript);
          }
        }

        if (transformed != null) {
          uri.setParameter("n", transformed);
        }
      } catch (ScriptException | NoSuchMethodException e) {
        handleScriptError(cipher.rawScript, playerScript, "n parameter", nParameter, e);
      }
    }

    try {
      return uri.build();
    } catch (URISyntaxException e) {
      throw new RuntimeException("Invalid URI construction", e);
    }
  }

  private static boolean isTransformationProblematic(String input, String output) {
    return output == null ||
           input.equals(output) ||
           output.startsWith("enhanced_except_") ||
           output.endsWith("_w8_" + input);
  }

  private void handleScriptError(String script, String playerScript, String paramType,
                                String paramValue, Exception e) {
    if (script != null) {
      dumpProblematicScript(script, playerScript,
          String.format("Can't transform %s parameter %s", paramType, paramValue));
    }

  }

  private CachedPlayerScript getPlayerScript(@NotNull HttpInterface httpInterface) throws IOException {
    try (CloseableHttpResponse response = httpInterface.execute(new HttpGet(YOUTUBE_EMBED_URL))) {
      HttpClientTools.assertSuccessWithContent(response, "fetch player script (embed)");

      final String responseText = EntityUtils.toString(response.getEntity(), StandardCharsets.UTF_8);
      final int startIdx = responseText.indexOf(JSURL_PREFIX);

      if (startIdx == -1) {
        throw throwWithDebugInfo(log, null, "no jsUrl found", "html", responseText);
      }

      final int urlStart = startIdx + JSURL_PREFIX.length();
      final int endIdx = responseText.indexOf('"', urlStart);
      final String scriptUrl = responseText.substring(urlStart, endIdx);

      final CachedPlayerScript newScript = new CachedPlayerScript(scriptUrl);
      cachedPlayerScriptRef.set(newScript);
      return newScript;
    }
  }

  public CachedPlayerScript getCachedPlayerScript(@NotNull HttpInterface httpInterface) throws IOException {
    CachedPlayerScript current = cachedPlayerScriptRef.get();
    final long now = System.currentTimeMillis();

    if (current == null || now >= current.expireTimestampMs) {

      synchronized (this) {
        current = cachedPlayerScriptRef.get();
        if (current == null || now >= current.expireTimestampMs) {
          cacheMissCounter.increment();
          return getPlayerScript(httpInterface);
        }
      }
    }

    cacheHitCounter.increment();
    return current;
  }

  public SignatureCipher getCipherScript(@NotNull HttpInterface httpInterface,
                                         @NotNull String cipherScriptUrl) throws IOException {
    SignatureCipher cached = cipherCache.get(cipherScriptUrl);
    if (cached != null) {
      cacheHitCounter.increment();
      return cached;
    }

    cacheMissCounter.increment();

    if (cipherCache.size() > CACHE_CLEANUP_THRESHOLD && !cacheCleanupInProgress) {
      cleanupCache();
    }

    synchronized (this) {

      cached = cipherCache.get(cipherScriptUrl);
      if (cached != null) {
        return cached;
      }

      if (log.isDebugEnabled()) {
        log.debug("Parsing player script {}", cipherScriptUrl);
      }

      final URI scriptUri = parseTokenScriptUrl(cipherScriptUrl);
      try (CloseableHttpResponse response = httpInterface.execute(new HttpGet(scriptUri))) {
        final int statusCode = response.getStatusLine().getStatusCode();

        if (!HttpClientTools.isSuccessWithContent(statusCode)) {
          throw new IOException(String.format(
              "Received non-success response code %d from script url %s (%s)",
              statusCode, cipherScriptUrl, scriptUri));
        }

        final String script = EntityUtils.toString(response.getEntity(), StandardCharsets.UTF_8);
        final SignatureCipher cipher = extractFromScript(script, cipherScriptUrl);
        cipherCache.put(cipherScriptUrl, cipher);

        return cipher;
      }
    }
  }

  private void cleanupCache() {
    if (cacheCleanupInProgress) {
      return;
    }

    Thread.ofVirtual().name("cipher-cache-cleanup").start(() -> {
      try {
        cacheCleanupInProgress = true;

        if (cipherCache.size() > MAX_CACHE_SIZE) {

          final int toRemove = cipherCache.size() - MAX_CACHE_SIZE + 10;
          cipherCache.entrySet().stream()
              .limit(toRemove)
              .forEach(entry -> cipherCache.remove(entry.getKey()));
        }

        if (dumpedScriptUrls.size() > MAX_DUMPED_SCRIPTS) {
          dumpedScriptUrls.clear();
        }

      } finally {
        cacheCleanupInProgress = false;
      }
    });
  }

  private void dumpProblematicScript(@NotNull String script, @NotNull String sourceUrl,
                                     @NotNull String issue) {
    if (dumpedScriptUrls.putIfAbsent(sourceUrl, Boolean.TRUE) != null) {
      return;
    }

    Thread.ofVirtual().name("script-dumper").start(() -> {
      try {
        final Path path = Files.createTempFile("lavaplayer-yt-player-script", ".js");
        Files.write(path, script.getBytes(StandardCharsets.UTF_8));

        log.error("Problematic YouTube player script {} detected (issue: {}). Dumped to {} (Version: {})",
            sourceUrl, issue, path.toAbsolutePath(), YoutubeSource.VERSION);
      } catch (Exception e) {
        log.error("Failed to dump problematic YouTube player script {} (issue: {})", sourceUrl, issue, e);
      }
    });
  }

  private SignatureCipher extractFromScript(@NotNull String script, @NotNull String sourceUrl) {

    Matcher scriptTimestamp = TIMESTAMP_PATTERN.matcher(script);
    if (!scriptTimestamp.find()) {
      scriptExtractionFailed(script, sourceUrl, ExtractionFailureType.TIMESTAMP_NOT_FOUND);
    }

    Matcher globalVarsMatcher = GLOBAL_VARS_PATTERN.matcher(script);
    if (!globalVarsMatcher.find()) {
      scriptExtractionFailed(script, sourceUrl, ExtractionFailureType.VARIABLES_NOT_FOUND);
    }

    Matcher sigActionsMatcher = ACTIONS_PATTERN.matcher(script);
    if (!sigActionsMatcher.find()) {
      scriptExtractionFailed(script, sourceUrl, ExtractionFailureType.SIG_ACTIONS_NOT_FOUND);
    }

    Matcher sigFunctionMatcher = SIG_FUNCTION_PATTERN.matcher(script);
    if (!sigFunctionMatcher.find()) {
      scriptExtractionFailed(script, sourceUrl, ExtractionFailureType.DECIPHER_FUNCTION_NOT_FOUND);
    }

    Matcher nFunctionMatcher = N_FUNCTION_PATTERN.matcher(script);
    if (!nFunctionMatcher.find()) {
      scriptExtractionFailed(script, sourceUrl, ExtractionFailureType.N_FUNCTION_NOT_FOUND);
    }

    final String timestamp = scriptTimestamp.group(1);
    final String globalVars = globalVarsMatcher.group("code");
    final String sigActions = sigActionsMatcher.group(0);
    final String sigFunction = sigFunctionMatcher.group(0);
    String nFunction = nFunctionMatcher.group(0);

    final int paramStart = nFunction.indexOf('(') + 1;
    final int paramEnd = nFunction.indexOf(')', paramStart);
    if (paramStart > 0 && paramEnd > paramStart) {
      final String nfParameterName = nFunction.substring(paramStart, paramEnd).trim();

      nFunction = nFunction.replaceFirst(
          "if\\s*\\(typeof\\s*[^\\s()]+\\s*===?[\\s\\S]*?\\)\\s*return\\s*" +
          Pattern.quote(nfParameterName) + "\\s*;?",
          ""
      );
    }

    return new SignatureCipher(timestamp, globalVars, sigActions, sigFunction, nFunction, script);
  }

  private void scriptExtractionFailed(String script, String sourceUrl, ExtractionFailureType failureType) {
    dumpProblematicScript(script, sourceUrl, "must find " + failureType.friendlyName);
    throw new ScriptExtractionException("Must find " + failureType.friendlyName + " from script: " + sourceUrl, failureType);
  }

  private List<String> getQuotedFunctions(@Nullable String... functionNames) {
    return Stream.of(functionNames)
        .filter(Objects::nonNull)
        .map(Pattern::quote)
        .collect(Collectors.toList());
  }

  private static URI parseTokenScriptUrl(@NotNull String urlString) {
    try {
      if (urlString.startsWith("//")) {
        return new URI("https:" + urlString);
      } else if (urlString.startsWith("/")) {
        return new URI(YOUTUBE_HOST + urlString);
      } else {
        return new URI(urlString);
      }
    } catch (URISyntaxException e) {
      throw new RuntimeException("Invalid script URL: " + urlString, e);
    }
  }

  public String getCacheStats() {
    final long hits = cacheHitCounter.sum();
    final long misses = cacheMissCounter.sum();
    final long total = hits + misses;
    final double hitRate = total > 0 ? (double) hits / total * 100 : 0;

    return String.format("Cache Stats - Size: %d, Hits: %d, Misses: %d, Hit Rate: %.2f%%",
        cipherCache.size(), hits, misses, hitRate);
  }

  public void cleanup() {
    scriptEngineThreadLocal.remove();
  }

  public static class CachedPlayerScript {
    public final String url;
    public final long expireTimestampMs;

    protected CachedPlayerScript(@NotNull String url) {
      this.url = url;
      this.expireTimestampMs = System.currentTimeMillis() + SCRIPT_CACHE_TTL_MS;
    }
  }
}
