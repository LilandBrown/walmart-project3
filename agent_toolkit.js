'use strict';
// Walmart Toolkit agent — the cart agent and the checkout agent, merged.
//
// WHY THEY HAD TO MERGE: both hooked
// com.apollographql.apollo3.api.http.DefaultHttpRequestComposer.compose. Two frida
// scripts assigning .implementation to one Java method do not compose — the second
// replaces the first — so running both tools at once meant one of them silently
// stopped capturing. There is now ONE hook, dispatching on the operation name.
//
// Three jobs, deliberately independent (see DOCUMENTATION.md §6, §7, §10):
//
//   capture — the one composer hook documents the app's add-to-cart mutations AND the
//             two checkout operations, each governed by its own mode.
//   peek    — for a checkout call that reaches the network, a hook on okhttp's
//             Chain.proceed reads the reply NON-destructively, so the contractId /
//             order result is reported while the app still gets its copy.
//   send    — build a request ourselves and dispatch it through the app's own
//             OkHttpClient, whose interceptor chain mints the PerimeterX token and the
//             x-o-* envelope for OUR request. One function serves both tools: with an
//             item it is the cart's direct send (item substituted into a template),
//             without one it is the checkout's verbatim replay.
//
// Discovery is shared too. Both agents used to resolve okio/okhttp off PerimeterX
// separately; there is now one `H`, built in two stages so the cheap half (needed to
// peek a response) does not pay for the expensive half (needed to send).
Java.perform(function () {
  var JString = Java.use('java.lang.String');
  var IOEx = Java.use('java.io.IOException');
  var Thread = Java.use('java.lang.Thread');
  var ListIface = Java.use('java.util.List');
  var Closeable = Java.use('java.io.Closeable');
  var HttpBody = Java.use('com.apollographql.apollo3.api.http.HttpBody');

  // --- discover the (obfuscated) okio classes so this survives app updates ---
  // 1) BufferedSink = the parameter type of HttpBody.writeTo(...)
  var sinkName = null;
  var hbm = HttpBody.class.getDeclaredMethods();
  for (var i = 0; i < hbm.length; i++) {
    if (('' + hbm[i].getName()) === 'writeTo') sinkName = '' + hbm[i].getParameterTypes()[0].getName();
  }
  var SinkIface = Java.use(sinkName);

  // 2) sink.write(byte[]) method name
  var writeBytesName = null;
  var sm = SinkIface.class.getDeclaredMethods();
  for (var j = 0; j < sm.length; j++) {
    var ps = sm[j].getParameterTypes();
    if (ps.length === 1 && ('' + ps[0].getName()) === '[B') { writeBytesName = '' + sm[j].getName(); break; }
  }

  // 3) okio.Buffer (same package as sink) with a no-arg ctor + a 0-arg readByteArray()->byte[]
  var BufferCls = null, readBytesName = null;
  var pkg = sinkName.indexOf('.') > 0 ? sinkName.substring(0, sinkName.indexOf('.')) : '';
  var classes = Java.enumerateLoadedClassesSync();
  for (var c = 0; c < classes.length; c++) {
    var n = classes[c];
    if (pkg && n.indexOf(pkg + '.') !== 0) continue;
    try {
      var K = Java.use(n);
      if (!SinkIface.class.isAssignableFrom(K.class)) continue;
      var ctors = K.class.getDeclaredConstructors(), noArg = false;
      for (var k = 0; k < ctors.length; k++) if (ctors[k].getParameterTypes().length === 0) noArg = true;
      if (!noArg) continue;
      var kms = K.class.getDeclaredMethods(), rb = null;
      for (var m = 0; m < kms.length; m++) {
        if (kms[m].getParameterTypes().length === 0 && ('' + kms[m].getReturnType().getName()) === '[B') { rb = '' + kms[m].getName(); break; }
      }
      if (rb) { BufferCls = n; readBytesName = rb; break; }
    } catch (e) {}
  }
  var Buffer = Java.use(BufferCls);

  function readJson(httpReq) {
    var buf = Buffer.$new();
    httpReq.getBody().writeTo(Java.cast(buf, SinkIface));
    return '' + JString.$new(buf[readBytesName](), 'UTF-8');
  }

  function readJsonSafe(httpReq) {             // GETs have no body
    try { return httpReq.getBody() === null ? null : readJson(httpReq); }
    catch (e) { return null; }
  }

  // ==========================================================================
  // STATE
  // ==========================================================================

  // Add-to-cart mode. Two axes: does the agent *document* the add, and does it
  // *intercept* it (change or block what the app sends)?
  //   'view' — document: no.  intercept: no.  Nothing is even read; the app
  //            behaves exactly as if the agent were not loaded.
  //   'grab' — document: yes. intercept: no.  The add reaches Walmart untouched
  //            and is copied to the intercepted list. This is how you save an item.
  //   'hold' — document: yes. intercept: yes. The add is copied, then blocked, so
  //            nothing reaches Walmart.
  // Only 'hold' ever affects the app, and none of the three touch OUR sends — those
  // are built at the okhttp layer and never reach the composer hook.
  var mode = 'grab';

  // What the agent does with a checkout call the app makes. Each op has its OWN mode:
  //   'watch'     — DOCUMENT it; the call reaches Walmart and its RESPONSE is read too
  //                 (contractId for prep, the order result for commit). A PlaceOrder
  //                 the APP makes goes through and the order is placed.
  //   'intercept' — DOCUMENT it AND block it on-device: nothing reaches Walmart.
  //   'idle'      — pass through, log nothing; the body is not even read.
  //
  // These REPLACE the cart agent's old holdCheckout/watchCheckout pair, which was a
  // cruder version of the same thing (one flag for both ops, no response capture).
  // Setting PlaceOrder to 'intercept' is what the cart tool's "Block checkout" did.
  var modePrep   = 'watch';   // CreatePurchaseContract
  var modeCommit = 'watch';   // PlaceOrder

  // Read the response to a checkout call that actually reaches the network. On by
  // default; exposed over rpc so the host can turn it off if a build misbehaves.
  var captureResponses = true;

  var delayMs = 0, lastSend = 0;   // minimum gap enforced between consecutive sends

  // How long the agent is willing to hold a scheduled send. The JS runtime is
  // single-threaded: while we wait here, an app thread that hits one of our hooks
  // blocks too, so a long hold would freeze the app. The host does the long wait
  // and hands us the deadline only seconds out — see SCHEDULING in the host.
  var SCHED_MAX_WAIT = 30000;
  // The same ceiling on a burst, for the same reason: its rows are dispatched one
  // row delay apart from a single loop on this thread, so the whole span is time the
  // JS runtime is not answering the app's hooks.
  var BURST_MAX_SPAN = 30000;
  // Item ids that cannot resolve to a real offer. A send carrying them travels the
  // WHOLE path (okhttp discovery, PX token minting, TCP+TLS, the gateway) and comes
  // back rejected inside a 200, so it warms everything without touching the cart.
  var WARM_OFFER = '00000000000000000000000000000000', WARM_ITEM = '0000000000';

  // Operation families we care about (substring match on the Apollo operation name).
  var ADD_OP = 'UpdateQuantity';                // add-to-cart / quantity change
  var CHECKOUT_PREP = 'CreatePurchaseContract'; // prices+locks the cart, returns contractId
  var CHECKOUT_COMMIT = 'PlaceOrder';           // THE op that commits the order

  // Correlating a request (seen at the Apollo composer) with its response (seen at the
  // okhttp layer). Each documented, non-blocked checkout call gets a cid; the composer
  // stamps `pending[stage] = {cid, ts}`, and the okhttp Chain hook consumes it when the
  // matching request goes out, tagging the response with the same cid. The host stitches
  // the two together by cid. Any op in Watch mode can be pending; Intercept blocks both,
  // and a blocked call has no response to wait for.
  var cidSeq = 0;
  var pending = {};        // 'prep' | 'commit' -> {cid, ts}
  var pendingCount = 0;    // cheap gate: when 0, the okhttp hook is a pure passthrough
  var PENDING_TTL = 30000; // drop a stale pending after 30s (request never made the wire)

  // ==========================================================================
  // HELPERS
  // ==========================================================================

  // Wait so consecutive sends START >= delayMs apart, and report how long that
  // cost. The clock is stamped at dispatch, not at completion, so the throttle and
  // the round-trip overlap: the effective cadence is max(delayMs, rtt), not their
  // sum. Returns the ms actually slept.
  // `override` lets one caller pace itself without touching the global setting:
  // a timed run's follow-up rows carry their own delay, set in the Timed send
  // panel, which is deliberately separate from the bulk-send throttle.
  function pace(override) {
    var waited = 0;
    var d = (override === undefined || override === null) ? delayMs : (override | 0);
    if (d > 0) {
      var wait = d - (Date.now() - lastSend);
      if (wait > 0) {
        var w0 = Date.now();
        try { Thread.sleep(Math.floor(wait)); } catch (e) {}
        waited = Date.now() - w0;
      }
    }
    lastSend = Date.now();
    return waited;
  }

  // Wait until an absolute instant on THIS DEVICE's clock, and report how far off
  // we landed (+ve = late). The caller converts a host deadline into device time;
  // the device clock here is hundreds of ms off the host's, so the two are never
  // interchangeable (DOCUMENTATION.md §9).
  //
  // Thread.sleep() lands a few ms late under load, so sleep to 4 ms short and spin
  // the rest. Date.now() is ms-resolution, which is comfortably inside the ±10 ms
  // that one-way network jitter already costs — spinning longer buys nothing.
  function sleepUntilDev(t) {
    var left = t - Date.now();
    if (left > SCHED_MAX_WAIT) {
      throw new Error('scheduled dispatch is ' + left + ' ms out; the agent holds at most ' +
                      SCHED_MAX_WAIT + ' ms (a longer hold would stall the app) — arm closer in');
    }
    return sleepTo(t);
  }

  // The same wake-up discipline with no ceiling on the wait. Used for the gaps
  // BETWEEN a burst's rows, which are the operator's own row delay and are already
  // bounded as a whole by BURST_MAX_SPAN.
  function sleepTo(t) {
    var left = t - Date.now();
    if (left > 4) { try { Thread.sleep(Math.floor(left - 4)); } catch (e) {} }
    while (Date.now() < t) { /* spin the last few ms */ }
    return Date.now() - t;
  }

  function applyItem(json, t) {
    return json.replace(/"usItemId":"[^"]*"/g, '"usItemId":"' + t.usItemId + '"')
               .replace(/"offerId":"[^"]*"/g, '"offerId":"' + t.offerId + '"')
               .replace(/"quantity":[0-9.]+/g, '"quantity":' + t.quantity);
  }

  // Apollo-level request metadata, captured so a direct send can reproduce it.
  // These are the headers Apollo itself sets (X-APOLLO-*, Accept, Content-Type) —
  // the PerimeterX and x-o-* envelope is added later by okhttp's interceptors and
  // is deliberately NOT here: a stale PX token must never be replayed.
  function reqUrl(httpReq) {
    try { return '' + httpReq.getUrl(); } catch (e) { return null; }
  }
  function reqHeaders(httpReq) {
    var out = [];
    try {
      var L = Java.cast(httpReq.getHeaders(), ListIface);
      for (var i = 0; i < L.size(); i++) {
        var hh = L.get(i);
        out.push(['' + hh.getName(), '' + hh.getValue()]);
      }
    } catch (e) {}
    return out;
  }

  // Apollo's captured HttpRequest carries only the BASE url (…/orchestra/cartxo/graphql);
  // the persisted-query path (/<OperationName>/<sha256Hash>) is appended further down by
  // the app's own engine, which a direct send bypasses. Posting to the bare base url gets
  // a flat HTTP 400 from the gateway, so rebuild the full path from the body — both parts
  // are in there. See DOCUMENTATION.md §1, §7.
  function fullUrl(baseUrl, json) {
    var u = ('' + (baseUrl || '')).replace(/\/+$/, '');
    var op = /"operationName"\s*:\s*"([^"]+)"/.exec(json);
    var hash = /"sha256Hash"\s*:\s*"([^"]+)"/.exec(json);
    if (!op || !hash) return u;                 // nothing to append; send as captured
    var suffix = '/' + op[1] + '/' + hash[1];
    return u.indexOf(suffix) !== -1 ? u : u + suffix;
  }

  // ==========================================================================
  // THE ONE COMPOSER HOOK
  //
  // Dispatches on the operation name: checkout ops follow their own per-op mode,
  // add-to-cart follows the cart mode. The two branches share nothing but this
  // entry point, which is exactly the arrangement that stopped them being two
  // scripts fighting over one method.
  // ==========================================================================
  var C = Java.use('com.apollographql.apollo3.api.http.DefaultHttpRequestComposer');
  C.compose.implementation = function (apolloReq) {
    var httpReq = this.compose(apolloReq);
    try {
      var name = '' + apolloReq.getOperation().name();
      var isPrep   = name.indexOf(CHECKOUT_PREP) !== -1;
      var isCommit = name.indexOf(CHECKOUT_COMMIT) !== -1;

      // --- checkout ---------------------------------------------------------
      if (isPrep || isCommit) {
        var stage = isCommit ? 'commit' : 'prep';
        var m = isCommit ? modeCommit : modePrep;
        var intercepted = (m === 'intercept');
        var document = (m !== 'idle');   // idle logs nothing and reads nothing
        if (!document && !intercepted) return httpReq;
        var cid = ++cidSeq;

        // Document the call: operation name, url (carries the persisted-query hash),
        // Apollo headers, the full body (variables + extensions), which mode captured
        // it, its cid (so a later response can be matched to it), and whether it was
        // intercepted (blocked) or observed (passed through).
        if (document) {
          send({ type: 'checkout', op: name, stage: stage,
                 mode: m, intercepted: intercepted, cid: cid, ts: (new Date()).getTime(),
                 body: readJsonSafe(httpReq),
                 url: reqUrl(httpReq), headers: reqHeaders(httpReq) });
        }

        // Blocked on-device: the app gets an IOException instead of a network call, so
        // nothing reaches Walmart. It shows a generic "technical issue" — expected.
        // A blocked call never reaches the network, so it is NOT marked pending: there
        // is no response to wait for.
        if (intercepted) {
          if (document) send({ type: 'blocked', op: name, stage: stage });
          throw IOEx.$new('order-blocked-by-tool');
        }

        // Not blocked => it will hit the network. Arm the okhttp response hook (once)
        // and mark this stage pending so the hook knows to read the reply.
        if (document && captureResponses) {
          try {
            armResponseHooks();                 // idempotent; discovers + hooks on first use
            if (!pending[stage]) pendingCount++;
            pending[stage] = { cid: cid, ts: Date.now() };
          } catch (e) { send({ type: 'error', msg: 'arm-resp: ' + e }); }
        }
        return httpReq;
      }

      // --- add to cart ------------------------------------------------------
      if (name.indexOf(ADD_OP) !== -1) {
        // Only the APP's own adds reach here. Ours are built at the okhttp layer
        // and never pass through the composer, so there is nothing to exempt.
        if (mode === 'view') return httpReq;     // passive: don't even read the body

        var json = readJsonSafe(httpReq);
        if (json === null) return httpReq;       // bodyless: nothing to document or replace
        // url + Apollo headers ride along so a direct send can rebuild this exact
        // request later without the app having to make another one.
        send({ type: 'capture', op: name, ts: (new Date()).getTime(), body: json,
               url: reqUrl(httpReq), headers: reqHeaders(httpReq) });
        if (mode !== 'hold') return httpReq;     // grab: documented, otherwise untouched

        // hold — intercept: documented above, now blocked so nothing reaches Walmart.
        // Replacing the item is not done here; the GUI overwrites the intercepted
        // rows instead, and 'Send requests' dispatches them itself.
        send({ type: 'held', op: name, scope: 'add' });
        throw IOEx.$new('held-by-tool');
      }
    } catch (e) {
      var s = '' + e;
      if (s.indexOf('held-by-tool') !== -1 || s.indexOf('order-blocked-by-tool') !== -1) throw e;
      send({ type: 'error', msg: s });
    }
    return httpReq;
  };

  // ==========================================================================
  // OKHTTP DISCOVERY — one `H` for both tools, built in two stages.
  //
  // Everything is discovered at runtime rather than hardcoded: R8 renames okhttp on
  // every app update, so names like R61.A are build-specific. The one fixed point is
  // that PerimeterX ships its SDK un-obfuscated, and PXInterceptor implements okhttp's
  // Interceptor — that names okhttp's package for us.
  //
  //   discoverCore()  interceptor / chain / proceed / request / response, how to read
  //                   a response body, how to peek one non-destructively, and the two
  //                   timing longs. Cheap. Enough to hook Chain.proceed.
  //   discoverSend()  adds Builder, RequestBody, our body class, the client, newCall
  //                   and execute. This is the ~1073 ms half (DOCUMENTATION.md §9), so
  //                   peeking a checkout response does not pay for it.
  // ==========================================================================
  var PX_INTERCEPTOR = 'com.perimeterx.mobile_sdk.main.PXInterceptor';
  var H = null;              // discovered handles, built once

  function declaredMethods(clsName) {
    return Java.use(clsName).class.getDeclaredMethods();
  }
  function isJdk(n) { return /^(java|javax|kotlin|android|dalvik)\./.test(n); }

  function discoverCore() {
    if (H) return H;
    var h = {};

    // 1. okhttp Interceptor + Chain + Response, off PerimeterX's un-obfuscated interceptor.
    var ifs = Java.use(PX_INTERCEPTOR).class.getInterfaces();
    for (var i = 0; i < ifs.length; i++) {
      var ms = ifs[i].getDeclaredMethods();
      if (ms.length === 1 && ms[0].getParameterTypes().length === 1) {
        h.interceptor = '' + ifs[i].getName();
        h.chain       = '' + ms[0].getParameterTypes()[0].getName();
        h.response    = '' + ms[0].getReturnType().getName();
      }
    }
    if (!h.chain) throw new Error('PXInterceptor implements no okhttp Interceptor interface');
    h.pkg = h.interceptor.lastIndexOf('.') > 0
          ? h.interceptor.substring(0, h.interceptor.lastIndexOf('.')) : '';

    // 2. Request = the parameter of Chain.proceed(Request) -> Response, and proceed's
    //    name. Using proceed (1 arg) rather than request() disambiguates Request from
    //    Chain's other no-arg getters (connection(), call()).
    var cms = declaredMethods(h.chain);
    for (var j = 0; j < cms.length; j++) {
      var ps = cms[j].getParameterTypes();
      if (ps.length === 1 && ('' + cms[j].getReturnType().getName()) === h.response) {
        h.request = '' + ps[0].getName();
        h.proceed = '' + cms[j].getName();
      }
    }
    if (!h.request) throw new Error('could not resolve Request from ' + h.chain);

    // 3. Response body: R8 stripped the Kotlin body() getter, so the ResponseBody is
    //    reachable only as a FIELD. Nested Response fields (networkResponse /
    //    cacheResponse / priorResponse) are Closeable too, so the discriminator is
    //    "Closeable, not a Response, and yields String or byte[]". Per-candidate try:
    //    one unloadable type must not abort the whole search.
    try {
      var rfs = Java.use(h.response).class.getDeclaredFields();
      for (var r = 0; r < rfs.length && !h.respBodyField; r++) {
        try {
          var ft = '' + rfs[r].getType().getName();
          if (ft === h.response || isJdk(ft) || ft.indexOf('.') < 0) continue;
          var BK = Java.use(ft);
          if (!Closeable.class.isAssignableFrom(BK.class)) continue;
          var sms = BK.class.getDeclaredMethods();
          for (var s = 0; s < sms.length; s++) {
            if (sms[s].getParameterTypes().length !== 0) continue;
            var srt = '' + sms[s].getReturnType().getName();
            if (srt === 'java.lang.String' || srt === '[B') {
              h.respBodyField = '' + rfs[r].getName();
              h.respBodyCls   = ft;
              h.bodyRead      = '' + sms[s].getName();
              h.bodyIsBytes   = (srt === '[B');
              break;
            }
          }
        } catch (e) { /* try the next candidate */ }
      }
    } catch (e) { h.respBodyError = '' + e; }

    // 4. Non-destructive read of the response. First choice: Response.peekBody(long),
    //    which buffers a COPY and leaves the real body for the app to consume. It is a
    //    method on Response taking one long and returning the ResponseBody type.
    try {
      var pms = declaredMethods(h.response);
      for (var p = 0; p < pms.length && !h.peekBody; p++) {
        var pp = pms[p].getParameterTypes();
        if (pp.length === 1 && ('' + pp[0].getName()) === 'long' &&
            ('' + pms[p].getReturnType().getName()) === h.respBodyCls) {
          h.peekBody = '' + pms[p].getName();
        }
      }
    } catch (e) {}

    // 5. Fallback if peekBody was stripped: ResponseBody.source().peek().readByteArray().
    //    okio's peek() returns a NEW BufferedSource that reads ahead without consuming
    //    the original — also non-destructive. source() is the ResponseBody's no-arg
    //    getter returning an okio type that has both a no-arg [B reader (readByteArray)
    //    and a no-arg self-returning method (peek).
    if (!h.peekBody && h.respBodyCls) {
      try {
        var bms = declaredMethods(h.respBodyCls);
        for (var b = 0; b < bms.length && !h.srcGetter; b++) {
          if (bms[b].getParameterTypes().length !== 0) continue;
          var brt = '' + bms[b].getReturnType().getName();
          if (isJdk(brt) || brt.indexOf('.') < 0 || brt === h.respBodyCls) continue;
          var SK; try { SK = Java.use(brt); } catch (e) { continue; }
          var sms2 = SK.class.getDeclaredMethods(), rd = null, pk = null;
          for (var q = 0; q < sms2.length; q++) {
            if (sms2[q].getParameterTypes().length !== 0) continue;
            var qrt = '' + sms2[q].getReturnType().getName();
            if (qrt === '[B' && !rd) rd = '' + sms2[q].getName();
            if (qrt === brt && !pk) pk = '' + sms2[q].getName();
          }
          if (rd && pk) { h.srcGetter = '' + bms[b].getName(); h.srcType = brt; h.srcRead = rd; h.srcPeek = pk; }
        }
      } catch (e) {}
    }

    // 6. Response.sentRequestAtMillis / receivedResponseAtMillis. okhttp stamps these
    //    itself: the first when the request bytes actually go on the wire (so AFTER the
    //    whole interceptor chain, PX token minting included), the second when the
    //    response headers land. They are the only two `long` fields on Response, and
    //    they split our round-trip into "our own pre-flight work" and "time on the
    //    wire" — which is what tells you how far ahead of a deadline to dispatch.
    //    Optional: without them we still report the outer round-trip.
    h.respLongs = [];
    try {
      var lfs = Java.use(h.response).class.getDeclaredFields();
      for (var l = 0; l < lfs.length; l++) {
        if (('' + lfs[l].getType().getName()) === 'long') h.respLongs.push('' + lfs[l].getName());
      }
    } catch (e) {}

    H = h;
    return H;
  }

  function discoverSend() {
    var h = discoverCore();
    if (h.sendReady) return h;

    // 7. Request.Builder = the no-arg-returned class that can hand a Request back.
    var rms = declaredMethods(h.request);
    for (var k = 0; k < rms.length && !h.builder; k++) {
      if (rms[k].getParameterTypes().length !== 0) continue;
      var cand = '' + rms[k].getReturnType().getName();
      if (cand === h.request || cand.indexOf('.') < 0 || isJdk(cand)) continue;
      var bms = declaredMethods(cand);
      for (var m = 0; m < bms.length; m++) {
        if (bms[m].getParameterTypes().length === 0 &&
            ('' + bms[m].getReturnType().getName()) === h.request) {
          h.builder = cand; h.bBuild = '' + bms[m].getName(); break;
        }
      }
    }
    if (!h.builder) throw new Error('could not resolve Request.Builder');

    // 8. Builder members. R8 strips unused ones, so what survives is a small set:
    //    (String,String) = a header setter, (String, RequestBody) = method+body,
    //    and two single-String methods — url() and removeHeader() — which are
    //    told apart by probing, below.
    var singles = [];
    var bm2 = declaredMethods(h.builder);
    for (var n = 0; n < bm2.length; n++) {
      var bp = bm2[n].getParameterTypes(), nm = '' + bm2[n].getName();
      if (bp.length === 2 && ('' + bp[0].getName()) === 'java.lang.String') {
        if (('' + bp[1].getName()) === 'java.lang.String') h.bHeader = nm;
        else if (!isJdk('' + bp[1].getName())) { h.bMethod = nm; h.requestBody = '' + bp[1].getName(); }
      } else if (bp.length === 1 && ('' + bp[0].getName()) === 'java.lang.String') {
        singles.push(nm);
      }
    }
    if (!h.bHeader || !h.bMethod) throw new Error('could not resolve Builder header/method setters');

    // url() vs removeHeader(): build() throws without a url, so whichever one
    // lets a build succeed is url().
    var B = Java.use(h.builder);
    for (var s = 0; s < singles.length && !h.bUrl; s++) {
      try {
        var probe = B.$new();
        probe[singles[s]]('https://www.walmart.ca/');
        probe[h.bBuild]();
        h.bUrl = singles[s];
      } catch (e) {}
    }
    if (!h.bUrl) throw new Error('could not identify Builder.url() among ' + JSON.stringify(singles));

    // 9. RequestBody members: writeTo(BufferedSink) is the abstract one we must
    //    implement; contentLength()/contentType() we override so okhttp does not
    //    have to buffer or guess.
    var fms = declaredMethods(h.requestBody);
    for (var f = 0; f < fms.length; f++) {
      var fp = fms[f].getParameterTypes(), fn = '' + fms[f].getName();
      var rt = '' + fms[f].getReturnType().getName();
      if (fp.length === 1 && ('' + fp[0].getName()) === sinkName) h.rbWriteTo = fn;
      else if (fp.length === 0 && rt === 'long') h.rbLength = fn;
      else if (fp.length === 0 && !isJdk(rt) && rt.indexOf('.') > 0) {
        h.rbType = fn; h.mediaType = rt;
      }
    }
    if (!h.rbWriteTo) throw new Error('could not resolve RequestBody.writeTo');

    // 10. Our body class. contentType() returns null deliberately: okhttp's bridge
    //     only sets Content-Type from the body when it is non-null, so returning
    //     null lets the captured Apollo Content-Type header stand unduplicated.
    //     ONE class for both tools now — the two agents used to register
    //     com.wct.DirectBody and com.wcd.CheckoutBody separately, which is exactly
    //     the kind of duplication that merging removes.
    var spec = {};
    spec[h.rbWriteTo] = {
      returnType: 'void', argumentTypes: [sinkName],
      implementation: function (sink) { Java.cast(sink, SinkIface)[writeBytesName](this.payload.value); }
    };
    if (h.rbLength) {
      spec[h.rbLength] = { returnType: 'long', argumentTypes: [],
                           implementation: function () { return this.payload.value.length; } };
    }
    if (h.rbType) {
      spec[h.rbType] = { returnType: h.mediaType, argumentTypes: [],
                         implementation: function () { return null; } };
    }
    if (!h.Body) {
      h.Body = Java.registerClass({
        name: 'com.wmtk.ToolkitBody', superClass: Java.use(h.requestBody),
        fields: { payload: '[B' }, methods: spec
      });
    }

    // 11. The client class (JDK types R8 cannot rename), and Call.Factory.newCall.
    h.clientClasses = [];
    var all = Java.enumerateLoadedClassesSync();
    var pre = h.pkg === '' ? null : h.pkg + '.';
    for (var c = 0; c < all.length; c++) {
      var cn = all[c];
      if (cn.charAt(0) === '[') continue;
      if (pre === null ? cn.indexOf('.') >= 0 : cn.indexOf(pre) !== 0) continue;
      try {
        var flds = Java.use(cn).class.getDeclaredFields(), marks = 0, lists = 0;
        for (var q2 = 0; q2 < flds.length; q2++) {
          var ft2 = '' + flds[q2].getType().getName();
          if (ft2 === 'javax.net.ssl.SSLSocketFactory' || ft2 === 'java.net.ProxySelector' ||
              ft2 === 'javax.net.ssl.HostnameVerifier' || ft2 === 'java.net.Proxy') marks++;
          if (ft2 === 'java.util.List') lists++;
        }
        if (marks >= 2 && lists >= 1) h.clientClasses.push(cn);
      } catch (e) {}
    }
    if (!h.clientClasses.length) throw new Error('no OkHttpClient class found in package ' + h.pkg);

    for (var x = 0; x < h.clientClasses.length && !h.newCall; x++) {
      var kifs = Java.use(h.clientClasses[x]).class.getInterfaces();
      for (var y = 0; y < kifs.length; y++) {
        var kms2 = kifs[y].getDeclaredMethods();
        if (kms2.length === 1 && kms2[0].getParameterTypes().length === 1 &&
            ('' + kms2[0].getParameterTypes()[0].getName()) === h.request) {
          h.newCall = '' + kms2[0].getName();
          h.call = '' + kms2[0].getReturnType().getName();
          h.clientCls = h.clientClasses[x];
        }
      }
    }
    if (!h.newCall) throw new Error('no newCall(Request) on any client class');

    // 12. Call.execute() = the no-arg method returning Response.
    var callMs = declaredMethods(h.call);
    for (var e2 = 0; e2 < callMs.length; e2++) {
      if (callMs[e2].getParameterTypes().length === 0 &&
          ('' + callMs[e2].getReturnType().getName()) === h.response) h.execute = '' + callMs[e2].getName();
    }
    if (!h.execute) throw new Error('no execute() on ' + h.call);

    h.sendReady = true;
    return h;
  }

  // The client we want is the ONE instance carrying the full interceptor chain —
  // Walmart's identity/telemetry stack ending in PXInterceptor. Other live
  // clients have empty chains and would send a request with no PX token at all.
  function findPxClient(h) {
    if (h.client) {
      try { h.client.getClass(); return h.client; }   // still valid?
      catch (e) { h.client = null; }
    }
    var found = null, chain = null;
    h.clientClasses.forEach(function (cn) {
      if (found) return;
      try {
        Java.choose(cn, {
          onMatch: function (inst) {
            if (found) return;
            var flds = inst.getClass().getDeclaredFields();
            for (var i = 0; i < flds.length; i++) {
              try {
                flds[i].setAccessible(true);
                var v = flds[i].get(inst);
                if (v === null || !ListIface.class.isInstance(v)) continue;
                var L = Java.cast(v, ListIface), names = [];
                for (var j = 0; j < L.size(); j++) names.push('' + L.get(j).getClass().getName());
                if (names.some(function (n) { return /perimeterx|humansecurity/i.test(n); })) {
                  found = inst; chain = names; return;   // -> h.chainNames, NOT h.chain
                }
              } catch (e) {}
            }
          },
          onComplete: function () {}
        });
      } catch (e) {}
    });
    h.client = found;
    h.chainNames = chain;      // h.chain is the Interceptor.Chain CLASS — don't clobber it
    return found;
  }

  // ==========================================================================
  // RESPONSE PEEKING — a hook on okhttp's Chain.proceed, for checkout calls the
  // APP makes. Our own sends read their response directly (we own it); this exists
  // only because the app's copy must survive being read.
  // ==========================================================================
  var respArmed = false;        // have we attempted to install the Chain hook?
  var respHookCount = 0;        // how many concrete Chain.proceed methods we hooked

  // Resolve (once) the Request getter that yields the full request URL — the one whose
  // return value stringifies to an http(s) URL. The persisted-query path
  // (/<OperationName>/<sha256Hash>) is in that URL by the time the request is on the
  // okhttp chain, which is how we tell a CreatePurchaseContract request from any other.
  function resolveReqUrlGetter(h, req) {
    if (h.reqUrlTried) return;
    h.reqUrlTried = true;
    try {
      var ms = Java.use(h.request).class.getDeclaredMethods();
      for (var i = 0; i < ms.length; i++) {
        if (ms[i].getParameterTypes().length !== 0) continue;
        var rt = '' + ms[i].getReturnType().getName();
        if (rt === 'void' || rt.indexOf('.') < 0) continue;   // skip primitives
        var nm = '' + ms[i].getName();
        try {
          var v = req[nm]();
          if (v !== null && /^https?:\/\//.test('' + v)) { h.reqUrlGetter = nm; return; }
        } catch (e) {}
      }
    } catch (e) {}
  }

  // Peek the response body without consuming it. Returns the JSON text, null (no body),
  // or a short 'body unreadable: ...' note. Never throws.
  function readRespBody(h, resp) {
    try {
      if (h.peekBody) {
        var rb = resp[h.peekBody](1048576);          // cap at 1 MB; checkout replies are small
        if (rb === null) return null;
        var raw = Java.cast(rb, Java.use(h.respBodyCls))[h.bodyRead]();
        return h.bodyIsBytes ? ('' + JString.$new(raw, 'UTF-8')) : ('' + raw);
      }
      if (h.srcGetter && h.srcPeek && h.srcRead) {
        var fld = Java.use(h.response).class.getDeclaredField(h.respBodyField);
        fld.setAccessible(true);
        var body = fld.get(resp);
        if (body === null) return null;
        var src = Java.cast(body, Java.use(h.respBodyCls))[h.srcGetter]();
        var pk = src[h.srcPeek]();
        var bytes = pk[h.srcRead]();
        return '' + JString.$new(bytes, 'UTF-8');
      }
    } catch (e) { return 'body unreadable: ' + e; }
    return null;
  }

  // Read the full body of a response WE own (safe to consume — we close it after).
  function readOwnedRespBody(h, resp) {
    try {
      var fld = Java.use(h.response).class.getDeclaredField(h.respBodyField);
      fld.setAccessible(true);
      var rb = fld.get(resp);
      if (rb === null) return null;
      var raw = Java.cast(rb, Java.use(h.respBodyCls))[h.bodyRead]();
      return h.bodyIsBytes ? ('' + JString.$new(raw, 'UTF-8')) : ('' + raw);
    } catch (e) { return 'body unreadable: ' + e; }
  }

  // The hook installed on every concrete Chain.proceed. When a checkout stage is
  // pending, the FIRST hop whose request URL carries that op consumes the pending entry
  // (so exactly one hop reports), runs the real proceed, then peeks the reply. The gate
  // `pendingCount === 0` makes this a pure passthrough during ordinary navigation —
  // which matters more now than it did, because this hook is live whenever the toolkit
  // is attached, including while the cart half is being used.
  function makeProceedHook(h, mn) {
    return function (req) {
      if (pendingCount === 0 || !captureResponses) return this[mn](req);
      var stage = null, cid = null;
      try {
        if (!h.reqUrlGetter) resolveReqUrlGetter(h, req);
        var url = h.reqUrlGetter ? ('' + req[h.reqUrlGetter]()) : '';
        var st = url.indexOf(CHECKOUT_PREP) !== -1 ? 'prep'
               : (url.indexOf(CHECKOUT_COMMIT) !== -1 ? 'commit' : null);
        if (st && pending[st]) {
          if ((Date.now() - pending[st].ts) < PENDING_TTL) { stage = st; cid = pending[st].cid; }
          delete pending[st]; pendingCount--;      // consume (or drop-if-stale) either way
        }
      } catch (e) {}

      var resp = this[mn](req);                     // the real network round-trip

      if (cid !== null) {
        try {
          var code = null, cm = /code=(\d+)/.exec('' + resp);
          if (cm) code = parseInt(cm[1], 10);
          send({ type: 'checkout_response', cid: cid, stage: stage, code: code,
                 body: readRespBody(h, resp), ts: (new Date()).getTime() });
        } catch (e) { send({ type: 'error', msg: 'resp-cap: ' + e }); }
      }
      return resp;
    };
  }

  // Discover okhttp, then hook proceed() on every loaded concrete class implementing the
  // Chain interface. Called lazily on the first non-blocked checkout op, by which point
  // okhttp is long since loaded. Best-effort: any failure just leaves response capture
  // off, and the request side keeps working.
  function armResponseHooks() {
    if (respArmed) return respHookCount > 0;
    respArmed = true;
    try {
      var h = discoverCore();                       // cheap half only — no send discovery
      var ChainIface = Java.use(h.chain);
      var all = Java.enumerateLoadedClassesSync();
      for (var i = 0; i < all.length; i++) {
        var nm = all[i];
        if (nm.charAt(0) === '[') continue;
        if (h.pkg && nm.indexOf(h.pkg + '.') !== 0) continue;   // okhttp package only
        var K; try { K = Java.use(nm); } catch (e) { continue; }
        var impl = false;
        try { impl = (nm !== h.chain) && ChainIface.class.isAssignableFrom(K.class); } catch (e) { impl = false; }
        if (!impl) continue;
        var ms; try { ms = K.class.getDeclaredMethods(); } catch (e) { continue; }
        for (var m = 0; m < ms.length; m++) {
          var ps = ms[m].getParameterTypes();
          if (ps.length === 1 && ('' + ps[0].getName()) === h.request &&
              ('' + ms[m].getReturnType().getName()) === h.response) {
            var pn = '' + ms[m].getName();
            try {
              var meth = K[pn];
              var tgt = (meth.overloads && meth.overloads.length > 1) ? meth.overload(h.request) : meth;
              tgt.implementation = makeProceedHook(h, pn);
              respHookCount++;
            } catch (e) {}
          }
        }
      }
      send({ type: 'resp-armed', ok: respHookCount > 0, hooked: respHookCount,
             peekBody: !!h.peekBody, fallback: (!h.peekBody && !!h.srcGetter),
             chain: h.chain, response: h.response, respBodyCls: h.respBodyCls || null,
             respBodyField: h.respBodyField || null });
      return respHookCount > 0;
    } catch (e) {
      send({ type: 'resp-armed', ok: false, error: '' + e });
      return false;
    }
  }

  // ==========================================================================
  // BUILD / READ — the two halves of a send that are the same however it is
  // dispatched. Split out of directSend so a burst can build every row up front,
  // BEFORE its hold, and so its completion callback reports a response exactly the
  // way the blocking path does.
  // ==========================================================================

  // Assemble the okhttp Request for one send. Pure CPU: no I/O, nothing on the wire.
  // Returns {req, json, url, op}.
  function buildRequest(h, tmpl, item) {
    if (!tmpl || !tmpl.body) throw new Error('no captured request to build from');
    var json = item ? applyItem(tmpl.body, item) : tmpl.body;
    var url = fullUrl(tmpl.url, json);
    var b = Java.use(h.builder).$new();
    b[h.bUrl](url);
    // Replay whatever the capture carried, then fill in the Apollo envelope.
    //
    // HttpRequest.getHeaders() is EMPTY at compose time on this build — the
    // X-APOLLO-* headers are attached further down the app's own engine, the same
    // place the persisted-query path is appended. Without them the gateway answers
    // 400 "Something went wrong while processing the query."; with them it accepts
    // the request. Both values are derivable from the body. See DOCUMENTATION.md §3.
    var have = {};
    (tmpl.headers || []).forEach(function (kv) {
      if (/^content-length$/i.test(kv[0])) return;      // okhttp computes this
      try { b[h.bHeader](kv[0], kv[1]); have[('' + kv[0]).toLowerCase()] = 1; } catch (e) {}
    });
    function ensure(k, v) {
      if (v && !have[k.toLowerCase()]) { try { b[h.bHeader](k, v); } catch (e) {} }
    }
    var opM = /"operationName"\s*:\s*"([^"]+)"/.exec(json);
    var hashM = /"sha256Hash"\s*:\s*"([^"]+)"/.exec(json);
    ensure('X-APOLLO-OPERATION-NAME', opM && opM[1]);
    ensure('X-APOLLO-OPERATION-ID', hashM && hashM[1]);
    ensure('Accept', 'multipart/mixed; deferSpec=20220824, application/json');
    ensure('Content-Type', 'application/json');

    var body = h.Body.$new();
    body.payload.value = JString.$new(json).getBytes('UTF-8');
    b[h.bMethod]('POST', body);

    return { req: b[h.bBuild](), json: json, url: url, op: (opM && opM[1]) || null };
  }

  // Read everything we report about a dispatched request off its Response, then close
  // it. Shared by the blocking path and by a burst's completion callback — that
  // callback runs on one of okhttp's dispatcher threads, but it is handed the same
  // Response class, and these are the same discovered fields.
  function readResult(h, resp) {
    var summary = '' + resp;                            // "Response{... code=200 ...}"
    var m = /code=(\d+)/.exec(summary);
    var code = m ? parseInt(m[1], 10) : null;

    // Always read the payload, not just on a non-2xx. GraphQL reports failures
    // INSIDE a 200 via an "errors" array, so status alone would score a rejected
    // add as accepted. Responses here are small JSON.
    // NOT truncated. The cart agent used to cap this at 600 chars, which was fine when
    // the only caller logged an add-to-cart rejection — but a checkout replay's caller
    // parses the contractId out of a full priced-cart response, and 600 chars would cut
    // it off. The 600-char cap now applies only where it belongs: the log message.
    var detail = null;
    if (h.respBodyField && h.bodyRead) detail = readOwnedRespBody(h, resp);
    // okhttp's own stamps, read before the response is closed. Two epoch-ms longs:
    // the smaller is when the bytes went out, the larger when the reply landed.
    var wireOut = null, wireIn = null;
    if (h.respLongs && h.respLongs.length >= 2) {
      try {
        var vals = [];
        for (var w = 0; w < h.respLongs.length; w++) {
          var lf = Java.use(h.response).class.getDeclaredField(h.respLongs[w]);
          lf.setAccessible(true);
          var lv = lf.getLong(resp);
          if (lv > 1000000000000) vals.push(lv);       // epoch ms, not a timeout/size
        }
        if (vals.length >= 2) {
          vals.sort(function (a, b) { return a - b; });
          wireOut = vals[0]; wireIn = vals[vals.length - 1];
        }
      } catch (e) {}
    }
    try { Java.cast(resp, Closeable).close(); } catch (e) {}

    // A 2xx carrying a GraphQL "errors" array is a rejection wearing a success code.
    var gqlErrors = detail !== null && /"errors"\s*:\s*\[/.test(detail);
    return { summary: summary, code: code, detail: detail, gqlErrors: gqlErrors,
             wireOut: wireOut, wireIn: wireIn,
             accepted: code !== null && code >= 200 && code < 300 && !gqlErrors };
  }

  // ==========================================================================
  // SEND — one function for both tools.
  //
  // Build the request ourselves and dispatch it through the app's own OkHttpClient,
  // so its interceptor chain mints the PerimeterX token and the x-o-* envelope for
  // OUR request. Nothing of the app's is touched, nothing is armed, nobody taps
  // anything, and because it is assembled at the okhttp layer it never passes through
  // the composer hook above — so it cannot echo back into a captured list, and no
  // mode can block it.
  //
  //   item set   -> the cart's direct send: the template's item ids are replaced.
  //   item null  -> the checkout's replay: the captured body goes out verbatim.
  //
  // That single difference is the whole of what used to be two near-identical
  // functions in two agents.
  //
  // tmpl = {url, headers:[[k,v]...], body}; item = {offerId, usItemId, quantity} | null
  //
  // dry=true builds the request and stops: it proves the Builder/body/registerClass
  // path works without putting a single byte on the wire.
  //
  // o = optional {at, lead, quiet, delay}:
  //   at    — dispatch deadline as epoch ms ON THIS DEVICE's clock. Set, and the
  //           send is held until `at - lead` instead of being paced by delayMs.
  //   lead  — how far before `at` to dispatch, so the request ARRIVES at `at`.
  //   quiet — don't push a rejection out as an 'error' message (the warm-up send
  //           is rejected by design and must not read as a failure in the log).
  //   delay — pace this one send by this many ms instead of the global throttle.
  // ==========================================================================
  function directSend(tmpl, item, dry, o) {
    o = o || {};
    // Timings, all ms on the device's clock (see the `timing` field of the result):
    //   discover — okhttp/PX resolution. ~0 after the first send; H is cached.
    //   build    — assembling Request + body. Pure CPU, no I/O.
    //   wait     — how long the delayMs throttle actually slept before dispatch.
    //   rtt      — newCall().execute(): the whole interceptor chain (PX token minting
    //              included) plus the network round-trip. This is the real cost.
    //   read     — pulling the response body off the field.
    //   skew     — scheduled sends only: dispatch time minus the wake-up instant.
    var t0 = Date.now();
    var h = discoverSend();
    var client = findPxClient(h);
    if (!client) throw new Error('no OkHttpClient instance carrying a PerimeterX interceptor');
    var tDisc = Date.now();

    var built = buildRequest(h, tmpl, item);
    var json = built.json, url = built.url, req = built.req;
    var tBuilt = Date.now();
    if (dry) {
      return { ok: true, dry: true, request: '' + req, bytes: json.length,
               sentItem: item || null, op: built.op,
               interceptors: h.chainNames ? h.chainNames.length : null,
               timing: { discover: tDisc - t0, build: tBuilt - tDisc, total: tBuilt - t0 } };
    }

    // Everything above — discovery, the JSON rewrite, the Builder, the body — is
    // done BEFORE we start waiting, so the only work left between the wake-up and
    // the bytes going out is newCall().execute(). The throttle is deliberately
    // skipped on a scheduled send: delayMs exists to pace a bulk run, and letting
    // it hold here would push the send past the one instant it exists to hit.
    var waited = 0, wake = null, skew = null;
    if (o.at) {
      wake = o.at - (o.lead || 0);
      skew = sleepUntilDev(wake);
      lastSend = Date.now();      // keep the throttle's clock honest for later sends
    } else {
      waited = pace(o.delay);
    }
    var tSent = Date.now();
    var resp = client[h.newCall](req)[h.execute]();
    var tBack = Date.now();
    var r = readResult(h, resp);
    var tRead = Date.now();
    var summary = r.summary, code = r.code, detail = r.detail;
    var gqlErrors = r.gqlErrors, accepted = r.accepted;
    var wireOut = r.wireOut, wireIn = r.wireIn;

    // Also push the outcome out as a message. The rpc return carries `detail`, but
    // the gateway's own text is the difference between diagnosing a failure and
    // guessing at it, and the shared log is where it belongs.
    if (!accepted && detail !== null && !o.quiet) {
      send({ type: 'error', msg: 'direct send HTTP ' + code +
                                 (gqlErrors ? ' (graphql errors)' : '') + ' — ' +
                                 detail.substring(0, 600) });
    }

    return { ok: true, code: code, accepted: accepted, gqlErrors: gqlErrors,
             response: summary, detail: detail, url: url,
             op: built.op,
             // Top-level too, not just inside `timing`: the checkout half reads
             // result.rtt directly (it never had a `timing` block to look in).
             rtt: tBack - tSent,
             bytes: json.length, interceptors: h.chainNames ? h.chainNames.length : null,
             timing: { discover: tDisc - t0, build: tBuilt - tDisc, wait: waited,
                       rtt: tBack - tSent, read: tRead - tBack, total: tRead - t0,
                       sentAt: tSent, backAt: tBack,
                       // scheduled sends: what we aimed at and how close we got.
                       // arrival is wireOut + the caller's one-way estimate, i.e.
                       // when the request actually landed, in device-clock ms.
                       deadline: o.at || null, wake: wake, skew: skew,
                       lead: o.at ? (o.lead || 0) : null,
                       // preflight = our own chain before a byte leaves the device
                       // (PX token minting lives here); wire = out on the network,
                       // server work, and back.
                       preflight: wireOut === null ? null : wireOut - tSent,
                       wire: wireOut === null ? null : wireIn - wireOut,
                       wireOut: wireOut, wireIn: wireIn } };
  }

  // ==========================================================================
  // BURST — several add-to-carts in flight AT ONCE, spaced only by the row delay.
  //
  // WHY THIS EXISTS. directSend dispatches with Call.execute(), which blocks until
  // the reply is back — and it blocks on frida's single JS thread, so a run of rows
  // was strictly one-after-another: row N could not go out until row N-1 had come
  // back. The ~220 ms round-trip therefore set the spacing, and any row delay below
  // it did nothing at all (the host used to warn about exactly this). The rows were
  // sequential; the delay was a floor that was never the binding one.
  //
  // WHAT CHANGES. A burst uses Call.enqueue() instead. enqueue hands the call to
  // okhttp's own dispatcher thread pool and returns in well under a millisecond, so
  // the JS thread is free immediately and the round-trip is no longer in the loop.
  // Rows are then in flight concurrently, and the gap between their dispatches is
  // just the sleep we take between the enqueue calls — the row delay, and nothing
  // else. Row delay 0 puts them all on the wire together.
  //
  // WHAT IT COSTS. execute() ran the request on this thread, so dispatch and
  // bytes-out were the same instant. enqueue adds a hand-off to a pool thread, which
  // is sub-millisecond but not zero. That does NOT weaken the timing: arrival is
  // still measured from okhttp's own `sentRequestAtMillis` (wireOut), stamped when
  // the bytes actually leave, which is what the host's lead already aims with.
  //
  // Completions arrive on okhttp's threads and are collected into `bursts[id]`; the
  // host picks them up with burstresults(id). It has to be two calls, not one: while
  // this thread is dispatching it holds the JS lock, so no callback can run until it
  // returns.
  // ==========================================================================
  var bursts = {}, burstSeq = 0;

  // Resolve the async half of okhttp — enqueue(Callback) and the Callback interface —
  // the same way everything else here is resolved, by shape rather than by name, so it
  // survives the app's obfuscation:
  //   Call.enqueue     = the void method taking exactly one non-JDK interface
  //   Callback         = that interface; its two methods are told apart by their
  //                      second parameter (Response = onResponse, IOException = onFailure)
  function discoverAsync(h) {
    if (h.asyncReady || h.asyncError) return h;
    try {
      var cms = declaredMethods(h.call);
      for (var i = 0; i < cms.length && !h.enqueue; i++) {
        var ps = cms[i].getParameterTypes();
        if (ps.length !== 1 || ('' + cms[i].getReturnType().getName()) !== 'void') continue;
        var pn = '' + ps[0].getName();
        if (isJdk(pn) || pn.indexOf('.') < 0) continue;
        try { if (!Java.use(pn).class.isInterface()) continue; } catch (e) { continue; }
        h.enqueue = '' + cms[i].getName(); h.callbackIface = pn;
      }
      if (!h.enqueue) throw new Error('no enqueue(Callback) on ' + h.call);

      var kms = declaredMethods(h.callbackIface);
      for (var k = 0; k < kms.length; k++) {
        var kp = kms[k].getParameterTypes();
        if (kp.length !== 2) continue;
        var second = '' + kp[1].getName();
        if (second === h.response) h.cbOnResponse = '' + kms[k].getName();
        else if (second === 'java.io.IOException') h.cbOnFailure = '' + kms[k].getName();
      }
      if (!h.cbOnResponse || !h.cbOnFailure) {
        throw new Error('could not tell onResponse from onFailure on ' + h.callbackIface);
      }

      // One callback class for every burst. It carries no state of its own: the row
      // it belongs to is found by identity on the Call object we enqueued, which
      // okhttp hands straight back. Registering a class with a per-instance tag
      // field would work too, but this needs nothing from the class spec beyond the
      // two methods the interface already demands.
      if (!h.Callback) {
        var m = {};
        m[h.cbOnResponse] = {
          returnType: 'void', argumentTypes: [h.call, h.response],
          implementation: function (call, resp) { burstSettle(call, resp, null); }
        };
        m[h.cbOnFailure] = {
          returnType: 'void', argumentTypes: [h.call, 'java.io.IOException'],
          implementation: function (call, e) { burstSettle(call, null, '' + e); }
        };
        h.Callback = Java.registerClass({
          name: 'com.wmtk.ToolkitCallback',
          implements: [Java.use(h.callbackIface)], methods: m
        });
      }
      h.asyncReady = true;
    } catch (e) {
      h.asyncError = '' + e;
    }
    return h;
  }

  // okhttp's Dispatcher caps concurrent calls PER HOST at 5. Every row of a burst goes
  // to the same host, so from row 6 on they would sit in its ready queue and leave only
  // as earlier ones finish — reinstating, at a larger row count, exactly the
  // serialisation the burst exists to remove. Raise the cap to cover the burst.
  //
  // Best-effort and by shape: the dispatcher is the field on the client whose class
  // owns okhttp's call queues and the two int caps; the per-host cap is the smaller of
  // those ints (5 vs maxRequests' 64). If it does not look like that, we change nothing
  // and report what we found, so the host can say why rows bunched up.
  function dispatcherHeadroom(h, client, need) {
    if (h.perHostFld === undefined) {
      h.perHostFld = null; h.perHostOwner = null;
      try {
        var cf = client.getClass().getDeclaredFields();
        for (var i = 0; i < cf.length && !h.perHostFld; i++) {
          cf[i].setAccessible(true);
          var v = cf[i].get(client);
          if (v === null) continue;
          var dcls = v.getClass();
          var df = dcls.getDeclaredFields(), queues = 0, ints = [];
          for (var j = 0; j < df.length; j++) {
            var tn = '' + df[j].getType().getName();
            if (tn === 'java.util.ArrayDeque' || tn === 'java.util.Deque') queues++;
            if (tn === 'int') ints.push(df[j]);
          }
          if (queues < 2 || ints.length < 2) continue;   // not the dispatcher
          var lo = null;
          for (var q = 0; q < ints.length; q++) {
            ints[q].setAccessible(true);
            var val = ints[q].getInt(v);
            if (val <= 0) continue;
            if (lo === null || val < lo.val) lo = { fld: ints[q], val: val };
          }
          if (!lo) continue;
          h.perHostFld = lo.fld; h.perHostOwner = v; h.perHostOrig = lo.val;
        }
      } catch (e) { h.perHostFld = null; h.asyncNote = 'dispatcher not found: ' + e; }
    }
    if (!h.perHostFld) return { perHost: null, raised: false };
    try {
      var cur = h.perHostFld.getInt(h.perHostOwner);
      if (cur >= need) return { perHost: cur, raised: false };
      h.perHostFld.setInt(h.perHostOwner, need);
      return { perHost: need, raised: true, from: cur };
    } catch (e) {
      return { perHost: null, raised: false, error: '' + e };
    }
  }

  // Put the per-host cap back where the app had it. Called once a burst is collected.
  function dispatcherRestore(h) {
    if (!h || !h.perHostFld || h.perHostOrig === undefined) return null;
    try {
      h.perHostFld.setInt(h.perHostOwner, h.perHostOrig);
      return h.perHostOrig;
    } catch (e) { return null; }
  }

  // A row has come back (or failed). Runs on an okhttp dispatcher thread, so keep it
  // short: read the response, stash it, and get out.
  function burstSettle(call, resp, err) {
    var row = null;
    for (var id in bursts) {
      var rows = bursts[id].rows;
      for (var i = 0; i < rows.length; i++) {
        if (rows[i].done || rows[i].call === null) continue;
        try { if (rows[i].call.equals(call)) { row = rows[i]; break; } } catch (e) {}
      }
      if (row) break;
    }
    if (!row) {                          // burst already collected; nothing to record
      if (resp) { try { Java.cast(resp, Closeable).close(); } catch (e) {} }
      return;
    }
    var back = Date.now();
    if (err !== null) {
      row.result = { ok: false, error: err };
    } else {
      try {
        var r = readResult(H, resp);
        row.result = { ok: true, code: r.code, accepted: r.accepted, gqlErrors: r.gqlErrors,
                       response: r.summary, detail: r.detail, url: row.url, op: row.op,
                       bytes: row.bytes, rtt: back - row.sentAt,
                       timing: { rtt: back - row.sentAt, sentAt: row.sentAt, backAt: back,
                                 deadline: row.target, wake: row.wake, skew: row.skew,
                                 lead: row.lead, offset: row.offset,
                                 preflight: r.wireOut === null ? null : r.wireOut - row.sentAt,
                                 wire: r.wireOut === null ? null : r.wireIn - r.wireOut,
                                 wireOut: r.wireOut, wireIn: r.wireIn } };
      } catch (e) {
        row.result = { ok: false, error: 'response unreadable: ' + e };
      }
    }
    row.done = true;
    row.call = null;                     // let the Call go; identity is no longer needed
  }

  // Dispatch every row of `items` from one hold, `delay` ms apart, all in flight at
  // once. o = {at, lead, delay}: `at`/`lead` schedule ROW 1 exactly as schedulesend
  // does, and each later row is aimed at at + n*delay. Returns as soon as the last row
  // is on its way — the replies are collected by burstresults(id).
  function burstSend(tmpl, items, o) {
    o = o || {};
    var t0 = Date.now();
    var h = discoverSend();
    var client = findPxClient(h);
    if (!client) throw new Error('no OkHttpClient instance carrying a PerimeterX interceptor');
    discoverAsync(h);
    if (!h.asyncReady) throw new Error('parallel dispatch unavailable — ' + h.asyncError);
    if (!items || !items.length) throw new Error('a burst needs at least one item');
    var gap = Math.max(0, o.delay | 0);
    var span = gap * (items.length - 1);
    if (span > BURST_MAX_SPAN) {
      throw new Error('a ' + items.length + '-row burst ' + gap + ' ms apart spans ' + span +
                      ' ms; the agent dispatches for at most ' + BURST_MAX_SPAN +
                      ' ms (longer would stall the app) — shorten the row delay');
    }
    var tDisc = Date.now();

    // Build EVERY row before the hold, for the same reason a single scheduled send
    // builds before its own: the only work left between the wake-up and the bytes
    // going out must be the dispatch itself.
    var built = [];
    for (var i = 0; i < items.length; i++) built.push(buildRequest(h, tmpl, items[i]));
    var tBuilt = Date.now();

    var head = dispatcherHeadroom(h, client, items.length);

    var id = 'b' + (++burstSeq);
    var rows = [];
    for (i = 0; i < items.length; i++) {
      rows.push({ i: i, item: items[i], url: built[i].url, op: built[i].op,
                  bytes: built[i].json.length, offset: gap * i, target: null, wake: null,
                  skew: null, lead: o.at ? (o.lead || 0) : null, sentAt: null,
                  call: null, done: false, result: null });
    }
    bursts[id] = { id: id, rows: rows, created: t0, gap: gap, perHost: head.perHost };

    // Row 1 holds for the deadline; the rest are pure offsets from where it woke.
    var wake = o.at ? o.at - (o.lead || 0) : Date.now();
    var skew = o.at ? sleepUntilDev(wake) : 0;
    lastSend = Date.now();               // keep the throttle's clock honest for later sends

    var dispatched = 0, firstErr = null, prevOut = null;
    for (i = 0; i < rows.length; i++) {
      var due = wake + rows[i].offset;
      // The row delay is a SPACING between rows, not merely a target for each one.
      // Those targets are absolute — row n is aimed at wake + n*gap — so if the run
      // starts late (the deadline already past when we woke, or the lead overshot it)
      // every row whose target is ALSO in the past comes due at once, and they all
      // dispatch in the same millisecond with the delay silently gone. Hold each row
      // to at least `gap` after the one before it actually left, so a late start
      // costs the burst its deadline but never its spacing.
      if (i > 0 && gap > 0 && prevOut !== null && prevOut + gap > due) {
        due = prevOut + gap;
        rows[i].late = true;              // reported: this row was spaced, not targeted
      }
      rows[i].target = o.at ? o.at + rows[i].offset : null;
      rows[i].wake = due;
      if (i > 0) rows[i].skew = sleepTo(due);
      else rows[i].skew = skew;
      try {
        var call = client[h.newCall](built[i].req);
        rows[i].call = call;
        rows[i].sentAt = Date.now();
        call[h.enqueue](h.Callback.$new());
        dispatched++;
      } catch (e) {
        rows[i].done = true;
        rows[i].call = null;
        rows[i].result = { ok: false, error: '' + e };
        if (firstErr === null) firstErr = '' + e;
      }
      // Whether or not the enqueue took, this row's dispatch instant is the floor the
      // next row is spaced from — a row that failed still consumed its slot.
      prevOut = rows[i].sentAt !== null ? rows[i].sentAt : Date.now();
    }
    var tOut = Date.now();

    return { ok: true, id: id, n: rows.length, dispatched: dispatched, gap: gap,
             error: firstErr, perHost: head.perHost, perHostRaised: !!head.raised,
             perHostWas: head.from === undefined ? null : head.from,
             note: h.asyncNote || null,
             interceptors: h.chainNames ? h.chainNames.length : null,
             wake: wake, skew: skew, deadline: o.at || null,
             lead: o.at ? (o.lead || 0) : null,
             sentAt: rows.map(function (r) { return r.sentAt; }),
             // `span` is what the burst actually cost on the wire-side: first row
             // dispatched to last. With the round-trip out of the loop it should sit
             // within a millisecond or two of gap * (n-1).
             timing: { discover: tDisc - t0, build: tBuilt - tDisc, dispatch: tOut - wake,
                       span: rows[0].sentAt === null ? null : tOut - rows[0].sentAt,
                       total: tOut - t0 } };
  }

  // ==========================================================================
  // RPC — the union of what the two agents exposed.
  //
  // Two names had to change because both agents used them for different things:
  //   setmode(m)                  is the CART mode (view/grab/hold)
  //   setcheckoutmode(stage, m)   is the checkout per-op mode (was setmode(stage,m))
  // and getstate() now returns both tools' state in one object.
  // ==========================================================================
  rpc.exports = {
    // --- cart: send an add-to-cart built from a template, with the item swapped in.
    // Returns {ok:true, code, accepted, detail} or {ok:false, error}. Blocking: the
    // HTTP call runs on frida's thread (never the app's main looper), so the caller
    // must not be the GUI thread.
    // `delay` is optional: omitted, the global throttle applies; supplied, it
    // paces this send instead, so a timed run's follow-up rows can use their own.
    directsend: function (tmpl, item, delay) {
      try { return directSend(tmpl, item, false, { delay: delay }); }
      catch (e) { return { ok: false, error: '' + e }; }
    },
    // Same construction path, stopped before dispatch. Sends nothing.
    directdry: function (tmpl, item) {
      try { return directSend(tmpl, item, true); }
      catch (e) { return { ok: false, error: '' + e }; }
    },

    // --- checkout: replay a captured call verbatim (no item substitution).
    // CreatePurchaseContract returns a contractId; PlaceOrder COMMITS THE ORDER.
    // The host names the call; the agent just dispatches.
    sendcall: function (tmpl, delay) {
      try { return directSend(tmpl, null, false, { delay: delay }); }
      catch (e) { return { ok: false, error: '' + e }; }
    },

    // ---- scheduling --------------------------------------------------------
    // The device's clock, so the host can measure the offset between the two and
    // convert a host deadline into device time. They differ by hundreds of ms.
    nowdev: function () { return Date.now(); },

    // TCP handshake RTT to a host, measured FROM THIS DEVICE, in ms.
    //
    // This is the only way to get the one-way number honestly. okhttp's own stamps
    // bracket "bytes out -> reply in", which is one way + Walmart's server work +
    // one way back, and no amount of arithmetic splits that into its parts. A bare
    // TCP connect carries no server work at all, so it IS the network RTT, and one
    // way is half of it.
    //
    // It must run on the device: the emulator sits behind a BlueStacks NAT hop the
    // host does not traverse, so a handshake timed on the host understates it.
    // The first sample pays DNS and is dropped by the caller.
    pingtcp: function (host, port, n) {
      try {
        var Socket = Java.use('java.net.Socket');
        var Addr = Java.use('java.net.InetSocketAddress');
        var out = [];
        for (var i = 0; i < (n || 5); i++) {
          var s = Socket.$new();
          try {
            var t0 = Date.now();
            s.connect(Addr.$new(host, port | 0), 5000);
            out.push(Date.now() - t0);
          } catch (e) {
            out.push(null);
          }
          try { s.close(); } catch (e) {}
        }
        return { ok: true, host: host, port: port | 0, rtts: out };
      } catch (e) { return { ok: false, error: '' + e }; }
    },

    // Hold this request until `at` (device epoch ms) minus `lead`, then dispatch.
    // Blocks the caller for the whole wait, which is why the host arms the agent
    // only a couple of seconds out. Scheduling INSIDE the agent is the point: it
    // takes the host->agent RPC hop (~8 ms, and jittery) out of the critical path,
    // because the RPC has already returned into the wait by the time we fire.
    schedulesend: function (tmpl, item, at, lead) {
      try { return directSend(tmpl, item, false, { at: at, lead: lead | 0 }); }
      catch (e) { return { ok: false, error: '' + e }; }
    },

    // Hold as schedulesend does, then dispatch ALL of `items` — row 1 at `at`, row n
    // at at + (n-1)*delay — with every one of them in flight at the same time. Returns
    // as soon as the last is away, carrying the burst id; the replies are collected
    // separately, because nothing can come back while this call still holds the JS
    // thread. `at` may be omitted to burst immediately.
    burstsend: function (tmpl, items, at, lead, delay) {
      try {
        return burstSend(tmpl, items, { at: at || null, lead: lead | 0, delay: delay | 0 });
      } catch (e) { return { ok: false, error: '' + e }; }
    },

    // Collect a burst. `done` is how many rows have replied; poll until it reaches `n`
    // (or give up — a row that never answers stays pending rather than lying).
    burstresults: function (id) {
      var b = bursts[id];
      if (!b) return { ok: false, error: 'no such burst: ' + id };
      var done = 0;
      var out = b.rows.map(function (r) {
        if (r.done) done++;
        return { i: r.i, item: r.item, offset: r.offset, target: r.target,
                 sentAt: r.sentAt, skew: r.skew, done: r.done, result: r.result };
      });
      return { ok: true, id: id, n: b.rows.length, done: done, gap: b.gap,
               perHost: b.perHost, rows: out };
    },

    // Drop a collected burst and hand the app's dispatcher its own per-host cap back.
    burstclear: function (id) {
      var b = bursts[id];
      if (b) {
        b.rows.forEach(function (r) { r.call = null; });
        delete bursts[id];
      }
      var restored = null;
      var live = false;
      for (var k in bursts) { live = true; break; }
      if (!live) restored = dispatcherRestore(H);   // nothing left in flight
      return { ok: true, id: id, cleared: !!b, perHostRestored: restored };
    },

    // A throwaway send that CANNOT land in the cart: the sentinel ids resolve to no
    // offer, so the gateway rejects it ("offerId is invalid") inside a 200 — but the
    // request still travels the whole path, paying the ~1073 ms of okhttp discovery
    // and the ~59 ms TCP+TLS handshake that would otherwise be charged to the first
    // scheduled send (DOCUMENTATION.md §9). Returns the measured `preflight`, which
    // is what the host uses to size the lead time.
    warmup: function (tmpl) {
      try {
        var r = directSend(tmpl, { offerId: WARM_OFFER, usItemId: WARM_ITEM, quantity: 1 },
                           false, { quiet: true });
        r.warm = true;
        // Rejected is the expected outcome here; anything else means the sentinel
        // resolved to a real offer, and something DID go into the cart.
        r.landed = !!r.accepted;
        return r;
      } catch (e) { return { ok: false, error: '' + e }; }
    },

    // Dry run of the discovery, so the GUI can report whether sending is usable on
    // this build before anything is sent. Serves both tools — there is one send path.
    probedirect: function () {
      try {
        var h = discoverSend();
        var c = findPxClient(h);
        discoverAsync(h);      // parallel dispatch is optional: report it, don't fail on it
        return { ok: !!c, pkg: h.pkg, interceptor: h.interceptor, chainCls: h.chain,
                 async: !!h.asyncReady, asyncError: h.asyncError || null,
                 enqueue: h.enqueue || null, callback: h.callbackIface || null,
                 chainNames: h.chainNames, response: h.response,
                 respBodyField: h.respBodyField || null, respBodyCls: h.respBodyCls || null,
                 bodyRead: h.bodyRead || null, bodyIsBytes: !!h.bodyIsBytes,
                 respBodyError: h.respBodyError || null,
                 peekBody: h.peekBody || null, srcGetter: h.srcGetter || null,
                 respArmed: respArmed, respHooked: respHookCount,
                 request: h.request, builder: h.builder, requestBody: h.requestBody,
                 client: h.clientCls, newCall: h.newCall, execute: h.execute,
                 url: h.bUrl, header: h.bHeader, method: h.bMethod, build: h.bBuild,
                 error: c ? null : 'no client instance carries a PerimeterX interceptor' };
      } catch (e) { return { ok: false, error: '' + e }; }
    },
    probesend: function () { return rpc.exports.probedirect(); },   // checkout's old name

    // ---- modes -------------------------------------------------------------
    // The cart mode: what happens to add-to-carts the APP makes.
    setmode: function (m) {
      if (m === 'capture') m = 'grab';           // old name for the same mode
      if (m === 'view' || m === 'grab' || m === 'hold') mode = m;
      return mode;
    },
    // The checkout mode, PER OP: stage is 'prep' (CreatePurchaseContract) or 'commit'
    // (PlaceOrder); m is 'watch' | 'intercept' | 'idle'. The two are independent.
    setcheckoutmode: function (stage, m) {
      if (m !== 'watch' && m !== 'intercept' && m !== 'idle') return null;
      if (stage === 'prep') modePrep = m;
      else if (stage === 'commit') modeCommit = m;
      else return null;
      return m;
    },
    // Read the response to non-blocked checkout calls. On by default; the host can flip
    // it off if a build's okhttp discovery misbehaves.
    setcaptureresponses: function (v) { captureResponses = !!v; return captureResponses; },
    setdelay: function (ms) { delayMs = ms | 0; return delayMs; },

    getstate: function () {
      return { mode: mode, delayMs: delayMs,
               modePrep: modePrep, modeCommit: modeCommit,
               captureResponses: captureResponses,
               respArmed: respArmed, respHooked: respHookCount,
               prep: CHECKOUT_PREP, commit: CHECKOUT_COMMIT, add: ADD_OP };
    }
  };

  send({ type: 'ready', sink: sinkName, buffer: BufferCls,
         readBytes: readBytesName, writeBytes: writeBytesName,
         mode: mode, modePrep: modePrep, modeCommit: modeCommit,
         captureResponses: captureResponses, merged: true });
});
