/**
 * ============================================================
 *  polyglot-constants.js  v2.0
 * ============================================================
 *  يحمّل ثوابت Polyglot Zobrist (781 قيمة 64-bit) تلقائياً
 *  من CDN موثوق، ويخزّنها في localStorage لتجنب التحميل المتكرر.
 *
 *  ✅ جاهز للعمل مباشرة على GitHub Pages
 *  ✅ لا يحتاج أي سكربت توليد أو build
 *  ✅ حجم صغير جداً (~6 KB)
 *  ✅ تحميل مرة واحدة فقط ثم يُخزَّن
 *  ✅ 4 مصادر احتياطية عند الفشل
 *  ✅ يعمل في Main Thread وفي Web Worker
 *
 *  الواجهة المُصدَّرة:
 *    window.POLYGLOT_RANDOM          Uint32Array[1562]  (بعد التحميل)
 *    window.POLYGLOT_RANDOM_PROMISE  Promise<Uint32Array>
 *    window.POLYGLOT_STATUS          { loading, error, count, source, fromCache }
 *    window.POLYGLOT_RELOAD()        مسح الكاش وإعادة المحاولة
 *    window.POLYGLOT_IS_READY()      فحص الحالة بشكل متزامن
 * ============================================================
 */
(function (global) {
  'use strict';

  /* ====== الإعدادات ====== */
  var VERSION         = 'v2';
  var CACHE_KEY       = 'polyglot_constants_' + VERSION;
  var CACHE_TTL_MS    = 90 * 24 * 60 * 60 * 1000;  // 90 يوماً
  var EXPECTED_COUNT  = 781;
  var TIMEOUT_MS      = 15000;
  var VERIFY_HASH     = '463b96181691fc9c';        // hash الموقف الابتدائي

  /* ====== مصادر احتياطية (الأسرع أولاً) ====== */
  var SOURCES = [
    'https://cdn.jsdelivr.net/gh/niklasf/python-chess@master/chess/polyglot.py',
    'https://cdn.jsdelivr.net/gh/michaeldv/donna_opening_books@master/polyglot/random.c',
    'https://raw.githack.com/niklasf/python-chess/master/chess/polyglot.py',
    'https://cdn.statically.io/gh/niklasf/python-chess/master/chess/polyglot.py'
  ];

  /* ====== حالة عامة ====== */
  var STATUS = {
    loading: true,
    error: null,
    count: 0,
    source: null,
    fromCache: false
  };
  global.POLYGLOT_STATUS = STATUS;
  global.POLYGLOT_RANDOM = null;

  /* ====== أدوات مساعدة ====== */
  function logInfo() {
    if (typeof console !== 'undefined' && console.log) {
      var a = Array.prototype.slice.call(arguments);
      a.unshift('[Polyglot]');
      console.log.apply(console, a);
    }
  }
  function logWarn() {
    if (typeof console !== 'undefined' && console.warn) {
      var a = Array.prototype.slice.call(arguments);
      a.unshift('[Polyglot]');
      console.warn.apply(console, a);
    }
  }
  function logError() {
    if (typeof console !== 'undefined' && console.error) {
      var a = Array.prototype.slice.call(arguments);
      a.unshift('[Polyglot]');
      console.error.apply(console, a);
    }
  }

  /* ====== استخراج القيم الـ hex من نصّ المصدر ====== */
  function extractHexes(text) {
    if (!text) return [];
    var seen = Object.create(null);
    var out = [];
    var re = /0x[0-9A-Fa-f]{16}/g;
    var m;
    while ((m = re.exec(text)) !== null) {
      var h = m[0].toUpperCase();
      if (!seen[h]) {
        seen[h] = true;
        out.push(h);
        if (out.length >= EXPECTED_COUNT) break;
      }
    }
    return out;
  }

  /* ====== بناء Uint32Array مسطّح من قائمة hex ====== */
  function buildFlat(hexes) {
    if (hexes.length < EXPECTED_COUNT) return null;
    var flat = new Uint32Array(EXPECTED_COUNT * 2);
    for (var i = 0; i < EXPECTED_COUNT; i++) {
      var v = hexes[i].slice(2);  // حذف "0x"
      flat[i * 2]     = parseInt(v.slice(0, 8), 16) >>> 0;
      flat[i * 2 + 1] = parseInt(v.slice(8, 16), 16) >>> 0;
    }
    return flat;
  }

  /* ====== التحقق من صحة الثوابت ======
   * نحسب hash الموقف الابتدائي ونتأكد أنه يساوي القيمة المعروفة.
   * هذا يضمن أن الثوابت صحيحة 100% قبل استخدامها.
   */
  function verifyConstants(flat) {
    if (!flat || flat.length < EXPECTED_COUNT * 2) return false;

    var startFen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR';
    var map = { P:1, N:2, B:3, R:4, Q:5, K:6, p:9, n:10, b:11, r:12, q:13, k:14 };
    var board = new Int8Array(64);
    var sq = 0;

    for (var i = 0; i < startFen.length; i++) {
      var c = startFen[i];
      if (c === '/') continue;
      if (c >= '1' && c <= '8') { sq += c.charCodeAt(0) - 48; continue; }
      board[sq++] = map[c] || 0;
    }

    var hi = 0, lo = 0;
    for (var s = 0; s < 64; s++) {
      var p = board[s];
      if (!p) continue;
      var type = p & 7, color = p >> 3;
      var pieceIdx = (type - 1) * 2 + (color === 0 ? 1 : 0);
      var rank = s >> 3, file = s & 7;
      var pgSq = (7 - rank) * 8 + file;
      var idx = (pieceIdx * 64 + pgSq) * 2;
      hi ^= flat[idx];
      lo ^= flat[idx + 1];
    }
    // حقوق التبييت KQkq = 768, 769, 770, 771
    for (var k = 768; k <= 771; k++) {
      hi ^= flat[k * 2];
      lo ^= flat[k * 2 + 1];
    }

    var hiHex = ('00000000' + (hi >>> 0).toString(16)).slice(-8);
    var loHex = ('00000000' + (lo >>> 0).toString(16)).slice(-8);
    var computed = (hiHex + loHex).toLowerCase();

    if (computed === VERIFY_HASH) {
      logInfo('✓ تحقق ناجح — hash الموقف الابتدائي مطابق');
      return true;
    }
    logWarn('✗ فشل التحقق — computed=' + computed + ' expected=' + VERIFY_HASH);
    return false;
  }

  /* ====== localStorage ====== */
  function lsAvailable() {
    try {
      var k = '__pg_test__' + Date.now();
      global.localStorage.setItem(k, '1');
      global.localStorage.removeItem(k);
      return true;
    } catch (e) { return false; }
  }
  var LS_OK = (typeof global.localStorage !== 'undefined') && lsAvailable();

  function loadFromCache() {
    if (!LS_OK) return null;
    try {
      var raw = global.localStorage.getItem(CACHE_KEY);
      if (!raw) return null;
      var obj = JSON.parse(raw);
      if (!obj || !obj.ts || !obj.data) return null;
      if (Date.now() - obj.ts > CACHE_TTL_MS) {
        global.localStorage.removeItem(CACHE_KEY);
        return null;
      }
      var arr = obj.data;
      var flat = new Uint32Array(arr.length);
      for (var i = 0; i < arr.length; i++) flat[i] = arr[i] >>> 0;
      return flat;
    } catch (e) {
      return null;
    }
  }

  function saveToCache(flat, source) {
    if (!LS_OK) return;
    try {
      var arr = new Array(flat.length);
      for (var i = 0; i < flat.length; i++) arr[i] = flat[i];
      global.localStorage.setItem(CACHE_KEY, JSON.stringify({
        ts: Date.now(),
        source: source || '',
        data: arr
      }));
    } catch (e) {
      logWarn('تعذّر التخزين المؤقت:', e.message);
    }
  }

  function clearCache() {
    if (!LS_OK) return;
    try { global.localStorage.removeItem(CACHE_KEY); } catch (e) {}
  }

  /* ====== الجلب من الشبكة ====== */
  function fetchText(url, timeoutMs) {
    return new Promise(function (resolve, reject) {
      var done = false;
      var timer = setTimeout(function () {
        if (done) return;
        done = true;
        reject(new Error('انتهت المهلة (' + timeoutMs + 'ms)'));
      }, timeoutMs);

      fetch(url, { cache: 'force-cache', mode: 'cors', credentials: 'omit' })
        .then(function (resp) {
          if (!resp.ok) throw new Error('HTTP ' + resp.status);
          return resp.text();
        })
        .then(function (text) {
          if (done) return;
          done = true;
          clearTimeout(timer);
          resolve(text);
        })
        .catch(function (err) {
          if (done) return;
          done = true;
          clearTimeout(timer);
          reject(err);
        });
    });
  }

  function tryOneSource(url) {
    return fetchText(url, TIMEOUT_MS).then(function (text) {
      var hexes = extractHexes(text);
      if (hexes.length < EXPECTED_COUNT) {
        throw new Error('عدد غير كافٍ: ' + hexes.length + ' < ' + EXPECTED_COUNT);
      }
      var flat = buildFlat(hexes);
      if (!flat) throw new Error('فشل بناء المصفوفة');
      if (!verifyConstants(flat)) throw new Error('فشل التحقق من الصحة');
      return { flat: flat, source: url };
    });
  }

  /* ====== التسلسل الرئيسي ====== */
  var cached = loadFromCache();

  if (cached) {
    global.POLYGLOT_RANDOM = cached;
    STATUS.loading = false;
    STATUS.count = cached.length / 2;
    STATUS.source = 'localStorage';
    STATUS.fromCache = true;
    logInfo('تم التحميل من الكاش — ' + STATUS.count + ' ثابت');
    global.POLYGLOT_RANDOM_PROMISE = Promise.resolve(cached);
  } else {
    global.POLYGLOT_RANDOM_PROMISE = (function () {
      var idx = 0;

      function attempt() {
        if (idx >= SOURCES.length) {
          throw new Error('فشلت جميع المصادر (' + SOURCES.length + ')');
        }
        var url = SOURCES[idx++];
        logInfo('المحاولة ' + idx + '/' + SOURCES.length + ':', url);

        return tryOneSource(url).then(function (res) {
          global.POLYGLOT_RANDOM = res.flat;
          STATUS.loading = false;
          STATUS.count = res.flat.length / 2;
          STATUS.source = res.source;
          STATUS.error = null;
          STATUS.fromCache = false;
          saveToCache(res.flat, res.source);
          logInfo('✅ نجح — ' + STATUS.count + ' ثابت من ' + res.source);
          return res.flat;
        }).catch(function (err) {
          logWarn('✗ فشل (' + url + '): ' + err.message);
          return attempt();
        });
      }

      return attempt().catch(function (err) {
        STATUS.loading = false;
        STATUS.error = err.message;
        logError('❌ فشل نهائي:', err.message);
        throw err;
      });
    })();
  }

  /* ====== واجهات إضافية ====== */
  global.POLYGLOT_RELOAD = function () {
    clearCache();
    logInfo('تم مسح الكاش — أعد تحميل الصفحة');
  };

  global.POLYGLOT_IS_READY = function () {
    return !!(global.POLYGLOT_RANDOM && global.POLYGLOT_RANDOM.length >= EXPECTED_COUNT * 2);
  };

  /* ====== رسالة أخيرة عند الجاهزية ====== */
  global.POLYGLOT_RANDOM_PROMISE.then(function (flat) {
    if (flat && flat.length === EXPECTED_COUNT * 2) {
      logInfo('الثوابت جاهزة للاستخدام —', flat.length / 2, 'قيمة');
    }
  }).catch(function () { /* تم التعامل معه مسبقاً */ });

})(typeof window !== 'undefined' ? window : self);
