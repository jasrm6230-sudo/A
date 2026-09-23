/**
 * polyglot-constants.js — v3.0 (Robust)
 * 
 * يجلب 781 ثابت Polyglot Zobrist من عدة مصادر CDN.
 * - لا يعتمد على مصدر واحد
 * - يسجّل كل خطوة في Console
 * - يخزّن في localStorage بعد النجاح الأول
 * - يعمل في الصفحة الرئيسية وفي Web Worker
 * 
 * الواجهة:
 *   window.POLYGLOT_RANDOM          Uint32Array[1562]  (بعد النجاح)
 *   window.POLYGLOT_RANDOM_PROMISE  Promise<Uint32Array>
 *   window.POLYGLOT_STATUS          { loading, error, count, source }
 */
(function (global) {
  'use strict';

  var EXPECTED = 781;
  var CACHE_KEY = 'polyglot_constants_v3';
  var TIMEOUT_MS = 10000;

  // حالة عامة
  var STATUS = {
    loading: true,
    error: null,
    count: 0,
    source: null
  };
  global.POLYGLOT_STATUS = STATUS;
  global.POLYGLOT_RANDOM = null;

  console.log('[Polyglot] ملف الثوابت بدأ التحميل');

  // ===== أدوات مساعدة =====

  function log() {
    var args = Array.prototype.slice.call(arguments);
    args.unshift('[Polyglot]');
    console.log.apply(console, args);
  }

  function warn() {
    var args = Array.prototype.slice.call(arguments);
    args.unshift('[Polyglot]');
    console.warn.apply(console, args);
  }

  // استخراج القيم الـ hex (16 خانة) من نص
  function extractHexes(text) {
    if (!text) return [];
    var seen = {};
    var out = [];
    var re = /0x([0-9A-Fa-f]{16})/g;
    var m;
    while ((m = re.exec(text)) !== null) {
      var h = m[1].toUpperCase();
      if (!seen[h]) {
        seen[h] = true;
        out.push(h);
        if (out.length === EXPECTED) break;
      }
    }
    return out;
  }

  // بناء Uint32Array مسطّح
  function buildFlat(hexes) {
    var flat = new Uint32Array(EXPECTED * 2);
    for (var i = 0; i < EXPECTED; i++) {
      var h = hexes[i];
      flat[i * 2]     = parseInt(h.substring(0, 8), 16) >>> 0;
      flat[i * 2 + 1] = parseInt(h.substring(8, 16), 16) >>> 0;
    }
    return flat;
  }

  // التحقق من صحة الثوابت عبر hash الموقف الابتدائي
  function verify(flat) {
    // الموقف: rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1
    // بترتيب Polyglot: 0=bP,1=wP,2=bN,3=wN,4=bB,5=wB,6=bR,7=wR,8=bQ,9=wQ,10=bK,11=wK
    var board = new Int8Array(64);
    // نستخدم ترتيب المحرك (a8=0) لكن نحول المربعات
    var startFen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR';
    var map = { P:1, N:2, B:3, R:4, Q:5, K:6, p:9, n:10, b:11, r:12, q:13, k:14 };
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
      var t = p & 7, col = p >> 3;
      var pieceIdx = (t - 1) * 2 + (col === 0 ? 1 : 0);
      var rank = s >> 3, file = s & 7;
      var pgsq = (7 - rank) * 8 + file;
      var idx = (pieceIdx * 64 + pgsq) * 2;
      hi ^= flat[idx];
      lo ^= flat[idx + 1];
    }
    // حقوق التبييت KQkq
    for (var k = 768; k <= 771; k++) {
      hi ^= flat[k * 2];
      lo ^= flat[k * 2 + 1];
    }
    var hiHex = ('00000000' + (hi >>> 0).toString(16)).slice(-8);
    var loHex = ('00000000' + (lo >>> 0).toString(16)).slice(-8);
    var computed = (hiHex + loHex).toLowerCase();
    return computed === '463b96181691fc9c';
  }

  // ===== localStorage =====
  function lsAvailable() {
    try {
      var k = '__pg_test_v3__';
      global.localStorage.setItem(k, '1');
      global.localStorage.removeItem(k);
      return true;
    } catch (e) {
      return false;
    }
  }
  var LS_OK = (typeof global.localStorage !== 'undefined') && lsAvailable();

  function loadFromCache() {
    if (!LS_OK) return null;
    try {
      var raw = global.localStorage.getItem(CACHE_KEY);
      if (!raw) return null;
      var arr = JSON.parse(raw);
      if (!arr || arr.length !== EXPECTED * 2) return null;
      var flat = new Uint32Array(EXPECTED * 2);
      for (var i = 0; i < arr.length; i++) flat[i] = arr[i] >>> 0;
      return flat;
    } catch (e) {
      return null;
    }
  }

  function saveToCache(flat, src) {
    if (!LS_OK) return;
    try {
      var arr = new Array(flat.length);
      for (var i = 0; i < flat.length; i++) arr[i] = flat[i];
      global.localStorage.setItem(CACHE_KEY, JSON.stringify(arr));
      log('حُفظ في localStorage');
    } catch (e) {
      warn('تعذّر الحفظ في localStorage:', e.message);
    }
  }

  // ===== جلب مع مهلة =====
  function fetchWithTimeout(url) {
    return new Promise(function (resolve, reject) {
      var done = false;
      var timer = setTimeout(function () {
        if (done) return;
        done = true;
        reject(new Error('timeout'));
      }, TIMEOUT_MS);

      fetch(url, { cache: 'force-cache', mode: 'cors', credentials: 'omit' })
        .then(function (r) {
          if (!r.ok) throw new Error('HTTP ' + r.status);
          return r.text();
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

  // ===== مصادر الثوابت =====
  var SOURCES = [
    'https://cdn.jsdelivr.net/gh/niklasf/python-chess@master/chess/polyglot.py',
    'https://raw.githubusercontent.com/niklasf/python-chess/master/chess/polyglot.py',
    'https://cdn.statically.io/gh/niklasf/python-chess/master/chess/polyglot.py',
    'https://rawcdn.githack.com/niklasf/python-chess/master/chess/polyglot.py',
    'https://raw.githack.com/niklasf/python-chess/master/chess/polyglot.py',
    'https://cdn.jsdelivr.net/gh/michaeldv/donna_opening_books@master/polyglot/random.c',
    'https://raw.githubusercontent.com/michaeldv/donna_opening_books/master/polyglot/random.c',
    'https://cdn.jsdelivr.net/gh/AndyGrant/Ethereal@master/src/polyglot.cpp',
    'https://raw.githubusercontent.com/AndyGrant/Ethereal/master/src/polyglot.cpp',
    'https://cdn.jsdelivr.net/gh/official-stockfish/Stockfish@master/src/syzygy/tbprobe.cpp'
  ];

  // ===== محاولة مصدر واحد =====
  function trySource(url) {
    return fetchWithTimeout(url).then(function (text) {
      var hexes = extractHexes(text);
      log('وجدت ' + hexes.length + ' قيمة في ' + url.split('/').slice(-2).join('/'));
      if (hexes.length < EXPECTED) {
        throw new Error('قيم غير كافية (' + hexes.length + '/' + EXPECTED + ')');
      }
      var flat = buildFlat(hexes);
      if (!verify(flat)) {
        throw new Error('فشل التحقق من hash');
      }
      return { flat: flat, source: url };
    });
  }

  // ===== المحاولة بالتسلسل =====
  function tryAll() {
    var idx = 0;
    return new Promise(function (resolve, reject) {
      function attempt() {
        if (idx >= SOURCES.length) {
          reject(new Error('فشلت جميع المصادر (' + SOURCES.length + ')'));
          return;
        }
        var url = SOURCES[idx++];
        log('محاولة ' + idx + '/' + SOURCES.length + ': ' + url);
        trySource(url).then(function (res) {
          global.POLYGLOT_RANDOM = res.flat;
          STATUS.loading = false;
          STATUS.count = EXPECTED;
          STATUS.source = res.source;
          log('✅ نجحت — ' + EXPECTED + ' ثابت');
          saveToCache(res.flat, res.source);
          resolve(res.flat);
        }).catch(function (err) {
          warn('فشلت: ' + err.message);
          attempt();
        });
      }
      attempt();
    });
  }

  // ===== البدء =====

  // 1) محاولة من localStorage
  var cached = loadFromCache();
  if (cached) {
    global.POLYGLOT_RANDOM = cached;
    STATUS.loading = false;
    STATUS.count = EXPECTED;
    STATUS.source = 'localStorage';
    log('✅ تحميل من localStorage — ' + EXPECTED + ' ثابت');
    global.POLYGLOT_RANDOM_PROMISE = Promise.resolve(cached);
  } else {
    // 2) جلب من الشبكة
    global.POLYGLOT_RANDOM_PROMISE = tryAll().catch(function (err) {
      STATUS.loading = false;
      STATUS.error = err.message;
      console.error('[Polyglot] ❌ فشل نهائي:', err.message);
      throw err;
    });
  }

  // دالة لإعادة التحميل القسري
  global.POLYGLOT_RELOAD = function () {
    if (LS_OK) {
      try { global.localStorage.removeItem(CACHE_KEY); } catch (e) {}
    }
    log('مسح الكاش — أعد تحميل الصفحة');
  };

})(typeof window !== 'undefined' ? window : self);
