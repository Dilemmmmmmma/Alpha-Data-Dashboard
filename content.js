(function () {
  'use strict';
  const STABLE_FALLBACK_POLL_MS = 1000;
  const DEFAULT_WINDOW_SEC = 20;
  const DEFAULT_TOLERANCE_PCT = 0.05;
  let stableWindowSec = DEFAULT_WINDOW_SEC;
  let stableTolerancePct = DEFAULT_TOLERANCE_PCT;
  let sampleBuffer = [];
  let currentMultiplier = 1;
  const tokenRecords = new Map();
  let tokenMapCache = null;
  let tokenMapCacheTime = 0;
  const TOKEN_MAP_CACHE_MS = 5 * 60 * 1000;
  let recentStableCache = null;
  let recentStableCacheTime = 0;
  const RECENT_STABLE_CACHE_MS = 1 * 15 * 1000;
  const DOM = {
    volatility: null,
    stability: null,
    multiplier4x: null,
    totalVolume: null,
    volumeIntegral: null,
    wear: null,
    recentStable: null,
    init() {
      this.volatility = document.querySelector('[data-alpha-volatility-status]');
      this.stability = document.querySelector('[data-alpha-stability-flag]');
      this.multiplier4x = document.querySelector('[data-alpha-multiplier4x]');
      this.totalVolume = document.querySelector('[data-alpha-total-volume]');
      this.volumeIntegral = document.querySelector('[data-alpha-volume-integral]');
      this.wear = document.querySelector('[data-alpha-wear]');
      this.recentStable = document.querySelector('[data-alpha-recent-stable]');
    }
  };
  const observedAmount = { value: NaN, ts: 0 };
  let lastCommit = { key: '', ts: 0 };
  let lastFillTriggerAt = 0;
  const STORAGE_KEYS = {
    totalRecords: 'alpha_total_records',
    wearValue: 'alpha_wear_value',
    baselineBalance: 'alpha_baseline_balance',
    lastTradeBalance: 'alpha_last_trade_balance',
    stableTolerance: 'alpha_stable_tolerance_pct'
  };

  function detectLanguage() {
    const hostname = window.location.hostname;
    const pathname = window.location.pathname;
    
    if (hostname.includes('binance.com')) {
      if (pathname.includes('/zh-CN/') || pathname.includes('/zh/')) {
        return 'zh';
      } else if (pathname.includes('/en/') || pathname.includes('/en-US/')) {
        return 'en';
      }
    }
    
    const htmlLang = document.documentElement.lang || '';
    if (htmlLang.startsWith('zh')) return 'zh';
    if (htmlLang.startsWith('en')) return 'en';
    
    return 'zh';
  }

  const currentLang = detectLanguage();
  
  const i18n = {
    zh: {
      multiplier4x: '4倍时间',
      stability: '稳定度',
      volatility: '波动率',
      totalVolume: '交易量',
      volumeIntegral: '交易量积分',
      wear: '磨损 / 磨损率',
      recentStable: '最近稳定',
      stable: '稳定',
      volatile: '波动',
      none: '暂无',
      clearConfirm: '是否清空 交易量 / 交易量积分 / 磨损 / 磨损率？',
      invalidValue: '无效的数值',
      threshold: '阈值 : ',
      save: '保存',
      cancel: '取消'
    },
    en: {
      multiplier4x: '4x Time',
      stability: 'Stability',
      volatility: 'Volatility',
      totalVolume: 'Volume',
      volumeIntegral: 'Volume Points',
      wear: 'Wear / Wear Rate',
      recentStable: 'Recent Stable',
      stable: 'Stable',
      volatile: 'Volatile',
      none: 'None',
      clearConfirm: 'Clear all data: Volume / Volume Points / Wear / Wear Rate?',
      invalidValue: 'Invalid value',
      threshold: 'Threshold: ',
      save: 'Save',
      cancel: 'Cancel'
    }
  };

  function t(key) {
    return i18n[currentLang]?.[key] || i18n.zh[key] || key;
  }
  const Storage = {
    get(key, defaultValue = null) {
      try {
        const value = localStorage.getItem(key);
        return value ? JSON.parse(value) : defaultValue;
      } catch (_) { return defaultValue; }
    },  
    set(key, value) {
      try { localStorage.setItem(key, JSON.stringify(value)); } catch (_) {}
    },
    remove(key) {
      try { localStorage.removeItem(key); } catch (_) {}
    }
  };
  (function initToleranceFromStorage(){
    const v = Number(Storage.get(STORAGE_KEYS.stableTolerance, DEFAULT_TOLERANCE_PCT));
    if (Number.isFinite(v) && v >= 0) stableTolerancePct = v; else stableTolerancePct = DEFAULT_TOLERANCE_PCT;
  })();
  let wearValue = 0;
  let baselineBalance = NaN;
  let lastTradeBalance = NaN;
  let lastObservedBalance = NaN;
  let stableStartTime = null;
  let stableTimer = null;
  let currentAlphaId = null;
  const Timers = {
    timers: new Map(),
    timeouts: new Map(),
    set(key, fn, delay) {
      this.clear(key);
      this.timers.set(key, setInterval(fn, delay));
    },
    setTimeout(key, fn, delay) {
      this.clearTimeout(key);
      this.timeouts.set(key, setTimeout(() => {
        this.timeouts.delete(key);
        fn();
      }, delay));
    },
    clear(key) {
      const timer = this.timers.get(key);
      if (timer) {
        clearInterval(timer);
        this.timers.delete(key);
      }
    },
    clearTimeout(key) {
      const timer = this.timeouts.get(key);
      if (timer) {
        clearTimeout(timer);
        this.timeouts.delete(key);
      }
    },
    clearAll() {
      this.timers.forEach(timer => clearInterval(timer));
      this.timeouts.forEach(timer => clearTimeout(timer));
      this.timers.clear();
      this.timeouts.clear();
    }
  };
  function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
  function computeVWAP(samples) {
    let sumPV = 0, sumV = 0;
    for (const s of samples) { if (!isNaN(s.v) && s.v > 0) { sumPV += s.p * s.v; sumV += s.v; } }
    return sumV > 0 ? (sumPV / sumV) : NaN;
  }
  function computeWeightedQuantile(samples, q) {
    const arr = samples.filter(s => !isNaN(s.v) && s.v > 0).slice().sort((a, b) => a.p - b.p);
    let totalV = 0; for (const s of arr) totalV += s.v;
    if (totalV <= 0) return NaN;
    const target = totalV * q;
    let cum = 0;
    for (const s of arr) { cum += s.v; if (cum >= target) return s.p; }
    return arr.length ? arr[arr.length - 1].p : NaN;
  }
  async function fetchJSON(url) {
    try {
      const res = await fetch(url, { cache: 'no-store' });
      return await res.json();
    } catch {
      return null;
    }
  }
  function getAlphaPageContract() {
    try {
      const m = location.pathname.match(/\/alpha\/[^/]+\/([^/?#]+)/i);
      if (m && m[1]) return m[1].toLowerCase();
    } catch (_) {}
    return '';
  }
  async function fetchAlphaTokenMap() {
    const url = 'https://www.binance.com/bapi/defi/v1/public/wallet-direct/buw/wallet/cex/alpha/all/token/list';
    const json = await fetchJSON(url);
    if (!json?.data) return null;
    const bySymbol = new Map();
    const byAddress = new Map();
    for (const it of json.data) {
      if (!it?.alphaId) continue;
      const rec = {
        alphaId: it.alphaId,
        symbol: (it.symbol || '').toUpperCase(),
        contract: (it.contractAddress || '').toLowerCase(),
        iconUrl: it.iconUrl || '',
        listingTime: Number(it.listingTime) || 0
      };
      if (rec.symbol) bySymbol.set(rec.symbol, rec);
      if (rec.contract) byAddress.set(rec.contract, rec);
    }
    return { bySymbol, byAddress };
  }
  async function getCachedTokenMap() {
    const now = Date.now();
    if (tokenMapCache && (now - tokenMapCacheTime) < TOKEN_MAP_CACHE_MS) {
      return tokenMapCache;
    }
    tokenMapCache = await fetchAlphaTokenMap();
    tokenMapCacheTime = now;
    return tokenMapCache;
  }
  async function getCurrentAlphaId() {
    try {
      const cache = await getCachedTokenMap();
      if (!cache) return null;
      const addr = getAlphaPageContract();
      if (addr && cache.byAddress && cache.byAddress.has(addr)) return cache.byAddress.get(addr).alphaId;
      return null;
    } catch (_) { return null; }
  }
  async function getCurrentSymbolUpper() {
    try {
      const cache = await getCachedTokenMap();
      if (!cache) return '';
      const addr = getAlphaPageContract();
      if (addr && cache.byAddress && cache.byAddress.has(addr)) {
        const rec = cache.byAddress.get(addr);
        return (rec.symbol || '').toString().toUpperCase();
      }
      return '';
    } catch (_) { return ''; }
  }
  async function fetchMultiplier(alphaId) {
    const url = `https://www.binance.com/bapi/defi/v1/public/alpha-trade/aggTicker24?dataType=limit&symbols=${alphaId}USDT`;
    const json = await fetchJSON(url);
    const data = json?.data;
    if (!data) return 0;
    const arr = Array.isArray(data) ? data : [data];
    const it = arr.find(x => x?.alphaId === alphaId || x?.symbol === `${alphaId}USDT`);
    return Number(it?.mulPoint) || 0;
  }
  async function fetchLatestTrades(alphaId, limit = 20) {
    const url = `https://www.binance.com/bapi/defi/v1/public/alpha-trade/agg-trades?symbol=${alphaId}USDT&limit=${limit}`;
    const json = await fetchJSON(url);
    const trades = json?.data || [];
    return trades
      .map(t => ({
        price: +t.p,
        volume: +t.q,
        timestamp: t.T
      }))
      .filter(t => t.price > 0 && t.volume > 0);
  }
  async   function processLatestTradeAPI(now) {
    const alphaId = await getCurrentAlphaId();
    if (!alphaId) return { isStable: false, rangePct: NaN, signPct: NaN };
    const trades = await fetchLatestTrades(alphaId, 20);
    if (trades.length === 0) return { isStable: false, rangePct: NaN, signPct: NaN };
    for (const tr of trades) sampleBuffer.push({ t: tr.timestamp, p: tr.price, v: tr.volume });
    
    const cutoff = now - stableWindowSec * 1000;
    sampleBuffer = sampleBuffer.filter(s => s && Number.isFinite(s.t) && s.t >= cutoff);
    const windowed = sampleBuffer;
    const first = windowed[0];
    const last = windowed[windowed.length - 1];
    if (!first || !last || !Number.isFinite(first.t) || !Number.isFinite(last.t)) return { isStable: false, rangePct: NaN, signPct: NaN };
    const coverageMs = last.t - first.t;

    const vwap = computeVWAP(windowed);
    const p05 = computeWeightedQuantile(windowed, 0.05);
    const p95 = computeWeightedQuantile(windowed, 0.95);
    if ([vwap, p05, p95].some(v => isNaN(v) || v === 0)) return { isStable: false, rangePct: NaN, signPct: NaN };
    const rangePct = Math.abs((p95 - p05) / vwap) * 100;
    const p50 = computeWeightedQuantile(windowed, 0.5);
    const signPct = isNaN(p50) ? NaN : ((p50 - vwap) / vwap) * 100;
    const isStable = rangePct <= stableTolerancePct;
    return { isStable, rangePct, signPct };
  }
  function ensureMetricsBar() {
    const nodes = document.querySelectorAll('div.bn-flex.items-center.gap-\\[16px\\]');
    return nodes.length ? nodes[0] : null;
  }
  function createMetricBlock(title, dataAttr, blockAttr) {
    const wrapper = document.createElement('div');
    wrapper.className = 'bn-flex flex-col gap-[2px] ';
    wrapper.setAttribute(blockAttr, '');
    const titleWrap = document.createElement('div');
    titleWrap.className = '';
    const titleInner = document.createElement('div');
    titleInner.className = '';
    titleInner.style.cursor = 'default';
    const titleBorder = document.createElement('div');
    titleBorder.className = 'border-0';
    const titleEl = document.createElement('div');
    titleEl.className = 'text-[12px] font-[400] leading-[18px] h-[18px] text-TertiaryText';
    titleEl.textContent = title;
    
    const eventListeners = [];
    if (dataAttr === 'data-alpha-total-volume') {
      titleEl.style.textDecoration = 'underline';
      titleEl.style.cursor = 'pointer';
      const clearDataHandler = () => {
        try {
          const ok = confirm(t('clearConfirm'));
          if (!ok) return;
          try { tokenRecords.clear(); } catch (_) {}
          saveTotalsToStorage();
          Storage.remove(STORAGE_KEYS.baselineBalance);
          Storage.remove(STORAGE_KEYS.lastTradeBalance);
          Storage.remove(STORAGE_KEYS.wearValue);
          const bal = readDomBalance();
          baselineBalance = Number.isFinite(bal) ? bal : NaN;
          lastTradeBalance = Number.isFinite(bal) ? bal : NaN;
          wearValue = 0;
          persistBaselineAndWear();
          updateTotalVolumeUI();
        } catch (_) {}
      };
      titleEl.addEventListener('click', clearDataHandler);
      eventListeners.push({ element: titleEl, event: 'click', handler: clearDataHandler });
    }
    if (dataAttr === 'data-alpha-volatility-status') {
      titleEl.style.textDecoration = 'underline';
      titleEl.style.cursor = 'pointer';
      const editor = document.createElement('div');
      editor.className = 'bn-flex items-center gap-[8px] mt-[2px] alpha-tol-editor';
      editor.style.display = 'none';
      const label = document.createElement('div');
      label.className = 'text-[12px] leading-[18px] text-TertiaryText';
      label.textContent = t('threshold');
      const inputEl = document.createElement('input');
      inputEl.type = 'text';
      inputEl.value = String(Number.isFinite(stableTolerancePct) ? stableTolerancePct : DEFAULT_TOLERANCE_PCT);
      inputEl.className = 'bn-textField-input w-[40px]';
      const saveBtn = document.createElement('button');
      saveBtn.className = 'bn-button bn-button__buy data-size-small';
      saveBtn.style.transform = 'scale(0.6)';
      saveBtn.style.transformOrigin = 'left center';
      saveBtn.textContent = t('save');
      const cancelBtn = document.createElement('button');
      cancelBtn.className = 'bn-button bn-button__sell data-size-small';
      cancelBtn.style.transform = 'scale(0.6)';
      cancelBtn.style.transformOrigin = 'left center';
      cancelBtn.textContent = t('cancel');
      editor.appendChild(label);
      editor.appendChild(inputEl);
      editor.appendChild(saveBtn);
      editor.appendChild(cancelBtn);
      titleBorder.appendChild(editor);
      function hideAllEditors() {
        document.querySelectorAll('.alpha-tol-editor').forEach(e => { e instanceof HTMLElement && (e.style.display = 'none'); });
      }
      const toggleEditorHandler = () => {
        const isHidden = editor.style.display === 'none';
        hideAllEditors();
        editor.style.display = isHidden ? 'flex' : 'none';
        if (isHidden) inputEl.focus();
      };
      const cancelHandler = () => { editor.style.display = 'none'; };
      const saveHandler = () => {
        const v = Number(inputEl.value);
        if (!Number.isFinite(v) || v < 0) { alert(t('invalidValue')); return; }
        stableTolerancePct = v;
        Storage.set(STORAGE_KEYS.stableTolerance, v);
        editor.style.display = 'none';
      };
      
      titleEl.addEventListener('click', toggleEditorHandler);
      cancelBtn.addEventListener('click', cancelHandler);
      saveBtn.addEventListener('click', saveHandler);
      
      eventListeners.push(
        { element: titleEl, event: 'click', handler: toggleEditorHandler },
        { element: cancelBtn, event: 'click', handler: cancelHandler },
        { element: saveBtn, event: 'click', handler: saveHandler }
      );
    }
    const valueRow = document.createElement('div');
    valueRow.className = 'bn-flex text-[12px] font-[400] leading-[16px] h-[16px] text-PrimaryText gap-[4px] items-center';
    const valueSpan = document.createElement('span');
    valueSpan.setAttribute(dataAttr, '');
    valueSpan.textContent = '';
    titleBorder.appendChild(titleEl);
    titleInner.appendChild(titleBorder);
    titleWrap.appendChild(titleInner);
    valueRow.appendChild(valueSpan);
    wrapper.appendChild(titleWrap);
    wrapper.appendChild(valueRow);
    
    wrapper.cleanupEventListeners = () => {
      eventListeners.forEach(({ element, event, handler }) => {
        element.removeEventListener(event, handler);
      });
    };
    
    return wrapper;
  }
  const METRIC_CONFIGS = [
    { title: t('multiplier4x'), dataAttr: 'data-alpha-multiplier4x', blockAttr: 'data-alpha-multiplier4x-block', hasCheck: 'hasMx4' },
    { title: t('stability'), dataAttr: 'data-alpha-stability-flag', blockAttr: 'data-alpha-stability-block', hasCheck: 'hasStable' },
    { title: t('volatility'), dataAttr: 'data-alpha-volatility-status', blockAttr: 'data-alpha-volatility-block', hasCheck: 'hasVol' },
    { title: t('totalVolume'), dataAttr: 'data-alpha-total-volume', blockAttr: 'data-alpha-total-block', hasCheck: 'hasVolume' },
    { title: t('volumeIntegral'), dataAttr: 'data-alpha-volume-integral', blockAttr: 'data-alpha-integral-block', hasCheck: 'hasIntegral' },
    { title: t('wear'), dataAttr: 'data-alpha-wear', blockAttr: 'data-alpha-wear-block', hasCheck: 'hasWear' },
    { title: t('recentStable'), dataAttr: 'data-alpha-recent-stable', blockAttr: 'data-alpha-recent-stable-block', hasCheck: 'hasRecentStable' }
  ];
  function insertMetricsIfMissing() {
    const bar = ensureMetricsBar();
    if (!bar) return null;
    const checks = {
      hasVol: !!bar.querySelector('[data-alpha-volatility-status]'),
      hasStable: !!bar.querySelector('[data-alpha-stability-flag]'),
      hasMx4: !!bar.querySelector('[data-alpha-multiplier4x]'),
      hasVolume: !!bar.querySelector('[data-alpha-total-volume]'),
      hasIntegral: !!bar.querySelector('[data-alpha-volume-integral]'),
      hasWear: !!bar.querySelector('[data-alpha-wear]')
    };
    METRIC_CONFIGS.forEach(config => {
      if (!checks[config.hasCheck]) {
        const wrapper = createMetricBlock(config.title, config.dataAttr, config.blockAttr);
        bar.appendChild(wrapper);
      }
    });
    const volBlock = bar.querySelector('[data-alpha-volatility-block]') || bar.querySelector('[data-alpha-volatility-status]')?.closest('div.bn-flex.flex-col.gap-\\[2px\\]');
    const stableBlock = bar.querySelector('[data-alpha-stability-block]') || bar.querySelector('[data-alpha-stability-flag]')?.closest('div.bn-flex.flex-col.gap-\\[2px\\]');
    const mxBlock = bar.querySelector('[data-alpha-multiplier4x-block]') || bar.querySelector('[data-alpha-multiplier4x]')?.closest('div.bn-flex.flex-col.gap-\\[2px\\]');
    const totalBlock = bar.querySelector('[data-alpha-total-block]') || bar.querySelector('[data-alpha-total-volume]')?.closest('div.bn-flex.flex-col.gap-\\[2px\\]');
    const integBlock = bar.querySelector('[data-alpha-integral-block]') || bar.querySelector('[data-alpha-volume-integral]')?.closest('div.bn-flex.flex-col.gap-\\[2px\\]');
    const wearBlock = bar.querySelector('[data-alpha-wear-block]') || bar.querySelector('[data-alpha-wear]')?.closest('div.bn-flex.flex-col.gap-\\[2px\\]');
    if (volBlock && stableBlock && stableBlock.nextSibling !== volBlock) {
      try { bar.insertBefore(stableBlock, volBlock); } catch (_) {}
    }
    if (stableBlock && mxBlock && mxBlock.nextSibling !== stableBlock) {
      try { bar.insertBefore(mxBlock, stableBlock); } catch (_) {}
    }
    if (volBlock && totalBlock && volBlock.nextSibling !== totalBlock) {
      try { bar.insertBefore(totalBlock, volBlock.nextSibling); } catch (_) {}
    }
    if (totalBlock && integBlock && totalBlock.nextSibling !== integBlock) {
      try { bar.insertBefore(integBlock, totalBlock.nextSibling); } catch (_) {}
    }
    if (integBlock && wearBlock && integBlock.nextSibling !== wearBlock) {
      try { bar.insertBefore(wearBlock, integBlock.nextSibling); } catch (_) {}
    }
    return bar.querySelector('[data-alpha-volatility-status]');
  }
  function updateStatus({ isStable, rangePct, signPct }) {
    if (DOM.stability) {
      if (isStable) {
        if (!stableStartTime) {
          stableStartTime = Date.now();
        }
        const elapsed = Math.floor((Date.now() - stableStartTime) / 1000);
        const hours = Math.floor(elapsed / 3600);
        const minutes = Math.floor((elapsed % 3600) / 60);
        const seconds = elapsed % 60;
        let timeStr;
        if (hours > 0) {
          timeStr = `${hours}:${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
        } else {
          timeStr = `${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
        }
        DOM.stability.textContent = ` ${t('stable')} ${timeStr}`;
        DOM.stability.style.color = '#00ff88';
      } else {
        stableStartTime = null;
        DOM.stability.textContent = ` ${t('volatile')}`;
        DOM.stability.style.color = '#ffcc00';
      }
    }
    if (!DOM.volatility) return;
    if (!Number.isFinite(rangePct)) { DOM.volatility.textContent = ''; return; }
    const dir = Number.isFinite(signPct) ? (signPct > 0 ? '↑' : (signPct < 0 ? '↓' : '')) : '';
    DOM.volatility.textContent = ` ${rangePct.toFixed(4)}% ${dir}`;
    if (dir === '↑') DOM.volatility.style.color = '#00ff88';
    else if (dir === '↓') DOM.volatility.style.color = '#ff6666';
    else DOM.volatility.style.color = isStable ? '#00ff88' : '#ffcc00';
  }
  async function startStableLoop() {
    Timers.set('stable', async () => {
      const newAlphaId = await getCurrentAlphaId();
      if (newAlphaId !== currentAlphaId) {
        currentAlphaId = newAlphaId;
        stableStartTime = null;
        sampleBuffer = [];
        if (DOM.stability) {
          DOM.stability.textContent = ` ${t('volatile')}`;
          DOM.stability.style.color = '#ffcc00';
        }
        if (DOM.volatility) {
          DOM.volatility.textContent = '';
        }
      }
      const r = await processLatestTradeAPI(Date.now());
      updateStatus(r);
    }, STABLE_FALLBACK_POLL_MS);
    
    Timers.set('stableTimer', () => {
      if (stableStartTime && DOM.stability) {
        const elapsed = Math.floor((Date.now() - stableStartTime) / 1000);
        const hours = Math.floor(elapsed / 3600);
        const minutes = Math.floor((elapsed % 3600) / 60);
        const seconds = elapsed % 60;
        let timeStr;
        if (hours > 0) {
          timeStr = `${hours}:${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
        } else {
          timeStr = `${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
        }
        if (DOM.stability.textContent.includes(t('stable'))) {
          DOM.stability.textContent = ` ${t('stable')} ${timeStr}`;
        }
      }
    }, 1000);
  }
  async function startMultiplierCountdown() {
    if (!DOM.multiplier4x) return;
    Timers.set('multiplier', async () => {
      try {
        const cache = await getCachedTokenMap();
        const alphaId = await getCurrentAlphaId();
        if (!cache || !alphaId) { DOM.multiplier4x.textContent = ' —'; DOM.multiplier4x.style.color = '#CCCCCC'; return; }
        let rec = null;
        const addr = getAlphaPageContract();
        if (addr && cache.byAddress && cache.byAddress.has(addr)) rec = cache.byAddress.get(addr);
        const listingTime = rec && rec.listingTime ? Number(rec.listingTime) : 0;
        const mulPoint = await fetchMultiplier(alphaId);
        currentMultiplier = mulPoint > 1 ? mulPoint : 1;
        if (!listingTime || mulPoint < 4) { DOM.multiplier4x.textContent = ' —'; DOM.multiplier4x.style.color = '#CCCCCC'; return; }
        const msPerDay = 24 * 60 * 60 * 1000;
        const nowMs = Date.now();
        const remainingMs = Math.max(0, (30 * msPerDay) - (nowMs - listingTime));
        const totalHours = Math.floor(remainingMs / (60 * 60 * 1000));
        const remainingMinutes = Math.floor((remainingMs % (60 * 60 * 1000)) / (60 * 1000));
        const remainingSeconds = Math.floor((remainingMs % (60 * 1000)) / 1000);
        const txt = `${String(totalHours).padStart(2,'0')}:${String(remainingMinutes).padStart(2,'0')}:${String(remainingSeconds).padStart(2,'0')}`;
        DOM.multiplier4x.textContent = ` ${txt}`;
        const remainingDays = remainingMs / msPerDay;
        if (remainingDays > 15) DOM.multiplier4x.style.color = '#00ff88';
        else if (remainingDays >= 7) DOM.multiplier4x.style.color = '#ffcc00';
        else DOM.multiplier4x.style.color = '#ff6666';
      } catch (_) { DOM.multiplier4x.textContent = ' —'; DOM.multiplier4x.style.color = '#CCCCCC'; }
    }, 1000);
  }
  function readDomValue(selector, index = 0) {
    try {
      const app = document.getElementById('__APP');
      if (!app) return NaN;
      const elements = app.querySelectorAll(selector);
      if (!elements.length) return NaN;
      const el = elements[index] || elements[0];
      const match = (el.textContent || '').match(/(-?\d+(?:\.\d+)?)/);
      if (match) {
        const value = parseFloat(match[1]);
        if (Number.isFinite(value)) return value;
      }
    } catch (_) {}
    return NaN;
  }
  function readDomBalance() {
    return readDomValue('.text-PrimaryText.text-\\[12px\\].leading-\\[18px\\].font-\\[500\\]');
  }
  function getAmountText() {
    const value = readDomValue('.value', 2);
    return Number.isFinite(value) ? value.toString() : '';
  }
  function startAmountWatcher() {
    Timers.set('amount', () => {
      const t = getAmountText();
      const v = parseFloat((t || '').replace(/[^\d.]/g, ''));
      if (Number.isFinite(v) && v > 0) {
        observedAmount.value = v;
        observedAmount.ts = Date.now();
        recordPendingTrade(v);
      }
    }, 200);
  }
  let pendingTradeAmount = 0;
  let pendingTradeTimestamp = 0;
  let lastBalanceBeforeTrade = NaN;
  const TRADE_DETECTION_WINDOW_MS = 10000;
  const MIN_BALANCE_CHANGE_THRESHOLD = 0.0000001;

  let tradeQueue = [];
  const MAX_QUEUE_SIZE = 10;

  let tradePairs = new Map();
  let tradeIdCounter = 0;

  let refundAmount = 0;
  const REFUND_THRESHOLD = 3; 

  function startBalanceWatcher() {
    Timers.set('balance', () => {
      const bal = readDomBalance();
      if (Number.isFinite(bal)) {
        lastObservedBalance = bal;
        if (!Number.isFinite(baselineBalance)) {
          baselineBalance = bal;
          lastTradeBalance = bal;
          persistBaselineAndWear();
        } else {
          const delta = bal - lastTradeBalance;
          if (Number.isFinite(delta) && delta !== 0) {
            checkTradeCompletion(bal, delta);
            lastTradeBalance = bal;
            persistBaselineAndWear();
            updateTotalVolumeUI();
          }
        }
      }
    }, 1750);
  }

  function checkTradeCompletion(currentBalance, balanceChange) {
    const now = Date.now();
    const actualBalanceChange = Math.abs(balanceChange);
    
    tradeQueue = tradeQueue.filter(trade => (now - trade.timestamp) < TRADE_DETECTION_WINDOW_MS);
    for (const [id, pair] of tradePairs) {
      if ((now - pair.timestamp) > TRADE_DETECTION_WINDOW_MS) {
        tradePairs.delete(id);
      }
    }
    if (balanceChange > 0 && actualBalanceChange < REFUND_THRESHOLD) {
      refundAmount += actualBalanceChange;
      return;
    }
    
    if (balanceChange > 0) {
      for (const [id, pair] of tradePairs) {
        if (!pair.sell && pair.buy && Math.abs(actualBalanceChange - pair.buy) <= pair.buy * 0.1) {
          pair.sell = actualBalanceChange;
          pair.timestamp = now;
          onTradePairCompleted(pair.buy, pair.sell, balanceChange);
          
          tradePairs.delete(id);
          return;
        }
      }
    }
    
    if (balanceChange < 0) {
      let bestMatch = null;
      let bestMatchIndex = -1;
      let minDifference = Infinity;
      
      for (let i = 0; i < tradeQueue.length; i++) {
        const trade = tradeQueue[i];
        const expectedAmount = trade.amount;
        const difference = Math.abs(actualBalanceChange - expectedAmount);
        const ratio = actualBalanceChange / expectedAmount;
        
        if (ratio >= 0.5 && ratio <= 2.0 && difference < minDifference) {
          minDifference = difference;
          bestMatch = trade;
          bestMatchIndex = i;
        }
      }
      
      if (bestMatch && bestMatchIndex >= 0) {
        const tradeId = ++tradeIdCounter;
        tradePairs.set(tradeId, {
          buy: actualBalanceChange,
          sell: null,
          timestamp: now
        });
        
        tradeQueue.splice(bestMatchIndex, 1);
        return;
      }
    }
    
    if (pendingTradeAmount > 0 && (now - pendingTradeTimestamp) < TRADE_DETECTION_WINDOW_MS) {
      const ratio = actualBalanceChange / pendingTradeAmount;
      if (ratio >= 0.5 && ratio <= 2.0) {
        if (balanceChange < 0) {
          const tradeId = ++tradeIdCounter;
          tradePairs.set(tradeId, {
            buy: actualBalanceChange,
            sell: null,
            timestamp: now
          });
        } else {
          onTradeCompleted(pendingTradeAmount, balanceChange);
        }
        
        pendingTradeAmount = 0;
        pendingTradeTimestamp = 0;
        lastBalanceBeforeTrade = NaN;
        return;
      }
    }
    if (actualBalanceChange > MIN_BALANCE_CHANGE_THRESHOLD) {
    }
  }

  function recordPendingTrade(amount) {
    if (Number.isFinite(amount) && amount > 0) {
      const now = Date.now();
      
      if (pendingTradeAmount > 0) {
        tradeQueue.push({
          amount: pendingTradeAmount,
          timestamp: pendingTradeTimestamp
        });
        
        if (tradeQueue.length > MAX_QUEUE_SIZE) {
          tradeQueue.shift();
        }
        
      }
      
      pendingTradeAmount = amount;
      pendingTradeTimestamp = now;
      lastBalanceBeforeTrade = readDomBalance();
      
    }
  }

  async function onTradePairCompleted(buyAmount, sellAmount, balanceChange) {
    try {
      const sym = await getCurrentSymbolUpper();
      if (!sym) return;
      
      const actualTradeAmount = sellAmount;
      
      const commitKey = `${sym}|${actualTradeAmount.toFixed(8)}`;
      const now = Date.now();
      
      if (lastCommit.key === commitKey && (now - lastCommit.ts) < 5000) return;
      
      const rec = tokenRecords.get(sym) || { buy: 0, total: 0 };
      const newBuy = rec.buy + actualTradeAmount;
      const newTotal = newBuy * (Number(currentMultiplier) || 1);
      tokenRecords.set(sym, { buy: newBuy, total: newTotal });
      
      const wearAmount = sellAmount - buyAmount + refundAmount;
      wearValue += wearAmount;
      
      refundAmount = 0;
      
      lastCommit = { key: commitKey, ts: now };
      persistTotalsIfNeeded();
      persistBaselineAndWear();
      updateTotalVolumeUI();
      
    } catch (error) {
    }
  }

  async function onTradeCompleted(amount, balanceChange) {
    try {
      const sym = await getCurrentSymbolUpper();
      if (!sym) return;
      
      const actualTradeAmount = Math.abs(balanceChange);
      
      const commitKey = `${sym}|${actualTradeAmount.toFixed(8)}`;
      const now = Date.now();
      
      if (lastCommit.key === commitKey && (now - lastCommit.ts) < 5000) return;
      
      const rec = tokenRecords.get(sym) || { buy: 0, total: 0 };
      const newBuy = rec.buy + actualTradeAmount;
      const newTotal = newBuy * (Number(currentMultiplier) || 1);
      tokenRecords.set(sym, { buy: newBuy, total: newTotal });
      
      lastCommit = { key: commitKey, ts: now };
      persistTotalsIfNeeded();
      updateTotalVolumeUI();
      
    } catch (error) {
    }
  }
  function updateTotalVolumeUI() {
    if (!DOM.totalVolume) return;
    let totalCalculated = 0;
    for (const [, rec] of tokenRecords) totalCalculated += Number(rec.total) || 0;
    DOM.totalVolume.textContent = totalCalculated > 0 ? ` ${totalCalculated.toFixed(2)}` : ' —';
    DOM.totalVolume.style.color = getColor(totalCalculated, '#ffcc00', '#ffcc00', '#CCCCCC');
    if (DOM.volumeIntegral) {
      const integral = calculateIntegral(totalCalculated);
      DOM.volumeIntegral.textContent = Number.isFinite(integral) ? ` ${integral}` : ' —';
      DOM.volumeIntegral.style.color = '#ffcc00';
    }
    if (DOM.wear) {
      let wearRateText = Number.isFinite(wearValue) ? ` ${wearValue.toFixed(2)}` : ' —';
      if (Number.isFinite(wearValue)) {
        let totalBuyAmount = 0;
        for (const [, rec] of tokenRecords) totalBuyAmount += Number(rec.buy) || 0;
        if (totalBuyAmount > 0) {
          const wearRate = Math.abs(wearValue) * 10000 / totalBuyAmount;
          wearRateText = ` ${wearValue.toFixed(2)} / ${wearRate.toFixed(2)}`;
        }
      }
      DOM.wear.textContent = wearRateText;
      DOM.wear.style.color = getColor(wearValue);
    }
  }
  const calculateIntegral = n => n<2?0:Math.min(25,Math.floor(Math.log2(n)));

  const getColor = (value, positive='#00ff88', negative='#ff6666', neutral='#CCCCCC') => {
    return Number.isFinite(value) ? (value>0?positive:(value<0?negative:neutral)) : neutral;
  };

  async function fetchOther4xTokens() {
    const now = Date.now();
    if (recentStableCache && (now - recentStableCacheTime) < RECENT_STABLE_CACHE_MS) {
      return recentStableCache;
    }
    try {
      const response = await fetch('https://www.binance.com/bapi/defi/v1/public/wallet-direct/buw/wallet/cex/alpha/all/token/list');
      const data = await response.json();
      if (data.success && data.data) {
        const currentAlphaId = await getCurrentAlphaId();
        const other4xTokens = data.data.filter(token => 
          token.mulPoint === 4 && 
          token.alphaId !== currentAlphaId &&
          !token.offline
        );
        recentStableCache = other4xTokens;
        recentStableCacheTime = now;
        return other4xTokens;
      }
    } catch (_) {}
    return [];
  }

  async function calculateTokenStability(token) {
    try {
      const response = await fetch(`https://www.binance.com/bapi/defi/v1/public/alpha-trade/agg-trades?symbol=${token.alphaId}USDT&limit=180`);
      const data = await response.json();
      if (data.success && data.data && data.data.length >= 5) {
        const trades = data.data;
        const prices = trades.map(t => parseFloat(t.p));
        const vwap = trades.reduce((sum, t) => sum + parseFloat(t.p) * parseFloat(t.q), 0) / 
                    trades.reduce((sum, t) => sum + parseFloat(t.q), 0);
        if (isNaN(vwap) || vwap === 0) return { stability: 0, token };
        
        const sortedPrices = prices.sort((a, b) => a - b);
        const p05 = sortedPrices[Math.floor(sortedPrices.length * 0.05)];
        const p95 = sortedPrices[Math.floor(sortedPrices.length * 0.95)];
        const rangePct = Math.abs((p95 - p05) / vwap) * 100;
        
        const volume24h = parseFloat(token.volume24h) || 0;
        const liquidity = parseFloat(token.liquidity) || 0;
        
        return { 
          stability: rangePct, 
          token,
          volume24h,
          liquidity
        };
      }
    } catch (_) {}
    return { 
      stability: Infinity, 
      token,
      volume24h: 0,
      liquidity: 0
    };
  }

  async function findMostStableToken() {
    const tokens = await fetchOther4xTokens();
    if (tokens.length === 0) return null;
    
    const stabilityResults = await Promise.all(
      tokens.map(token => calculateTokenStability(token))
    );
    
    const validTokens = stabilityResults.filter(result => 
      result.stability < Infinity && result.stability <= stableTolerancePct
    );
    
    if (validTokens.length === 0) return null;
    
    const mostStable = validTokens.reduce((best, current) => {
      if (current.volume24h > best.volume24h) {
        return current;
      } else if (current.volume24h === best.volume24h) {
        if (current.stability < best.stability) {
          return current;
        } else if (current.stability === best.stability) {
          if (current.liquidity > best.liquidity) {
            return current;
          }
        }
      }
      return best;
    });
    
    return mostStable;
  }

  async function updateRecentStableUI() {
    if (!DOM.recentStable) return;
    try {
      const mostStable = await findMostStableToken();
      if (mostStable) {
        DOM.recentStable.innerHTML = `
          <div class="bn-flex items-center gap-[8px]">
            <div class="relative w-[16px] h-[16px]">
              <img class="overflow-hidden rounded-full w-full h-full" src="${mostStable.token.iconUrl}" style="width: 16px; height: 16px;">
            </div>
            <div>
              <div class="text-[12px] font-[500] text-PrimaryText">${mostStable.token.symbol}</div>
            </div>
          </div>
        `;
        DOM.recentStable.style.color = '#00ff88';
        DOM.recentStable.style.cursor = 'pointer';
        DOM.recentStable.style.textDecoration = 'none';
        DOM.recentStable.onclick = null;
        DOM.recentStable.onclick = (e) => {
          e.preventDefault();
          const langPath = currentLang === 'en' ? '/en' : '/zh-CN';
          const url = `${langPath}/alpha/bsc/${mostStable.token.contractAddress}`;
          
          if (window.history && window.history.pushState) {
            window.history.pushState(null, '', url);
            window.dispatchEvent(new PopStateEvent('popstate'));
            
            setTimeout(() => {
              recentStableCache = null;
              recentStableCacheTime = 0;
              updateRecentStableUI();
            }, 1000);
          } else {
            window.location.href = url;
          }
        };
      } else {
        DOM.recentStable.textContent = ` ${t('none')}`;
        DOM.recentStable.style.color = '#CCCCCC';
        DOM.recentStable.style.cursor = 'default';
        DOM.recentStable.style.textDecoration = 'none';
        DOM.recentStable.onclick = null;
      }
    } catch (_) {
      DOM.recentStable.textContent = ` ${t('none')}`;
      DOM.recentStable.style.color = '#CCCCCC';
      DOM.recentStable.style.cursor = 'default';
      DOM.recentStable.style.textDecoration = 'none';
      DOM.recentStable.onclick = null;
    }
  }

  function startUnifiedObserver() {
    let setupCompleted = false;
    const mo = new MutationObserver(() => {
      if (!setupCompleted) {
        const bar = ensureMetricsBar();
        if (bar) {
          setupCompleted = true;
          mo.disconnect();
          setup();
          return;
        }
      }
    });
    mo.observe(document.body, { childList: true, subtree: true, characterData: true });
    
    Timers.setTimeout('setupTimeout', () => {
      if (!setupCompleted) {
        setupCompleted = true;
        mo.disconnect();
        setup();
      }
    }, 20000);
  }
function saveTotalsToStorage() {
    const obj = {};
  for (const [k, v] of tokenRecords) {
      obj[k] = { buy: Number(v.buy) || 0, total: Number(v.total) || 0 };
    }
    Storage.set(STORAGE_KEYS.totalRecords, obj);
  }
  function loadTotalsFromStorage() {
  const parsed = Storage.get(STORAGE_KEYS.totalRecords, {});
  if (parsed && typeof parsed === 'object') {
    tokenRecords.clear();
    for (const k of Object.keys(parsed)) {
      const v = parsed[k] || {};
      const buy = Number(v.buy) || 0;
      const total = Number(v.total) || 0;
      if (buy > 0 || total > 0) tokenRecords.set(k, { buy, total });
    }
  }
  }
  function persistTotalsIfNeeded() { saveTotalsToStorage(); }
  function persistBaselineAndWear() {
    if (Number.isFinite(baselineBalance)) Storage.set(STORAGE_KEYS.baselineBalance, baselineBalance);
    Storage.set(STORAGE_KEYS.wearValue, Number(wearValue) || 0);
    if (Number.isFinite(lastTradeBalance)) Storage.set(STORAGE_KEYS.lastTradeBalance, lastTradeBalance);
  }
function loadBaselineAndWear() {
  const w = Storage.get(STORAGE_KEYS.wearValue, 0);
  wearValue = Number.isFinite(w) ? w : 0;
  const b = Storage.get(STORAGE_KEYS.baselineBalance, NaN);
  baselineBalance = Number.isFinite(b) ? b : NaN;
  const lt = Storage.get(STORAGE_KEYS.lastTradeBalance, NaN);
  lastTradeBalance = Number.isFinite(lt) ? lt : NaN;
}
  function startRecentStableLoop() {
    updateRecentStableUI();
    Timers.set('recentStable', updateRecentStableUI, RECENT_STABLE_CACHE_MS);
  }

  function startURLWatcher() {
    let lastURL = window.location.href;
    Timers.set('urlWatcher', () => {
      const currentURL = window.location.href;
      if (currentURL !== lastURL) {
        lastURL = currentURL;
        setTimeout(() => {
          recentStableCache = null;
          recentStableCacheTime = 0;
          updateRecentStableUI();
        }, 500);
      }
    }, 500);
  }

  function cleanup() {
    Timers.clearAll();
    sampleBuffer = [];
    recentStableCache = null;
    recentStableCacheTime = 0;
    tokenMapCache = null;
    tokenMapCacheTime = 0;
  }

  function setup() {
    const target = insertMetricsIfMissing();
    if (!target) return;
    DOM.init();
    loadTotalsFromStorage();
    loadBaselineAndWear();
    startStableLoop();
    startMultiplierCountdown();
    startAmountWatcher();
    startBalanceWatcher();
    startRecentStableLoop();
    startURLWatcher();
    updateTotalVolumeUI();
  }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', startUnifiedObserver, { once: true });
  } else {
    startUnifiedObserver();
  }

  window.addEventListener('beforeunload', cleanup);
})();