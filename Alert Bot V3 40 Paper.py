"""
바이낸스 선물 EMA 터치 실시간 알림봇 (텔레그램) v3.40-paper (유동적 봉 개수 자동 조절 + 엘리어트 파동 + 정밀 피보나치 통합판)
- 15분/1시간/4시간/12시간/일/주봉 x EMA 7, 25, 99 터치 후 반등/거절 알림 (고해상도 대형 차트 첨부)
- 차트에 피보나치 시작점(START 1.0)·끝지점(END 0.0) 마커, 엘리어트 파동 피벗([0]~[4]/[A]~[E]),
  파동 위치별 맞춤 되돌림(2파 0.382~0.618 / 4파 0.236~0.382), 확장 목표가(TGT), POC, NOW 가격 라벨 표시
- 버튼: 휴대폰/PC 키보드 자판이 절대 뜨지 않는 인라인 메뉴 버튼 적용
- 최적화: 메모리 슬라이싱 고속 렌더링 + HTTP 세션 재사용 + 스마트 캔들/선물지표 캐시 + 알림 상태 영속화
- v3.18~v3.39 모든 기능 및 설정/핫패치/업데이트 100% 호환 유지
- v3.40 유동적(Adaptive) 캔들 개수 자동 조절 & 실시간 배율 버튼 업그레이드:
  1) 1번째 사진(큰 그림, Macro View) 유동 확장(기본 65~150봉):
     · 고정 60봉 대신 최근 150봉 내에서 대파동(임펄스 0~4파 또는 주요 스윙 고/저점)의 시작점이 잘리지 않도록
       파동 크기를 역추적해 큰 그림 봉 개수를 자동으로 늘려 잡음 (예: 대파동이 길면 110~145봉, 짧으면 70~85봉)
  2) 2번째 사진(확대 차트, Micro Zoom View) 유동 축소(기본 16~42봉):
     · 고정 30봉 대신 현재 진행 중인 막바지 스윙 파동(START 1.0 ~ END 0.0 ~ 현재 눌림목)의 실제 길이에 맞춰
       불필요한 과거 봉을 덜어내고 16~42봉 사이로 촘촘하게 자동 줌인하여 타점 가독성을 극대화
  3) 차트 하단 실시간 배율 변경 인라인 버튼 & 명령어 지원:
     · 차트 밑에 [🔭120봉] [📊80봉] [🔍25봉] [🔬15봉] [🤖자동파동맞춤] 버튼을 배치해 언제든 원터치로 봉 개수를 늘리거나 줄여서 확인 가능
     · 채팅 명령어: '전체봉 110', '확대봉 22', '차트 BTC 4h 120' 지원 및 ⚙️설정에서 유동 봉 개수 켜기/끄기 지원
- 실행: python alert_bot_v3_40_paper.py     연결 테스트: python alert_bot_v3_40_paper.py --test
- 환경변수: TELEGRAM_TOKEN, TELEGRAM_CHAT_ID
"""
import os
import sys
import json
import time
import copy
import math
import signal
import re
import zlib
import struct
from datetime import datetime, timezone, timedelta

import requests

VERSION = "v3.40-paper (유동적봉개수·큰그림확장/확대축소·엘리어트파동·정밀피보나치·1초응답)"
VERSION_FILE = os.path.basename(__file__) if "__file__" in globals() else "alert_bot_v3_40_paper.py"
HOT_PATCH_ENABLED = True  # 텔레그램 채팅 "패치" 기능 (TELEGRAM_CHAT_ID 로 등록된 내 채팅방에서만 동작)
FULL_N = 90   # 유동 모드가 꺼져 있을 때 1번째(큰 그림) 차트 기본 캔들 개수
ZOOM_N = 24   # 유동 모드가 꺼져 있을 때 2번째(확대) 차트 기본 캔들 개수
FULL_MIN_N, FULL_MAX_N = 65, 150  # 유동 큰 그림 자동 조절 범위(봉)
ZOOM_MIN_N, ZOOM_MAX_N = 16, 42   # 유동 확대 차트 자동 조절 범위(봉)
POLL_SECONDS = 20        # EMA/급변 시세 스캔 주기(초)
FAST_CHECK_SECONDS = 5   # 가격 목표 알림 및 가상매매 포지션(SL/TP/반익절) 고빈도 확인 주기(초)
BOT_TICK_SECONDS = 1     # 두 텔레그램 봇의 버튼/메시지 즉시 응답을 위한 폴링 틱(초)

# 네트워크 속도 및 안정성 최적화를 위한 전역 세션(Connection Pool)
HTTP = requests.Session()
HTTP.headers.update({"User-Agent": "TradingAlertBot/3.40"})

ALLOWED_TF = ["5m", "15m", "1h", "4h", "12h", "1d", "1w"]
TF_RANK = {"5m": 1, "15m": 2, "1h": 3, "4h": 4, "12h": 5, "1d": 6, "1w": 7}
EMA_LIST = [7, 25, 99]

DEFAULTS = {
    "symbols": {"BTCUSDT": True, "ETHUSDT": True, "SOLUSDT": True},
    "tf_on": {tf: (tf != "5m") for tf in ALLOWED_TF},  # 5분봉은 차트용(일반 EMA 알림은 설정에서 켜기)
    "ema_on": {"7": True, "25": True, "99": True},
    "config_version": 340,
    "min_count": 1,              # 최근 기간 안에 같은 방향 신호가 이 횟수 이상일 때만 알림 (5분봉은 최근 2시간)
    "rep_on": True,              # 15분봉 EMA7 반복 터치 알림
    "rep_touch_min": 2,          # 이전에 EMA7을 이 횟수 이상 터치했어야 함
    "rep_window": 24,            # 최근 몇 개 15분봉을 볼지 (24개 = 6시간)
    "update_url": "",
    "surge_on": True,
    "surge_change_pct": 0.7,     # 5분봉 시가 대비 급변 기준(%)
    "surge_volume_mult": 2.5,    # 이전 20개 마감봉 평균 거래량 배수
    "fib_on": True,              # 차트에 엘리어트 파동 & 피보나치 되돌림/확장 및 텍스트 라벨 표시
    "zoom_on": True,             # 두 번째 사진으로 확대 차트 추가 전송
    "vol_on": True,              # 차트 하단에 거래량 바 + 20MA 및 POC(핵심 매물대) 표시
    "mtf_on": True,              # 가상매매 진입 시 상위 시간봉 추세 필터 및 타임프레임 위계 보호 적용
    "ew_on": True,               # 엘리어트 파동 카운팅(2파/4파/삼각형/다이아고날) 및 파동 맞춤 피보나치/SL/TP 적용
    "dyn_bars_on": True,         # 파동 크기에 맞춰 1번(큰그림 65~150봉)은 늘리고 2번(확대 16~42봉)은 줄이는 유동 봉 개수 모드
    "full_n": FULL_N,            # 수동 모드일 때 1번(큰 그림) 기본 봉 개수
    "zoom_n": ZOOM_N,            # 수동 모드일 때 2번(확대) 기본 봉 개수
}
# 터치 후 벗어났다고 인정하는 최소 이동 폭(%)
MIN_MOVE_PCT = {"5m": 0.03, "15m": 0.05, "1h": 0.1, "4h": 0.15, "12h": 0.2, "1d": 0.3, "1w": 0.5}
LOOKBACK_HOURS = {"5m": 2, "15m": 6, "1h": 24, "4h": 24, "12h": 48, "1d": 168, "1w": 672}
TF_LABEL = {"5m": "5분봉", "15m": "15분봉", "1h": "1시간봉", "4h": "4시간봉", "12h": "12시간봉", "1d": "일봉", "1w": "주봉"}
LOOK_LABEL = {"5m": "2시간", "15m": "6시간", "1h": "24시간", "4h": "24시간", "12h": "48시간", "1d": "7일", "1w": "4주"}

BASES = [
    "https://fapi.binance.com",
    "https://fapi1.binance.com",
    "https://fapi2.binance.com",
    "https://fapi3.binance.com",
]
KST = timezone(timedelta(hours=9))
CONFIG_FILE = os.path.expanduser("~/alert_config.json")
STATE_FILE = os.path.expanduser("~/alert_state.json")
PID_FILE = os.path.expanduser("~/alert_bot.pid")

alerted = {}             # 순서 유지 딕셔너리로 오래된 알림만 선별 정리
surge_alerted = {}       # 5분봉 급변 중복 알림 방지
closed_candle_seen = set()
update_offset = [0]

# API 중복 호출 방지용 단기 캐시
_CANDLE_CACHE = {}       # {(symbol, interval, limit): (timestamp, candles)}
_SENTIMENT_CACHE = {}    # {symbol: {"ts": float, "funding": float, "oi": float, "oi_chg": float}}
_MTF_TREND_CACHE = {}    # {(symbol, tf): (timestamp, trend_dict)}

CHART_BUTTONS = {
    "📈5분": "5m",
    "📈15분": "15m",
    "📈1시간": "1h",
    "📈4시간": "4h",
    "📈12시간": "12h",
    "📈일봉": "1d",
    "📈주봉": "1w",
}

# 자판이 절대 올라오지 않는 인라인 메뉴 버튼 (배율 즉시 조절 버튼 포함)
MAIN_INLINE_MARKUP = {
    "inline_keyboard": [
        [
            {"text": "📈5분", "callback_data": "ct:5m"},
            {"text": "📈15분", "callback_data": "ct:15m"},
            {"text": "📈1시간", "callback_data": "ct:1h"},
            {"text": "📈4시간", "callback_data": "ct:4h"},
            {"text": "📈12시간", "callback_data": "ct:12h"},
        ],
        [
            {"text": "📈일봉", "callback_data": "ct:1d"},
            {"text": "📈주봉", "callback_data": "ct:1w"},
            {"text": "📊현황", "callback_data": "act:status"},
            {"text": "⚙️설정", "callback_data": "act:settings"},
            {"text": "🔄업데이트", "callback_data": "act:update"},
        ],
        [
            {"text": "🔭120봉", "callback_data": "cb:15m:120"},
            {"text": "📊80봉", "callback_data": "cb:15m:80"},
            {"text": "🔍25봉", "callback_data": "cb:15m:25"},
            {"text": "🕯15봉", "callback_data": "c15:15m"},
            {"text": "🤖자동봉", "callback_data": "cba:15m"},
        ],
        [
            {"text": "🔔알림목록", "callback_data": "act:alerts"},
        ],
    ]
}
REMOVE_KEYBOARD = {"remove_keyboard": True}

# 외부 라이브러리 없이 고해상도 PNG에 숫자와 영문을 찍기 위한 5x7 비트맵 폰트
FONT_5X7 = {
    "0": ["01110", "10001", "10011", "10101", "11001", "10001", "01110"],
    "1": ["00100", "01100", "00100", "00100", "00100", "00100", "01110"],
    "2": ["01110", "10001", "00001", "00010", "00100", "01000", "11111"],
    "3": ["11110", "00001", "00001", "01110", "00001", "00001", "11110"],
    "4": ["00010", "00110", "01010", "10010", "11111", "00010", "00010"],
    "5": ["11111", "10000", "11110", "00001", "00001", "10001", "01110"],
    "6": ["00110", "01000", "10000", "11110", "10001", "10001", "01110"],
    "7": ["11111", "00001", "00010", "00100", "01000", "01000", "01000"],
    "8": ["01110", "10001", "10001", "01110", "10001", "10001", "01110"],
    "9": ["01110", "10001", "10001", "01111", "00001", "00010", "01100"],
    ".": ["00000", "00000", "00000", "00000", "00000", "01100", "01100"],
    ",": ["00000", "00000", "00000", "00000", "00110", "00100", "01000"],
    "-": ["00000", "00000", "00000", "11111", "00000", "00000", "00000"],
    "+": ["00000", "00100", "00100", "11111", "00100", "00100", "00000"],
    ":": ["00000", "01100", "01100", "00000", "01100", "01100", "00000"],
    "(": ["00010", "00100", "01000", "01000", "01000", "00100", "00010"],
    ")": ["01000", "00100", "00010", "00010", "00010", "00100", "01000"],
    "[": ["01110", "01000", "01000", "01000", "01000", "01000", "01110"],
    "]": ["01110", "00010", "00010", "00010", "00010", "00010", "01110"],
    " ": ["00000", "00000", "00000", "00000", "00000", "00000", "00000"],
    "=": ["00000", "00000", "11111", "00000", "11111", "00000", "00000"],
    "/": ["00001", "00010", "00010", "00100", "01000", "01000", "10000"],
    "%": ["11001", "11010", "00100", "01000", "10110", "00110", "00000"],
    "|": ["00100", "00100", "00100", "00100", "00100", "00100", "00100"],
    "!": ["00100", "00100", "00100", "00100", "00100", "00000", "00100"],
    "A": ["01110", "10001", "10001", "11111", "10001", "10001", "10001"],
    "B": ["11110", "10001", "10001", "11110", "10001", "10001", "11110"],
    "C": ["01111", "10000", "10000", "10000", "10000", "10000", "01111"],
    "D": ["11110", "10001", "10001", "10001", "10001", "10001", "11110"],
    "E": ["11111", "10000", "10000", "11110", "10000", "10000", "11111"],
    "F": ["11111", "10000", "10000", "11110", "10000", "10000", "10000"],
    "G": ["01111", "10000", "10000", "10111", "10001", "10001", "01111"],
    "H": ["10001", "10001", "10001", "11111", "10001", "10001", "10001"],
    "I": ["01110", "00100", "00100", "00100", "00100", "00100", "01110"],
    "J": ["00111", "00010", "00010", "00010", "10010", "10010", "01100"],
    "K": ["10001", "10010", "10100", "11000", "10100", "10010", "10001"],
    "L": ["10000", "10000", "10000", "10000", "10000", "10000", "11111"],
    "M": ["10001", "11011", "10101", "10101", "10001", "10001", "10001"],
    "N": ["10001", "11001", "10101", "10011", "10001", "10001", "10001"],
    "O": ["01110", "10001", "10001", "10001", "10001", "10001", "01110"],
    "P": ["11110", "10001", "10001", "11110", "10000", "10000", "10000"],
    "Q": ["01110", "10001", "10001", "10001", "10101", "10010", "01101"],
    "R": ["11110", "10001", "10001", "11110", "10100", "10010", "10001"],
    "S": ["01111", "10000", "10000", "01110", "00001", "00001", "11110"],
    "T": ["11111", "00100", "00100", "00100", "00100", "00100", "00100"],
    "U": ["10001", "10001", "10001", "10001", "10001", "10001", "01110"],
    "V": ["10001", "10001", "10001", "10001", "10001", "01010", "00100"],
    "W": ["10001", "10001", "10001", "10101", "10101", "11011", "10001"],
    "X": ["10001", "10001", "01010", "00100", "01010", "10001", "10001"],
    "Y": ["10001", "10001", "01010", "00100", "00100", "00100", "00100"],
    "Z": ["11111", "00001", "00010", "00100", "01000", "10000", "11111"],
}
PAPER_FONT = dict(FONT_5X7)


# ---------------- 알림 상태 영속화 ----------------
def _key_to_str(k):
    return json.dumps(list(k) if isinstance(k, tuple) else k, ensure_ascii=False)


def _str_to_key(s):
    try:
        v = json.loads(s)
        return tuple(v) if isinstance(v, list) else v
    except Exception:
        return s


def load_alert_state():
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        for ks in d.get("alerted", [])[-3000:]:
            alerted[_str_to_key(ks)] = True
        for ks in d.get("surge_alerted", [])[-2000:]:
            surge_alerted[_str_to_key(ks)] = True
        for ks in d.get("closed_seen", []):
            closed_candle_seen.add(_str_to_key(ks))
    except FileNotFoundError:
        pass
    except Exception as e:
        print("알림 상태 불러오기 실패:", e)


def save_alert_state():
    try:
        d = {
            "alerted": [_key_to_str(k) for k in list(alerted.keys())[-2500:]],
            "surge_alerted": [_key_to_str(k) for k in list(surge_alerted.keys())[-1500:]],
            "closed_seen": [_key_to_str(k) for k in closed_candle_seen],
        }
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False)
        os.replace(tmp, STATE_FILE)
    except Exception as e:
        print("알림 상태 저장 실패:", e)


def mark_alerted(key):
    alerted[key] = True
    if len(alerted) > 3000:
        for old_k in list(alerted.keys())[:1500]:
            alerted.pop(old_k, None)
    save_alert_state()


# ---------------- 설정 저장/불러오기 ----------------
def load_cfg():
    cfg = copy.deepcopy(DEFAULTS)
    raw = {}
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            raw = json.load(f)
    except Exception:
        pass
    syms = raw.get("symbols")
    if isinstance(syms, list):
        cfg["symbols"] = {s: True for s in syms}
    elif isinstance(syms, dict) and syms:
        cfg["symbols"] = syms
    if isinstance(raw.get("tf_on"), dict):
        cfg["tf_on"].update(raw["tf_on"])
    elif isinstance(raw.get("timeframes"), list):
        for tf in ALLOWED_TF:
            if tf != "15m":
                cfg["tf_on"][tf] = tf in raw["timeframes"]
    if isinstance(raw.get("ema_on"), dict):
        cfg["ema_on"].update(raw["ema_on"])
    for k in ("min_count", "rep_on", "rep_touch_min", "rep_window", "update_url",
              "surge_on", "surge_change_pct", "surge_volume_mult", "fib_on", "zoom_on",
              "vol_on", "mtf_on", "ew_on", "dyn_bars_on", "full_n", "zoom_n"):
        if k in raw:
            cfg[k] = raw[k]

    cfg["config_version"] = 340
    if raw.get("config_version", 0) != 340:
        try:
            save_cfg(cfg)
        except Exception:
            pass
    return cfg


def save_cfg(cfg):
    tmp = CONFIG_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    os.replace(tmp, CONFIG_FILE)


def active_symbols(cfg):
    return [s for s, on in cfg["symbols"].items() if on]


def active_tfs(cfg):
    return [tf for tf in ALLOWED_TF if cfg["tf_on"].get(tf)]


def active_emas(cfg):
    return [n for n in EMA_LIST if cfg["ema_on"].get(str(n))]


# ---------------- 시세/지표 (바이낸스 선물 + 스마트 캐시) ----------------
def get_candles(symbol, interval, limit=500, ttl=3.5):
    """진행 중인 봉 포함. 마지막 봉의 종가 = 현재가."""
    now = time.monotonic()
    ck = (symbol, interval, limit)
    cached = _CANDLE_CACHE.get(ck)
    if cached and (now - cached[0]) < ttl:
        return cached[1]
    if limit < 500:
        cached500 = _CANDLE_CACHE.get((symbol, interval, 500))
        if cached500 and (now - cached500[0]) < ttl and len(cached500[1]) >= limit:
            return cached500[1][-limit:]

    last_err = None
    for base in BASES:
        try:
            r = HTTP.get(
                base + "/fapi/v1/klines",
                params={"symbol": symbol, "interval": interval, "limit": limit},
                timeout=10,
            )
            r.raise_for_status()
            data = [{"t": k[0], "o": float(k[1]), "h": float(k[2]),
                     "l": float(k[3]), "c": float(k[4]), "v": float(k[5])} for k in r.json()]
            _CANDLE_CACHE[ck] = (now, data)
            if len(_CANDLE_CACHE) > 200:
                for old_k in list(_CANDLE_CACHE.keys())[:100]:
                    _CANDLE_CACHE.pop(old_k, None)
            return data
        except Exception as e:
            last_err = e
    raise RuntimeError("바이낸스 선물 접속 실패: %s" % last_err)


def get_futures_sentiment(symbol):
    """바이낸스 선물 펀딩비(Funding Rate) 및 미결제약정(Open Interest) 조회 (60초 캐시)"""
    now = time.monotonic()
    cached = _SENTIMENT_CACHE.get(symbol)
    if cached and (now - cached["ts"]) < 60.0:
        return cached
    funding_pct = None
    oi_val = None
    oi_chg_pct = 0.0
    for base in BASES:
        try:
            r1 = HTTP.get(base + "/fapi/v1/premiumIndex", params={"symbol": symbol}, timeout=5)
            if r1.status_code == 200:
                d1 = r1.json()
                funding_pct = float(d1.get("lastFundingRate", 0.0)) * 100.0
            r2 = HTTP.get(base + "/fapi/v1/openInterest", params={"symbol": symbol}, timeout=5)
            if r2.status_code == 200:
                d2 = r2.json()
                oi_val = float(d2.get("openInterest", 0.0))
            break
        except Exception:
            continue
    if cached and cached.get("oi") and oi_val:
        prev_oi = cached["oi"]
        if prev_oi > 0:
            oi_chg_pct = (oi_val - prev_oi) / prev_oi * 100.0
    info = {
        "ts": now,
        "funding": funding_pct,
        "oi": oi_val,
        "oi_chg": oi_chg_pct,
    }
    _SENTIMENT_CACHE[symbol] = info
    return info


def ema_series(closes, n):
    a = 2.0 / (n + 1)
    out = [closes[0]]
    for x in closes[1:]:
        out.append(a * x + (1 - a) * out[-1])
    return out


def rsi_series(closes, period=14):
    if len(closes) < 2:
        return [50.0] * len(closes)
    out = [50.0] * len(closes)
    gains, losses = [], []
    for i in range(1, len(closes)):
        d = closes[i] - closes[i - 1]
        gains.append(max(0.0, d))
        losses.append(max(0.0, -d))
    if len(gains) < period:
        return out
    avg_g = sum(gains[:period]) / period
    avg_l = sum(losses[:period]) / period
    out[period] = 100.0 if avg_l == 0 else (100.0 - 100.0 / (1.0 + avg_g / avg_l))
    for i in range(period, len(gains)):
        avg_g = (avg_g * (period - 1) + gains[i]) / period
        avg_l = (avg_l * (period - 1) + losses[i]) / period
        out[i + 1] = 100.0 if avg_l == 0 else (100.0 - 100.0 / (1.0 + avg_g / avg_l))
    return out


def atr_series(candles, period=14):
    if not candles:
        return []
    trs = [candles[0]["h"] - candles[0]["l"]]
    for i in range(1, len(candles)):
        h, l, pc = candles[i]["h"], candles[i]["l"], candles[i - 1]["c"]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    out = [trs[0]] * len(candles)
    if len(trs) < period:
        return out
    atr = sum(trs[:period]) / period
    out[period - 1] = atr
    for i in range(period, len(trs)):
        atr = (atr * (period - 1) + trs[i]) / period
        out[i] = atr
    return out


def calc_poc_info(candles, N=60, bins=24):
    """최근 N개 캔들의 가격대별 거래량 프로파일(Volume Profile)에서 최대 매물대(POC)를 계산"""
    cs = candles[-N:] if len(candles) >= N else candles
    if len(cs) < 5:
        return None
    lo = min(c["l"] for c in cs)
    hi = max(c["h"] for c in cs)
    span = hi - lo
    if span <= 0:
        return None
    step = span / bins
    vols = [0.0] * bins
    total_v = 0.0
    for c in cs:
        v = float(c.get("v", 0.0))
        if v <= 0:
            continue
        total_v += v
        typ = (c["h"] + c["l"] + c["c"]) / 3.0
        idx = min(bins - 1, max(0, int((typ - lo) / step)))
        vols[idx] += v
    if total_v <= 0:
        return None
    best_idx = max(range(bins), key=lambda i: vols[i])
    poc_low = lo + best_idx * step
    poc_high = poc_low + step
    poc_price = (poc_low + poc_high) * 0.5
    return {
        "price": poc_price,
        "low": poc_low,
        "high": poc_high,
        "share": vols[best_idx] / total_v * 100.0,
    }


def classify(c, v, move):
    if c["o"] >= v and c["l"] <= v and c["c"] >= v * (1 + move):
        return "long"
    if c["o"] <= v and c["h"] >= v and c["c"] <= v * (1 - move):
        return "short"
    return None


def fmt_p(v):
    if v >= 1000:
        return "{:,.1f}".format(v)
    elif v >= 10:
        return "{:,.2f}".format(v)
    else:
        return "{:,.4f}".format(v)


# ---------------- 엘리어트 파동 이론 + 정밀 피보나치 + 유동적 봉 개수 산출 엔진 ----------------
def extract_swing_pivots(cs, min_amp):
    """캔들 배열(cs)에서 최소 진폭(min_amp) 이상의 교대(High/Low) 스윙 피벗 시퀀스를 추출한다."""
    L = len(cs)
    if L < 5:
        return []
    raw = []
    for i in range(1, L - 1):
        l_h = max(cs[j]["h"] for j in range(max(0, i - 2), i))
        r_h = max(cs[j]["h"] for j in range(i + 1, min(L, i + 3)))
        if cs[i]["h"] >= l_h and cs[i]["h"] >= r_h:
            raw.append({"idx": i, "type": "H", "val": cs[i]["h"]})
        l_l = min(cs[j]["l"] for j in range(max(0, i - 2), i))
        r_l = min(cs[j]["l"] for j in range(i + 1, min(L, i + 3)))
        if cs[i]["l"] <= l_l and cs[i]["l"] <= r_l:
            raw.append({"idx": i, "type": "L", "val": cs[i]["l"]})

    first_type = "L" if cs[0]["c"] <= cs[min(L - 1, 3)]["c"] else "H"
    raw.insert(0, {"idx": 0, "type": first_type, "val": cs[0]["l"] if first_type == "L" else cs[0]["h"]})

    pivots = []
    for p in raw:
        if not pivots:
            pivots.append(dict(p))
            continue
        last = pivots[-1]
        if p["type"] == last["type"]:
            if (p["type"] == "H" and p["val"] >= last["val"]) or (p["type"] == "L" and p["val"] <= last["val"]):
                pivots[-1] = dict(p)
        else:
            if abs(p["val"] - last["val"]) >= min_amp:
                pivots.append(dict(p))
            elif len(pivots) >= 2:
                prev2 = pivots[-2]
                if (p["type"] == "H" and p["val"] > prev2["val"]) or (p["type"] == "L" and p["val"] < prev2["val"]):
                    pivots.pop()
                    pivots[-1] = dict(p)
    return pivots


def _leg_stats(cs, idx0, idx1):
    i0, i1 = min(idx0, idx1), max(idx0, idx1)
    bars = max(1, i1 - i0)
    vols = [float(cs[k].get("v", 0.0)) for k in range(i0, i1 + 1)]
    avg_v = sum(vols) / len(vols) if vols else 0.0
    return {"bars": bars, "avg_v": avg_v}


def calc_dynamic_window(candles, cfg=None):
    """파동 구조와 스윙 길이를 분석해:
    1) 1번째 사진(큰 그림, full_n): 대파동의 시작점([0]파/주요 고저점)이 잘리지 않도록 65~150봉 사이에서 유동적으로 늘리고,
    2) 2번째 사진(확대 차트, zoom_n): 최근 진행 중인 핵심 스윙/눌림목 길이에 맞춰 16~42봉 사이에서 유동적으로 줄여준다."""
    if cfg and not cfg.get("dyn_bars_on", True):
        fn = max(30, min(200, int(cfg.get("full_n", FULL_N))))
        zn = max(12, min(80, int(cfg.get("zoom_n", ZOOM_N))))
        return fn, zn

    total_len = len(candles)
    if total_len < 40:
        return min(total_len, FULL_N), min(total_len, ZOOM_N)

    # --- 1) 큰 그림(full_n, 65 ~ 150봉) 산출: 최근 150봉 내 대파동 시작점 추적 ---
    look_max = min(total_len, FULL_MAX_N)
    macro_cs = candles[-look_max:]
    m_hi = max(c["h"] for c in macro_cs)
    m_lo = min(c["l"] for c in macro_cs)
    m_span = m_hi - m_lo
    if m_span <= 0:
        return FULL_N, ZOOM_N

    pivots = extract_swing_pivots(macro_cs, m_span * 0.13)
    # 최근 4~5개 주요 파동 피벗의 시작점(예: 임펄스 0파 시작 또는 ABC 시작)이 화면 안에 넉넉히 들어오도록 설정
    if len(pivots) >= 5:
        anchor_idx = pivots[-5]["idx"]
    elif len(pivots) >= 3:
        anchor_idx = pivots[-3]["idx"]
    else:
        hi_i = max(range(len(macro_cs)), key=lambda i: macro_cs[i]["h"])
        lo_i = min(range(len(macro_cs)), key=lambda i: macro_cs[i]["l"])
        anchor_idx = min(hi_i, lo_i)

    needed_full = (len(macro_cs) - anchor_idx) + 8  # 시작 피벗 왼쪽에 8봉 여유 공간 확보
    full_n = max(FULL_MIN_N, min(FULL_MAX_N, needed_full))

    # --- 2) 확대 차트(zoom_n, 16 ~ 42봉) 산출: 최근 핵심 소파동(눌림목/반등) 길이에 밀착 ---
    micro_look = min(total_len, 50)
    micro_cs = candles[-micro_look:]
    u_hi = max(c["h"] for c in micro_cs)
    u_lo = min(c["l"] for c in micro_cs)
    u_span = u_hi - u_lo
    u_pivs = extract_swing_pivots(micro_cs, max(u_span * 0.15, m_span * 0.06))

    if len(u_pivs) >= 3:
        # 가장 최근 진행 중인 파동(직전 2개 피벗 ~ 현재 봉)이 꽉 차게 보이도록 설정
        u_anchor = u_pivs[-3]["idx"] if (len(micro_cs) - u_pivs[-2]["idx"]) < 10 else u_pivs[-2]["idx"]
        needed_zoom = (len(micro_cs) - u_anchor) + 5
    elif len(u_pivs) == 2:
        needed_zoom = (len(micro_cs) - u_pivs[0]["idx"]) + 4
    else:
        needed_zoom = ZOOM_N

    zoom_n = max(ZOOM_MIN_N, min(ZOOM_MAX_N, needed_zoom))
    # 확대 차트가 큰 그림의 60%를 넘지 않도록 보장해 1번·2번 사진의 배율 대비를 뚜렷하게 유지
    zoom_n = min(zoom_n, max(ZOOM_MIN_N, int(full_n * 0.55)))
    return int(full_n), int(zoom_n)


def calc_fib_info(candles, N=60):
    """엘리어트 파동 이론(임펄스 1~5파, 교대 법칙 2파 vs 4파, 확장 플랫 B파 보정, 수렴 삼각형, 엔딩 다이아고날)과
    피보나치 되돌림/확장 목표가를 결합한 정밀 스윙 분석기. 인덱스는 마지막 N개 봉 기준(차트 좌표)"""
    cs = candles[-N:] if len(candles) >= N else candles
    L = len(cs)
    if L < 12:
        return None

    overall_hi = max(c["h"] for c in cs)
    overall_lo = min(c["l"] for c in cs)
    total_span = overall_hi - overall_lo
    if total_span <= 0:
        return None

    # 1. 기본 스윙 파동 추출
    piv_hi, piv_lo = [], []
    for i in range(2, L - 1):
        h, l = cs[i]["h"], cs[i]["l"]
        left_h = [cs[j]["h"] for j in range(max(0, i - 2), i)]
        right_h = [cs[j]["h"] for j in range(i + 1, min(L, i + 3))]
        if h >= max(left_h) and h >= max(right_h):
            piv_hi.append(i)
        left_l = [cs[j]["l"] for j in range(max(0, i - 2), i)]
        right_l = [cs[j]["l"] for j in range(i + 1, min(L, i + 3))]
        if l <= min(left_l) and l <= min(right_l):
            piv_lo.append(i)

    recent_cut = max(0, L - max(20, int(L * 0.7)))
    cand_hi = [i for i in piv_hi if i >= recent_cut] or [max(range(recent_cut, L), key=lambda i: cs[i]["h"])]
    cand_lo = [i for i in piv_lo if i >= recent_cut] or [min(range(recent_cut, L), key=lambda i: cs[i]["l"])]

    hi_end = max(cand_hi, key=lambda i: cs[i]["h"])
    lo_end = min(cand_lo, key=lambda i: cs[i]["l"])

    up_wave = None
    if hi_end >= 3:
        lo_start = min(range(0, hi_end), key=lambda i: cs[i]["l"])
        amp = cs[hi_end]["h"] - cs[lo_start]["l"]
        if amp >= total_span * 0.25 and (hi_end - lo_start) >= 2:
            up_wave = (lo_start, hi_end, amp)

    down_wave = None
    if lo_end >= 3:
        hi_start = max(range(0, lo_end), key=lambda i: cs[i]["h"])
        amp = cs[hi_start]["h"] - cs[lo_end]["l"]
        if amp >= total_span * 0.25 and (lo_end - hi_start) >= 2:
            down_wave = (hi_start, lo_end, amp)

    if up_wave and down_wave:
        if up_wave[1] > down_wave[1]:
            chosen = ("up", up_wave[0], up_wave[1])
        elif down_wave[1] > up_wave[1]:
            chosen = ("down", down_wave[0], down_wave[1])
        else:
            chosen = ("up", up_wave[0], up_wave[1]) if up_wave[2] >= down_wave[2] else ("down", down_wave[0], down_wave[1])
    elif up_wave:
        chosen = ("up", up_wave[0], up_wave[1])
    elif down_wave:
        chosen = ("down", down_wave[0], down_wave[1])
    else:
        all_hi = max(range(L), key=lambda i: cs[i]["h"])
        all_lo = min(range(L), key=lambda i: cs[i]["l"])
        if all_lo < all_hi:
            chosen = ("up", all_lo, all_hi)
        else:
            chosen = ("down", all_hi, all_lo)

    mode, start_idx, end_idx = chosen
    if mode == "up":
        for k in range(end_idx + 1, L):
            if cs[k]["h"] >= cs[end_idx]["h"]:
                end_idx = k
    else:
        for k in range(end_idx + 1, L):
            if cs[k]["l"] <= cs[end_idx]["l"]:
                end_idx = k

    # 2. 다중 피벗(ZigZag) 추출 및 엘리어트 파동 규칙 적용
    pivots = extract_swing_pivots(cs, total_span * 0.14)
    ew_wave = "SWING"
    ew_label = "일반 스윙"
    ew_tag = "FIB"
    ew_warning = None
    ew_pivots = []
    ew_sl = None
    tp1_ext = None
    tp2_ext = None
    zone_lo_ratio, zone_hi_ratio = 0.382, 0.618
    zone_label = "0.382~0.618"

    price = cs[-1]["c"]

    # (A) 수렴 삼각형(Contracting / Running Triangle, PDF p.15~17)
    if len(pivots) >= 6:
        p0, pA, pB, pC, pD = pivots[-5], pivots[-4], pivots[-3], pivots[-2], pivots[-1]
        amp_A = abs(pA["val"] - p0["val"])
        amp_B = abs(pB["val"] - pA["val"])
        amp_C = abs(pC["val"] - pB["val"])
        amp_D = abs(pD["val"] - pC["val"])
        if amp_A > 0 and (amp_B <= amp_A * 1.382) and (amp_C < amp_B * 1.05) and (amp_D < amp_C * 1.05):
            st_early = _leg_stats(cs, p0["idx"], pB["idx"])
            st_late = _leg_stats(cs, pB["idx"], pD["idx"])
            if st_late["avg_v"] <= st_early["avg_v"] * 1.15:
                ew_wave = "TRIANGLE"
                ew_label = "📐 수렴 삼각형(ABCDE) · 5파 추력 대기"
                ew_tag = "EW:TRI"
                ew_pivots = [
                    {"idx": p0["idx"], "val": p0["val"], "lbl": "A"},
                    {"idx": pA["idx"], "val": pA["val"], "lbl": "B"},
                    {"idx": pB["idx"], "val": pB["val"], "lbl": "C"},
                    {"idx": pC["idx"], "val": pC["val"], "lbl": "D"},
                    {"idx": pD["idx"], "val": pD["val"], "lbl": "E"},
                ]
                if mode == "up":
                    tp1_ext = pD["val"] + amp_A * 0.618
                    tp2_ext = pD["val"] + amp_A * 1.0
                    ew_sl = min(pB["val"], pD["val"]) * 0.998
                else:
                    tp1_ext = pD["val"] - amp_A * 0.618
                    tp2_ext = pD["val"] - amp_A * 1.0
                    ew_sl = max(pB["val"], pD["val"]) * 1.002

    # (B) 임펄스 1-2-3-4파 및 엔딩 다이아고날 판별 (PDF p.3~10, p.21)
    if ew_wave == "SWING" and len(pivots) >= 4:
        cand_sets = [pivots[-4:]]
        if len(pivots) >= 5:
            cand_sets.insert(0, pivots[-5:-1])
        for pset in cand_sets:
            p0, p1, p2, p3 = pset[0], pset[1], pset[2], pset[3]
            if p3["idx"] < L - max(18, int(L * 0.35)):
                continue
            if p0["type"] == "L" and p1["type"] == "H" and p2["type"] == "L" and p3["type"] == "H":
                w1 = p1["val"] - p0["val"]
                w2_ret = (p1["val"] - p2["val"]) / w1 if w1 > 0 else 9.9
                w3 = p3["val"] - p2["val"]
                if w1 > 0 and 0.15 <= w2_ret < 1.0 and p3["val"] > p1["val"] and w3 >= w1 * 0.85:
                    w4_lo_idx = min(range(p3["idx"], L), key=lambda i: cs[i]["l"])
                    w4_lo = cs[w4_lo_idx]["l"]
                    w4_ret = (p3["val"] - w4_lo) / w3 if w3 > 0 else 0.0
                    overlap = w4_lo < p1["val"]

                    if overlap and w4_lo > p2["val"] and w4_ret < 0.786:
                        ew_wave = "END_DIAG"
                        ew_label = "⚠️ 다이아고날(1·4파 겹침) · 급반전 주의"
                        ew_tag = "EW:DIAG"
                        ew_warning = "1·4파 겹침(다이아고날 진행 또는 임펄스 무효)"
                        ew_pivots = [
                            {"idx": p0["idx"], "val": p0["val"], "lbl": "0"},
                            {"idx": p1["idx"], "val": p1["val"], "lbl": "1"},
                            {"idx": p2["idx"], "val": p2["val"], "lbl": "2"},
                            {"idx": p3["idx"], "val": p3["val"], "lbl": "3"},
                        ]
                        break

                    if not overlap and w4_ret <= 0.500:
                        mode = "up"
                        start_idx, end_idx = p2["idx"], p3["idx"]
                        ew_wave = "W4"
                        ew_label = "🌊 임펄스 4파 눌림 (교대법칙 0.236~0.382 존)"
                        ew_tag = "EW:W4"
                        zone_lo_ratio, zone_hi_ratio = 0.236, 0.382
                        zone_label = "0.236~0.382(4파존)"
                        ew_sl = max(p3["val"] - w3 * 0.500, p1["val"]) * 0.999
                        base_w4 = min(w4_lo, p3["val"] - w3 * 0.236)
                        tp1_ext = max(p3["val"], base_w4 + w1 * 0.618)
                        tp2_ext = max(tp1_ext * 1.004, base_w4 + (w1 * 1.0 if w3 >= w1 * 1.382 else (p3["val"] - p0["val"]) * 0.618))
                        ew_pivots = [
                            {"idx": p0["idx"], "val": p0["val"], "lbl": "0"},
                            {"idx": p1["idx"], "val": p1["val"], "lbl": "1"},
                            {"idx": p2["idx"], "val": p2["val"], "lbl": "2"},
                            {"idx": p3["idx"], "val": p3["val"], "lbl": "3"},
                        ]
                        if w4_lo_idx > p3["idx"]:
                            ew_pivots.append({"idx": w4_lo_idx, "val": w4_lo, "lbl": "4"})
                        break

            if p0["type"] == "H" and p1["type"] == "L" and p2["type"] == "H" and p3["type"] == "L":
                w1 = p0["val"] - p1["val"]
                w2_ret = (p2["val"] - p1["val"]) / w1 if w1 > 0 else 9.9
                w3 = p2["val"] - p3["val"]
                if w1 > 0 and 0.15 <= w2_ret < 1.0 and p3["val"] < p1["val"] and w3 >= w1 * 0.85:
                    w4_hi_idx = max(range(p3["idx"], L), key=lambda i: cs[i]["h"])
                    w4_hi = cs[w4_hi_idx]["h"]
                    w4_ret = (w4_hi - p3["val"]) / w3 if w3 > 0 else 0.0
                    overlap = w4_hi > p1["val"]

                    if overlap and w4_hi < p2["val"] and w4_ret < 0.786:
                        ew_wave = "END_DIAG"
                        ew_label = "⚠️ 하락 다이아고날(1·4파 겹침) · 급반등 주의"
                        ew_tag = "EW:DIAG"
                        ew_warning = "1·4파 겹침(다이아고날 진행 또는 임펄스 무효)"
                        ew_pivots = [
                            {"idx": p0["idx"], "val": p0["val"], "lbl": "0"},
                            {"idx": p1["idx"], "val": p1["val"], "lbl": "1"},
                            {"idx": p2["idx"], "val": p2["val"], "lbl": "2"},
                            {"idx": p3["idx"], "val": p3["val"], "lbl": "3"},
                        ]
                        break

                    if not overlap and w4_ret <= 0.500:
                        mode = "down"
                        start_idx, end_idx = p2["idx"], p3["idx"]
                        ew_wave = "W4"
                        ew_label = "🌊 하락 임펄스 4파 반등 (교대법칙 0.236~0.382 존)"
                        ew_tag = "EW:W4"
                        zone_lo_ratio, zone_hi_ratio = 0.236, 0.382
                        zone_label = "0.236~0.382(4파존)"
                        ew_sl = min(p3["val"] + w3 * 0.500, p1["val"]) * 1.001
                        base_w4 = max(w4_hi, p3["val"] + w3 * 0.236)
                        tp1_ext = min(p3["val"], base_w4 - w1 * 0.618)
                        tp2_ext = min(tp1_ext * 0.996, base_w4 - (w1 * 1.0 if w3 >= w1 * 1.382 else (p0["val"] - p3["val"]) * 0.618))
                        ew_pivots = [
                            {"idx": p0["idx"], "val": p0["val"], "lbl": "0"},
                            {"idx": p1["idx"], "val": p1["val"], "lbl": "1"},
                            {"idx": p2["idx"], "val": p2["val"], "lbl": "2"},
                            {"idx": p3["idx"], "val": p3["val"], "lbl": "3"},
                        ]
                        if w4_hi_idx > p3["idx"]:
                            ew_pivots.append({"idx": w4_hi_idx, "val": w4_hi, "lbl": "4"})
                        break

    # (C) 확장 플랫(Expanded Flat) B파 보정 및 2파/B파 눌림 판별 (PDF p.7, p.12, p.14)
    if mode == "up":
        swing_low = cs[start_idx]["l"]
        swing_high = cs[end_idx]["h"]
        diff = swing_high - swing_low
        if diff <= 0:
            return None
        cur_ret = (swing_high - price) / diff
        fib_236 = swing_high - diff * 0.236
        fib_382 = swing_high - diff * 0.382
        fib_500 = swing_high - diff * 0.500
        fib_618 = swing_high - diff * 0.618
        fib_786 = swing_high - diff * 0.786
        start_val, end_val = swing_low, swing_high
        hi_idx, lo_idx = end_idx, start_idx

        if ew_wave == "SWING":
            ret_low_idx = min(range(end_idx, L), key=lambda i: cs[i]["l"])
            ret_low = cs[ret_low_idx]["l"]
            max_ret = (swing_high - ret_low) / diff
            if 0.15 <= max_ret < 0.786:
                ew_wave = "W2"
                ew_label = "🌊 2파/B파 눌림 (0.382~0.618 골든존)"
                ew_tag = "EW:W2"
                ew_sl = swing_high - diff * 0.82
                proj_base = min(ret_low, fib_382)
                tp1_ext = max(swing_high * 1.002, proj_base + diff * 1.0)
                tp2_ext = max(tp1_ext * 1.004, proj_base + diff * 1.618)
                ew_pivots = [
                    {"idx": start_idx, "val": swing_low, "lbl": "0"},
                    {"idx": end_idx, "val": swing_high, "lbl": "1"},
                ]
                if ret_low_idx > end_idx:
                    ew_pivots.append({"idx": ret_low_idx, "val": ret_low, "lbl": "2"})
            elif 0.786 <= max_ret <= 1.0:
                ew_wave = "DEEP_ABC"
                ew_label = "⚠️ 깊은 되돌림(0.786↑) · 임펄스 2파보다 ABC/플랫 조정 주의"
                ew_tag = "EW:ABC"
                ew_warning = "0.786 이상 되돌림(조정파동 가능성 높음, p.7)"
                ew_sl = swing_low * 0.998
            elif 1.0 < max_ret <= 1.382:
                ew_wave = "EXP_FLAT_B"
                ew_label = "🔄 확장 플랫(Expanded Flat) B파 구간 (1.05~1.382 되돌림, p.14)"
                ew_tag = "EW:FLAT"
                ew_warning = "확장 플랫 조정 구간 주의(p.14)"
    else:
        swing_high = cs[start_idx]["h"]
        swing_low = cs[end_idx]["l"]
        diff = swing_high - swing_low
        if diff <= 0:
            return None
        cur_ret = (price - swing_low) / diff
        fib_236 = swing_low + diff * 0.236
        fib_382 = swing_low + diff * 0.382
        fib_500 = swing_low + diff * 0.500
        fib_618 = swing_low + diff * 0.618
        fib_786 = swing_low + diff * 0.786
        start_val, end_val = swing_high, swing_low
        hi_idx, lo_idx = start_idx, end_idx

        if ew_wave == "SWING":
            ret_high_idx = max(range(end_idx, L), key=lambda i: cs[i]["h"])
            ret_high = cs[ret_high_idx]["h"]
            max_ret = (ret_high - swing_low) / diff
            if 0.15 <= max_ret < 0.786:
                ew_wave = "W2"
                ew_label = "🌊 하락 2파/B파 반등 (0.382~0.618 골든존)"
                ew_tag = "EW:W2"
                ew_sl = swing_low + diff * 0.82
                proj_base = max(ret_high, fib_382)
                tp1_ext = min(swing_low * 0.998, proj_base - diff * 1.0)
                tp2_ext = min(tp1_ext * 0.996, proj_base - diff * 1.618)
                ew_pivots = [
                    {"idx": start_idx, "val": swing_high, "lbl": "0"},
                    {"idx": end_idx, "val": swing_low, "lbl": "1"},
                ]
                if ret_high_idx > end_idx:
                    ew_pivots.append({"idx": ret_high_idx, "val": ret_high, "lbl": "2"})
            elif 0.786 <= max_ret <= 1.0:
                ew_wave = "DEEP_ABC"
                ew_label = "⚠️ 깊은 반등(0.786↑) · 하락 2파보다 ABC/플랫 조정 주의"
                ew_tag = "EW:ABC"
                ew_warning = "0.786 이상 되돌림(조정파동 가능성 높음, p.7)"
                ew_sl = swing_high * 1.002
            elif 1.0 < max_ret <= 1.382:
                ew_wave = "EXP_FLAT_B"
                ew_label = "🔄 확장 플랫(Expanded Flat) B파 구간 (1.05~1.382 되돌림, p.14)"
                ew_tag = "EW:FLAT"
                ew_warning = "확장 플랫 조정 구간 주의(p.14)"

    if ew_wave == "W4":
        gz_a, gz_b = fib_236, fib_382
    else:
        gz_a, gz_b = fib_382, fib_618
    in_golden_zone = min(gz_a, gz_b) <= price <= max(gz_a, gz_b)
    retracing = (end_idx < (L - 1) or (mode == "up" and price < swing_high * 0.998)
                 or (mode == "down" and price > swing_low * 1.002))

    mode_label = ew_label if ew_wave != "SWING" else ("상승파동 눌림" if mode == "up" else "하락파동 반등")

    return {
        "mode": mode,
        "mode_label": mode_label,
        "ew_wave": ew_wave,
        "ew_label": ew_label,
        "ew_tag": ew_tag,
        "ew_warning": ew_warning,
        "ew_pivots": ew_pivots,
        "ew_sl": ew_sl,
        "tp1_ext": tp1_ext,
        "tp2_ext": tp2_ext,
        "zone_lo_ratio": zone_lo_ratio,
        "zone_hi_ratio": zone_hi_ratio,
        "zone_label": zone_label,
        "gz_a": gz_a,
        "gz_b": gz_b,
        "high": swing_high,
        "low": swing_low,
        "hi_idx": hi_idx,
        "lo_idx": lo_idx,
        "start_idx": start_idx,
        "end_idx": end_idx,
        "start_val": start_val,
        "end_val": end_val,
        "236": fib_236,
        "382": fib_382,
        "500": fib_500,
        "618": fib_618,
        "786": fib_786,
        "cur_ret": cur_ret,
        "in_zone": in_golden_zone,
        "retracing": retracing,
    }


def summarize(symbol, tf, cfg):
    candles = get_candles(symbol, tf)
    if len(candles) < 30:
        return None
    closes = [c["c"] for c in candles]
    last = len(candles) - 1
    price = candles[last]["c"]
    move = MIN_MOVE_PCT[tf] / 100.0
    cutoff = int(time.time() * 1000) - LOOKBACK_HOURS[tf] * 3600 * 1000
    ser_all = {n: ema_series(closes, n) for n in EMA_LIST}
    rsis = rsi_series(closes, 14)
    atrs = atr_series(candles, 14)
    closed_vols = [c.get("v", 0.0) for c in candles[max(0, last - 20):last]]
    avg_vol = sum(closed_vols) / len(closed_vols) if closed_vols else 0.0
    vol_ratio = candles[last].get("v", 0.0) / avg_vol if avg_vol > 0 else 1.0

    res = {
        "price": price,
        "t": candles[last]["t"],
        "emas": {},
        "candles": candles,
        "ser": ser_all,
        "rsi": rsis[-1],
        "atr": atrs[-1],
        "vol_ratio": vol_ratio,
    }
    for n in active_emas(cfg):
        ser = ser_all[n]
        longs = shorts = 0
        for i in range(min(n, last), len(candles)):
            if candles[i]["t"] < cutoff:
                continue
            s = classify(candles[i], ser[i], move)
            if s == "long":
                longs += 1
            elif s == "short":
                shorts += 1
        e = {"v": ser[last], "diff": (price - ser[last]) / ser[last] * 100.0,
             "side": classify(candles[last], ser[last], move),
             "longs": longs, "shorts": shorts}
        if tf == "15m" and n == 7:
            w = max(3, int(cfg["rep_window"]))
            touches = 0
            for i in range(max(n, last - w), last):
                if candles[i]["l"] <= ser[i] <= candles[i]["h"]:
                    touches += 1
            e["touches_prev"] = touches
        res["emas"][n] = e
    return res


def get_mtf_trend(symbol, tf):
    higher_map = {"5m": "1h", "15m": "1h", "1h": "4h", "4h": "1d", "12h": "1d", "1d": "1w"}
    htf = higher_map.get(tf)
    if not htf:
        return None, None
    now = time.monotonic()
    ck = (symbol, htf)
    cached = _MTF_TREND_CACHE.get(ck)
    if cached and (now - cached[0]) < 30.0:
        return htf, cached[1]
    try:
        cds = get_candles(symbol, htf, limit=120, ttl=15.0)
        closes = [c["c"] for c in cds]
        ser = {n: ema_series(closes, n) for n in EMA_LIST}
        tr = trend_read(cds, ser)
        _MTF_TREND_CACHE[ck] = (now, tr)
        return htf, tr
    except Exception:
        return htf, None


def calc_confluence(s, sym, tf, side, ema_n, cfg=None):
    """EMA 터치 신호의 5대 합류(Confluence) + 엘리어트 파동 적합성을 점검해 점수와 태그 리스트를 반환"""
    up = (side == "long")
    reasons = []
    score = 0

    full_n, _ = calc_dynamic_window(s["candles"], cfg)
    fib = calc_fib_info(s["candles"], full_n)
    ew_aligned = True
    if fib:
        if fib["retracing"] and fib["in_zone"] and ((up and fib["mode"] == "up") or (not up and fib["mode"] == "down")):
            score += 1
            reasons.append("골든존(%s)" % fib.get("zone_label", "0.382~0.618"))
        elif fib.get("ew_wave") in ("W2", "W4", "TRIANGLE") and ((up and fib["mode"] == "up") or (not up and fib["mode"] == "down")):
            score += 1
            reasons.append(fib.get("ew_tag", "EW파동"))
        if fib.get("ew_wave") in ("END_DIAG", "DEEP_ABC") and ((up and fib["mode"] == "up") or (not up and fib["mode"] == "down")):
            ew_aligned = False

    cds = s["candles"]
    prev_v = cds[-2].get("v", 0.0) if len(cds) >= 2 else 0.0
    closed_vols = [c.get("v", 0.0) for c in cds[max(0, len(cds) - 21):-1]]
    avg_v = sum(closed_vols) / len(closed_vols) if closed_vols else 1.0
    best_v_ratio = max(s.get("vol_ratio", 0.0), prev_v / avg_v if avg_v > 0 else 0.0)
    if best_v_ratio >= 1.15:
        score += 1
        reasons.append("거래량(%.1fx)" % best_v_ratio)

    rsi = s.get("rsi", 50.0)
    if 32.0 <= rsi <= 68.0:
        score += 1
        reasons.append("RSI(%.0f)" % rsi)
    elif (up and rsi < 32.0) or (not up and rsi > 68.0):
        score += 1
        reasons.append("RSI반전(%.0f)" % rsi)

    poc = calc_poc_info(cds, full_n)
    if poc:
        p = s["price"]
        if (up and p >= poc["low"] * 0.998) or (not up and p <= poc["high"] * 1.002):
            score += 1
            reasons.append("POC지지" if up else "POC저항")

    htf, htr = get_mtf_trend(sym, tf)
    mtf_aligned = True
    if htr:
        if up and htr["score"] >= 1:
            score += 1
            reasons.append("%s상승동조" % htf.upper())
        elif not up and htr["score"] <= -1:
            score += 1
            reasons.append("%s하락동조" % htf.upper())
        elif (up and htr["score"] <= -3) or (not up and htr["score"] >= 3):
            mtf_aligned = False

    return {
        "score": score,
        "reasons": reasons,
        "mtf_aligned": mtf_aligned,
        "ew_aligned": ew_aligned,
        "htf": htf,
        "htr": htr,
        "fib": fib,
        "poc": poc,
        "full_n": full_n,
    }


# ---------------- 대형 고해상도 차트 ----------------
def png_bytes(w, h, pix):
    raw = bytearray()
    row_bytes = w * 3
    for y in range(h):
        raw.append(0)
        raw.extend(pix[y * row_bytes:(y + 1) * row_bytes])

    def chunk(t, d):
        return (struct.pack(">I", len(d)) + t + d +
                struct.pack(">I", zlib.crc32(t + d) & 0xffffffff))
    return (b"\x89PNG\r\n\x1a\n" +
            chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0)) +
            chunk(b"IDAT", zlib.compress(bytes(raw), 6)) +
            chunk(b"IEND", b""))


def draw_chart(candles, ser, hi=None, N=60, K=3, show_fib=True, tag=None, show_vol=True, chart_tf=None):
    """K=3 기준 1680x840 대형 고해상도 차트 (유동적 봉 개수 N 지원: 15봉 초확대 ~ 150봉 큰그림까지 선명하게 렌더링)"""
    W, H = (560 * K if show_fib else 480 * K), 280 * K
    BG, GRID = (18, 23, 28), (38, 46, 54)
    GREEN, RED, WHITE = (38, 166, 154), (239, 83, 80), (220, 225, 230)
    VOL_GREEN, VOL_RED = (28, 115, 107), (165, 58, 58)
    VOL_MA_COL = (255, 213, 79)
    EMA_COL = {7: (255, 193, 7), 25: (206, 92, 230), 99: (66, 165, 245)}
    FIB_382_COL = (0, 229, 255)
    FIB_618_COL = (255, 150, 0)
    FIB_LIMIT_COL = (255, 99, 132)
    FIB_EXT_COL = (76, 235, 145)
    FIB_START_COL = (175, 185, 200)
    FIB_TREND_COL = (240, 215, 95)
    POC_COL = (186, 104, 200)
    POC_BG = (34, 27, 46)
    ZONE_BG = (30, 44, 58)
    LABEL_BG = (26, 33, 41)

    pix = bytearray(bytes(BG) * (W * H))
    row_stride = W * 3

    def put(x, y, c):
        if 0 <= x < W and 0 <= y < H:
            i = y * row_stride + x * 3
            pix[i], pix[i + 1], pix[i + 2] = c

    def rect(x1, y1, x2, y2, c):
        x1, x2 = max(0, int(x1)), min(W - 1, int(x2))
        y1, y2 = max(0, int(y1)), min(H - 1, int(y2))
        if x1 > x2 or y1 > y2:
            return
        span = x2 - x1 + 1
        row_chunk = bytes(c) * span
        start_offset = x1 * 3
        end_offset = (x2 + 1) * 3
        for y in range(y1, y2 + 1):
            base = y * row_stride
            pix[base + start_offset:base + end_offset] = row_chunk

    def line(x0, y0, x1, y1, c, th=1):
        x0, y0, x1, y1 = int(x0), int(y0), int(x1), int(y1)
        if y0 == y1:
            half = th // 2
            rect(min(x0, x1), y0 - half, max(x0, x1), y0 - half + max(1, th) - 1, c)
            return
        if x0 == x1:
            half = th // 2
            rect(x0 - half, min(y0, y1), x0 - half + max(1, th) - 1, max(y0, y1), c)
            return
        dx, dy = abs(x1 - x0), -abs(y1 - y0)
        sx, sy = (1 if x0 < x1 else -1), (1 if y0 < y1 else -1)
        err = dx + dy
        half = th // 2
        while True:
            if th <= 1:
                put(x0, y0, c)
            else:
                for oy in range(y0 - half, y0 - half + th):
                    if 0 <= oy < H:
                        for ox in range(x0 - half, x0 - half + th):
                            if 0 <= ox < W:
                                idx = oy * row_stride + ox * 3
                                pix[idx], pix[idx + 1], pix[idx + 2] = c
            if x0 == x1 and y0 == y1:
                break
            e2 = 2 * err
            if e2 >= dy:
                err += dy
                x0 += sx
            if e2 <= dx:
                err += dx
                y0 += sy

    def dashed_line(x0, y0, x1, y1, c, dash=5 * K, gap=3 * K, th=1):
        dist = math.hypot(x1 - x0, y1 - y0)
        if dist == 0:
            return
        dx, dy = (x1 - x0) / dist, (y1 - y0) / dist
        pos = 0.0
        while pos < dist:
            end_pos = min(pos + dash, dist)
            line(int(x0 + dx * pos), int(y0 + dy * pos),
                 int(x0 + dx * end_pos), int(y0 + dy * end_pos), c, th)
            pos += dash + gap

    def dashed_hline(x0, x1, y, c, dash=5 * K, gap=3 * K, th=1):
        x = int(x0)
        x1 = int(x1)
        half = th // 2
        while x < x1:
            rect(x, y - half, min(x + dash, x1), y - half + max(1, th) - 1, c)
            x += dash + gap

    def draw_circle(cx, cy, r, c, th=2):
        for a in range(160):
            ang = a * math.pi / 80
            ca, sa = math.cos(ang), math.sin(ang)
            for dr in range(th):
                put(int(cx + (r + dr) * ca), int(cy + (r + dr) * sa), c)

    def draw_text(x, y, text, c, scale=K, bg_box=True):
        s = str(text).upper()
        tw = len(s) * 6 * scale - scale
        th = 7 * scale
        if bg_box:
            rect(x - 2 * scale, y - 2 * scale, x + tw + 2 * scale, y + th + 2 * scale, LABEL_BG)
        cx = x
        for ch in s:
            pat = FONT_5X7.get(ch, FONT_5X7[" "])
            for ry, row in enumerate(pat):
                for rx, val in enumerate(row):
                    if val == "1":
                        rect(cx + rx * scale, y + ry * scale,
                             cx + (rx + 1) * scale - 1, y + (ry + 1) * scale - 1, c)
            cx += 6 * scale

    cs = candles[-N:]
    off = len(candles) - len(cs)
    lo = min(c["l"] for c in cs)
    top = max(c["h"] for c in cs)

    fib = calc_fib_info(cs, len(cs)) if show_fib else None
    if fib and fib.get("tp1_ext"):
        span0 = top - lo
        t1 = fib["tp1_ext"]
        if lo - span0 * 0.25 <= t1 <= top + span0 * 0.25:
            lo = min(lo, t1)
            top = max(top, t1)

    pad = (top - lo) * 0.13 or top * 0.001
    lo, top = lo - pad, top + pad

    L = 8 * K
    R = W - (136 * K if show_fib else 16 * K)
    T = 20 * K
    has_vol = show_vol and any(c.get("v", 0.0) > 0 for c in cs)
    B = (H - 52 * K) if has_vol else (H - 10 * K)
    VOL_T = B + 6 * K
    VOL_B = H - 8 * K
    bw = (R - L) / float(len(cs))
    wick_th = max(1, K - 1) if len(cs) > 95 else K

    def Y(v):
        return int(B - (v - lo) / (top - lo) * (B - T))

    poc = calc_poc_info(cs, len(cs)) if show_vol else None
    if poc:
        yp_hi = Y(poc["high"])
        yp_lo = Y(poc["low"])
        ya, yb = sorted((yp_hi, yp_lo))
        rect(L, max(T, ya), R, min(B, yb), POC_BG)

    if fib and fib["retracing"]:
        fx0 = int(L + (fib["start_idx"] + 0.5) * bw)
        yg_a = Y(fib["gz_a"])
        yg_b = Y(fib["gz_b"])
        ya, yb = sorted((yg_a, yg_b))
        rect(fx0, max(T, ya), R, min(B, yb), ZONE_BG)

    for k in range(1, 5):
        gy = T + (B - T) * k // 5
        rect(L, gy, R, gy, GRID)

    if poc:
        yp = Y(poc["price"])
        dashed_hline(L, R, yp, POC_COL, dash=4 * K, gap=4 * K, th=max(1, K - 1))

    if fib:
        fx0 = int(L + (fib["start_idx"] + 0.5) * bw)
        fx1 = int(L + (fib["end_idx"] + 0.5) * bw)
        fy0 = Y(fib["start_val"])
        fy1 = Y(fib["end_val"])
        yg_a = Y(fib["gz_a"])
        yg_b = Y(fib["gz_b"])

        dashed_hline(L, R, fy0, FIB_START_COL, dash=3 * K, gap=3 * K, th=max(1, K - 1))
        dashed_hline(L, R, fy1, FIB_START_COL, dash=3 * K, gap=3 * K, th=max(1, K - 1))

        if fib["retracing"]:
            dashed_hline(L, R + 4 * K, yg_a, FIB_382_COL, dash=6 * K, gap=3 * K, th=K)
            dashed_hline(L, R + 4 * K, yg_b, FIB_618_COL, dash=6 * K, gap=3 * K, th=K)
            lim_val = fib["500"] if fib.get("ew_wave") == "W4" else fib["786"]
            if lo <= lim_val <= top:
                dashed_hline(fx0, R, Y(lim_val), FIB_LIMIT_COL, dash=3 * K, gap=4 * K, th=max(1, K - 1))

        if fib.get("tp1_ext") and lo <= fib["tp1_ext"] <= top:
            yt1 = Y(fib["tp1_ext"])
            dashed_hline(fx1, R + 4 * K, yt1, FIB_EXT_COL, dash=6 * K, gap=3 * K, th=K)

        ew_pivs = fib.get("ew_pivots") or []
        if len(ew_pivs) >= 2:
            for pi in range(len(ew_pivs) - 1):
                px0 = int(L + (ew_pivs[pi]["idx"] + 0.5) * bw)
                py0 = Y(ew_pivs[pi]["val"])
                px1 = int(L + (ew_pivs[pi + 1]["idx"] + 0.5) * bw)
                py1 = Y(ew_pivs[pi + 1]["val"])
                dashed_line(px0, py0, px1, py1, FIB_TREND_COL, dash=5 * K, gap=3 * K, th=K)
        else:
            dashed_line(fx0, fy0, fx1, fy1, FIB_TREND_COL, dash=5 * K, gap=3 * K, th=K)

    # ---- 캔들 그리기 ----
    for k, c in enumerate(cs):
        xc = int(L + (k + 0.5) * bw)
        half = max(1, int(bw * 0.33))
        col = GREEN if c["c"] >= c["o"] else RED
        line(xc, Y(c["h"]), xc, Y(c["l"]), col, wick_th)
        y1, y2 = sorted((Y(c["o"]), Y(c["c"])))
        rect(xc - half, y1, xc + half, max(y2, y1 + wick_th), col)

    # ---- 하단 거래량(Volume) 바 + 20봉 거래량 이동평균선(VMA) ----
    if has_vol:
        rect(L, B + 2 * K, R, B + 2 * K, GRID)
        vols_all = [c.get("v", 0.0) for c in candles]
        max_v = max([c.get("v", 0.0) for c in cs] or [1.0]) or 1.0

        def VY(vv):
            return int(VOL_B - min(1.0, vv / max_v) * (VOL_B - VOL_T))

        prev_vpt = None
        for k, c in enumerate(cs):
            xc = int(L + (k + 0.5) * bw)
            half = max(1, int(bw * 0.30))
            vcol = VOL_GREEN if c["c"] >= c["o"] else VOL_RED
            vy = VY(c.get("v", 0.0))
            rect(xc - half, vy, xc + half, VOL_B, vcol)

            idx_all = off + k
            w_slice = vols_all[max(0, idx_all - 19):idx_all + 1]
            vma = sum(w_slice) / len(w_slice) if w_slice else 0.0
            vpt = (xc, VY(vma))
            if prev_vpt:
                line(prev_vpt[0], prev_vpt[1], vpt[0], vpt[1], VOL_MA_COL, max(1, K - 1))
            prev_vpt = vpt
        draw_text(L + 2 * K, VOL_T, "VOL / MA20", VOL_MA_COL, scale=max(1, K - 1), bg_box=True)

    # ---- EMA 선 그리기 ----
    for n, colr in EMA_COL.items():
        if n not in ser:
            continue
        prev = None
        for k in range(len(cs)):
            v = ser[n][off + k]
            if not (lo <= v <= top):
                prev = None
                continue
            pt = (int(L + (k + 0.5) * bw), Y(v))
            if prev:
                line(prev[0], prev[1], pt[0], pt[1], colr, K * 2 if n == hi else K)
            prev = pt

    ly = Y(cs[-1]["c"])
    dashed_hline(L, R + 4 * K, ly, WHITE, dash=3 * K, gap=3 * K, th=K)

    # ---- 피보나치 시작점/끝지점/엘리어트 파동 번호 마커 및 우측 라벨 렌더링 ----
    if fib:
        fx0 = int(L + (fib["start_idx"] + 0.5) * bw)
        fx1 = int(L + (fib["end_idx"] + 0.5) * bw)
        fy0 = Y(fib["start_val"])
        fy1 = Y(fib["end_val"])
        yg_a = Y(fib["gz_a"])
        yg_b = Y(fib["gz_b"])

        draw_circle(fx0, fy0, 5 * K, FIB_TREND_COL, th=K)
        rect(fx0 - 2 * K, fy0 - 2 * K, fx0 + 2 * K, fy0 + 2 * K, FIB_TREND_COL)
        draw_circle(fx1, fy1, 5 * K, WHITE, th=K)
        rect(fx1 - 2 * K, fy1 - 2 * K, fx1 + 2 * K, fy1 + 2 * K, WHITE)

        ew_pivs = fib.get("ew_pivots") or []
        if ew_pivs:
            for pv in ew_pivs:
                px = int(L + (pv["idx"] + 0.5) * bw)
                py = Y(pv["val"])
                is_top = (pv["val"] >= cs[pv["idx"]]["h"] * 0.9999)
                ty_off = py - 15 * K if is_top else py + 7 * K
                lbl_txt = "[%s]" % pv["lbl"]
                draw_text(max(L, min(R - 22 * K, px - 8 * K)), max(T, min(B - 9 * K, ty_off)),
                          lbl_txt, FIB_EXT_COL if pv["lbl"] in ("3", "5", "E") else FIB_TREND_COL, scale=K)
        else:
            s_tag_y = fy0 + 8 * K if fib["mode"] == "up" else fy0 - 15 * K
            e_tag_y = fy1 - 15 * K if fib["mode"] == "up" else fy1 + 8 * K
            draw_text(max(L, min(R - 35 * K, fx0 - 14 * K)), max(T, min(B - 8 * K, s_tag_y)), "START", FIB_TREND_COL, scale=K)
            draw_text(max(L, min(R - 25 * K, fx1 - 10 * K)), max(T, min(B - 8 * K, e_tag_y)), "END", WHITE, scale=K)

        labels = [
            {"y": fy0, "text": "1.0(S) " + fmt_p(fib["start_val"]), "col": FIB_START_COL},
            {"y": fy1, "text": "0.0(E) " + fmt_p(fib["end_val"]), "col": FIB_START_COL},
            {"y": ly,  "text": "NOW " + fmt_p(cs[-1]["c"]), "col": WHITE},
        ]
        if fib["retracing"]:
            if fib.get("ew_wave") == "W4":
                labels.append({"y": yg_a, "text": "0.236 " + fmt_p(fib["236"]), "col": FIB_382_COL})
                labels.append({"y": yg_b, "text": "0.382 " + fmt_p(fib["382"]), "col": FIB_618_COL})
                if lo <= fib["500"] <= top:
                    labels.append({"y": Y(fib["500"]), "text": "0.5(X) " + fmt_p(fib["500"]), "col": FIB_LIMIT_COL})
            else:
                labels.append({"y": yg_a, "text": "0.382 " + fmt_p(fib["382"]), "col": FIB_382_COL})
                labels.append({"y": yg_b, "text": "0.618 " + fmt_p(fib["618"]), "col": FIB_618_COL})
                if lo <= fib["786"] <= top:
                    labels.append({"y": Y(fib["786"]), "text": "0.786 " + fmt_p(fib["786"]), "col": FIB_LIMIT_COL})
        if fib.get("tp1_ext") and lo <= fib["tp1_ext"] <= top:
            labels.append({"y": Y(fib["tp1_ext"]), "text": "TGT " + fmt_p(fib["tp1_ext"]), "col": FIB_EXT_COL})
        if poc:
            labels.append({"y": Y(poc["price"]), "text": "POC " + fmt_p(poc["price"]), "col": POC_COL})
        labels.sort(key=lambda item: item["y"])
        min_gap = 11 * K
        for i in range(1, len(labels)):
            if labels[i]["y"] - labels[i - 1]["y"] < min_gap:
                labels[i]["y"] = labels[i - 1]["y"] + min_gap

        for lb in labels:
            ty = max(T, min(B - 8 * K, lb["y"] - 3 * K))
            draw_text(R + 6 * K, ty, lb["text"], lb["col"], scale=K, bg_box=True)

    if hi in ser:
        cx, cy = int(L + (len(cs) - 0.5) * bw), Y(ser[hi][-1])
        draw_circle(cx, cy, 9 * K, WHITE, th=K + 1)

    # 상단 범례 바 (EMA + 엘리어트 파동 태그 + 표시 봉 개수 N + RSI)
    lx = 8 * K
    for n in EMA_LIST:
        rect(lx, 5 * K, lx + 8 * K, 11 * K, EMA_COL[n])
        lg = "EMA%d" % n
        if n in ser:
            lg += " " + fmt_p(ser[n][-1])
        draw_text(lx + 10 * K, 5 * K, lg, EMA_COL[n], scale=K, bg_box=False)
        lx += 10 * K + len(lg) * 6 * K + 8 * K
    if fib:
        fg_txt = "%s(%dB)" % (fib.get("ew_tag", "FIB"), len(cs))
        draw_text(lx + 2 * K, 5 * K, fg_txt, FIB_382_COL, scale=K, bg_box=False)
        lx += len(fg_txt) * 6 * K + 8 * K
    rsis = rsi_series([c["c"] for c in candles], 14)
    if rsis:
        rsi_txt = "RSI %.0f" % rsis[-1]
        draw_text(lx + 2 * K, 5 * K, rsi_txt, VOL_MA_COL, scale=K, bg_box=False)
        lx += len(rsi_txt) * 6 * K + 8 * K
    if tag:
        draw_text(lx + 2 * K, 5 * K, tag, WHITE, scale=K, bg_box=False)

    # 우측 하단 시간봉 + 캔들 수 배지 (예: 4H 96B)
    if chart_tf in ALLOWED_TF:
        tf_str = "%s %dB" % (chart_tf.upper(), len(cs))
        sc = K + 1
        tw = len(tf_str) * 6 * sc - sc
        th = 7 * sc
        bx2 = W - 8 * K
        by2 = H - 6 * K
        bx1 = bx2 - tw - 8 * K
        by1 = by2 - th - 6 * K
        rect(bx1 - K, by1 - K, bx2 + K, by2 + K, WHITE)
        rect(bx1, by1, bx2, by2, LABEL_BG)
        draw_text(bx1 + 4 * K, by1 + 3 * K, tf_str, WHITE, scale=sc, bg_box=False)

    return png_bytes(W, H, pix)


# ---------------- 두 번째 텔레그램 봇: 자동 가상매매 ----------------
PAPER_FILE = os.path.expanduser("~/paper_config.json")
PAPER_DEFAULTS = {
    "on": True, "token": "", "chat_id": "", "offset": 0,
    "init_bud": 300.0, "bal": 300.0, "lev": 7, "alloc": 0.2,
    "rr": 2.0, "pos": {}, "hist": [], "seen": [],
    "dyn_sl_on": True,
    "partial_tp_on": True,
    "mtf_protect": True,
    "fee_rate": 0.0004,
    "total_fees": 0.0,
}
PAPER_ALLOC = {"BTCUSDT": 0.5, "ETHUSDT": 0.5}
PAPER_INLINE_MARKUP = {"inline_keyboard": [
    [{"text": "📊 가상매매 현황", "callback_data": "p:status"},
     {"text": "📈 성과 통계", "callback_data": "p:stats"},
     {"text": "📜 거래 내역", "callback_data": "p:hist"}],
    [{"text": "🧹 전량 가상청산", "callback_data": "p:closeall"},
     {"text": "♻️ 잔고 초기화", "callback_data": "p:reset"}],
]}


def load_paper():
    d = copy.deepcopy(PAPER_DEFAULTS)
    try:
        with open(PAPER_FILE, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if isinstance(raw, dict):
            d.update(raw)
    except FileNotFoundError:
        try:
            save_paper(d)
        except Exception as e:
            print("가상매매 설정 파일 생성 실패:", e)
    except Exception as e:
        print("가상매매 설정 읽기 실패:", e)
    d["token"] = os.environ.get("PAPER_TELEGRAM_TOKEN", d.get("token", ""))
    d.setdefault("pos", {})
    d.setdefault("hist", [])
    d.setdefault("seen", [])
    d.setdefault("dyn_sl_on", True)
    d.setdefault("partial_tp_on", True)
    d.setdefault("mtf_protect", True)
    d.setdefault("fee_rate", 0.0004)
    d.setdefault("total_fees", 0.0)
    if d.get("cfg_v", 0) < 2:
        d["cfg_v"] = 2
        d["lev"] = 7
        d["init_bud"] = 300.0
        d["bal"] = 300.0
        d["pos"] = {}
        try:
            save_paper(d)
        except Exception as e:
            print("가상매매 설정 저장 실패:", e)
    alloc_vals = list(PAPER_ALLOC.values())
    if alloc_vals:
        d["alloc"] = max(alloc_vals)
    return d


def save_paper(p):
    q = copy.deepcopy(p)
    if os.environ.get("PAPER_TELEGRAM_TOKEN"):
        try:
            with open(PAPER_FILE, "r", encoding="utf-8") as f:
                old = json.load(f)
            q["token"] = old.get("token", "")
        except Exception:
            q["token"] = ""
    tmp = PAPER_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(q, f, ensure_ascii=False, indent=2)
    os.replace(tmp, PAPER_FILE)


def paper_tg(p, method, timeout=8, **kw):
    token = p.get("token", "")
    if not token:
        return None
    return HTTP.post("https://api.telegram.org/bot%s/%s" % (token, method), timeout=timeout, **kw)


def send_paper_msg(text, p=None, keyboard=False):
    p = p or load_paper()
    if not p.get("token") or not p.get("chat_id"):
        return
    data = {"chat_id": p["chat_id"], "text": str(text)[:4000]}
    if keyboard:
        data["reply_markup"] = json.dumps(PAPER_INLINE_MARKUP, ensure_ascii=False)
    try:
        r = paper_tg(p, "sendMessage", data=data)
        if r is not None:
            r.raise_for_status()
    except Exception as e:
        print("가상매매 봇 전송 실패:", e)


def paper_status_text(p):
    initial = float(p.get("init_bud", 300.0))
    balance = float(p.get("bal", initial))
    realized = balance - initial
    fees = float(p.get("total_fees", 0.0))
    lines = ["📊 자동 가상매매 현황 (실제 주문 없음)",
             "잔고: %.2f USDT | 실현손익: %+.2f USDT (수수료 -%.2f USDT 반영)" % (balance, realized, fees),
             "레버리지: %sx | 증거금 배분: %.0f%% | 기본 손익비: 1:%.1f" %
             (p.get("lev", 7), float(p.get("alloc", .5))*100, p.get("rr", 2.0)),
             "엔진: 엘리어트 무효화 SL & 확장 TP | 1R반익절·본절스탑 | MTF위계보호"]
    positions = p.get("pos", {})
    if not positions:
        lines.append("\n열린 포지션 없음")
    else:
        lines.append("\n열린 포지션:")
        for sym, x in positions.items():
            side = "롱" if x.get("side") == "long" else "숏"
            be_tag = " [1R반익절·본절스탑중]" if x.get("tp1_done") else ""
            ew_tag = (" [%s]" % x["ew_tag"]) if x.get("ew_tag") else ""
            lines.append("%s %s (%s E%s)%s%s 진입 %s | 현재가 %s | SL %s | TP %s | 미실현 %+.2f USDT" %
                (sym, side, str(x.get("tf", "")).upper(), x.get("ema", "?"), ew_tag, be_tag,
                 fmt_p(x.get("entry", 0)), fmt_p(x.get("last", x.get("entry", 0))),
                 fmt_p(x.get("sl", 0)), fmt_p(x.get("tp", 0)), float(x.get("upnl", 0))))
    return "\n".join(lines)


def paper_stats_text(p):
    hist = p.get("hist", [])
    initial = float(p.get("init_bud", 300.0))
    balance = float(p.get("bal", initial))
    if not hist:
        return ("📈 가상매매 성과 통계\n"
                "아직 완료된 거래가 없습니다. 신호가 발생해 포지션이 청산되면 승률과 시간봉·파동별 성적표가 집계됩니다.")
    wins = [x for x in hist if float(x.get("pnl", 0.0)) > 0]
    losses = [x for x in hist if float(x.get("pnl", 0.0)) <= 0]
    total = len(hist)
    win_rate = len(wins) / total * 100.0 if total else 0.0
    gross_win = sum(float(x.get("pnl", 0.0)) for x in wins)
    gross_loss = abs(sum(float(x.get("pnl", 0.0)) for x in losses))
    pf = (gross_win / gross_loss) if gross_loss > 0 else (99.9 if gross_win > 0 else 0.0)
    avg_win = gross_win / len(wins) if wins else 0.0
    avg_loss = -gross_loss / len(losses) if losses else 0.0

    eq = initial
    peak = initial
    max_dd_pct = 0.0
    for x in hist:
        eq += float(x.get("pnl", 0.0))
        if eq > peak:
            peak = eq
        dd = (peak - eq) / peak * 100.0 if peak > 0 else 0.0
        if dd > max_dd_pct:
            max_dd_pct = dd

    by_strat = {}
    for x in hist:
        ew = (" " + x["ew_tag"]) if x.get("ew_tag") else ""
        k = "%s E%s%s" % (str(x.get("tf", "?")).upper(), x.get("ema", "?"), ew)
        st = by_strat.setdefault(k, {"n": 0, "w": 0, "pnl": 0.0})
        st["n"] += 1
        if float(x.get("pnl", 0.0)) > 0:
            st["w"] += 1
        st["pnl"] += float(x.get("pnl", 0.0))

    lines = [
        "📈 가상매매 성과 통계 (최근 %d건)" % total,
        "총 잔고: %.2f USDT (%+.2f%%)" % (balance, (balance - initial) / initial * 100.0 if initial else 0.0),
        "승률: %.1f%% (%d승 %d패)" % (win_rate, len(wins), len(losses)),
        "손익비(Profit Factor): %.2f | 최대낙폭(MDD): -%.2f%%" % (pf, max_dd_pct),
        "평균 익절: %+.2f USDT | 평균 손절: %.2f USDT" % (avg_win, avg_loss),
        "누적 수수료: -%.2f USDT" % float(p.get("total_fees", 0.0)),
        "\n🏆 신호·파동별 성적표:",
    ]
    for k, st in sorted(by_strat.items(), key=lambda item: item[1]["pnl"], reverse=True):
        wr = st["w"] / st["n"] * 100.0 if st["n"] else 0.0
        lines.append("· %s: %d건 | 승률 %.0f%% | %+.2f USDT" % (k, st["n"], wr, st["pnl"]))
    return "\n".join(lines)


def paper_status_image(p):
    try:
        from PIL import Image, ImageDraw, ImageFont
        from io import BytesIO
    except ImportError as e:
        raise RuntimeError("현황 이미지 폰트 렌더링에는 Pillow가 필요합니다: pip install pillow") from e

    positions = list((p.get("pos") or {}).items())
    initial = float(p.get("init_bud", 300.0))
    balance = float(p.get("bal", initial))
    realized = balance - initial
    unrealized = sum(float(x.get("upnl", 0)) for _, x in positions)
    hist = p.get("hist", [])
    wins = sum(1 for h in hist if float(h.get("pnl", 0)) > 0)
    win_rate_str = ("%d%% (%d/%d)" % (round(wins / len(hist) * 100), wins, len(hist))) if hist else "N/A"

    SCALE = 0.82
    W, H = 1000, max(800, 620 + len(positions) * 222)
    BG=(10,15,28); PANEL=(19,28,46); WHITE=(238,244,255); MUTED=(145,160,183)
    GREEN=(42,220,145); RED=(255,91,111); BLUE=(81,153,255); LINE=(43,58,82)
    im = Image.new("RGB", (round(W*SCALE), round(H*SCALE)), BG)
    d = ImageDraw.Draw(im)
    regular_paths = ["/system/fonts/Roboto-Regular.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf", "/usr/share/fonts/truetype/freefont/FreeSans.ttf"]
    bold_paths = ["/system/fonts/Roboto-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf", "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf"]
    def font(size, bold=False):
        for path in (bold_paths if bold else regular_paths):
            try: return ImageFont.truetype(path, size)
            except OSError: pass
        return ImageFont.load_default()
    def rect(box, color, radius=0):
        box = tuple(round(v*SCALE) for v in box)
        radius = round(radius*SCALE)
        if radius: d.rounded_rectangle(box, radius=radius, fill=color)
        else: d.rectangle(box, fill=color)
    def txt(x,y,value,color=WHITE,size=24,bold=False):
        d.text((round(x*SCALE),round(y*SCALE)), str(value),
               font=font(max(10, round(size*SCALE)),bold), fill=color)

    rect((0,0,W,9), BLUE)
    txt(42,27,"PAPER TRADING v3.40 (ELLIOTT WAVE)",WHITE,34,True)
    txt(43,76,"EW INVALIDATION SL  /  FIB EXTENSION TP  /  MTF GUARD",MUTED,20)
    rect((42,126,W-42,128),LINE)
    rect((42,153,W-42,355),PANEL,22); rect((42,153,51,355),BLUE)
    txt(72,174,"TOTAL BALANCE",MUTED,21,True)
    txt(72,210,f"{balance:,.2f} USDT",WHITE,54,True)
    txt(72,294,"REALIZED P&L",MUTED,18,True)
    txt(72,321,f"{realized:+,.2f} USDT",GREEN if realized>=0 else RED,26,True)
    rect((510,291,512,339),LINE)
    txt(548,294,"UNREALIZED P&L",MUTED,18,True)
    txt(548,321,f"{unrealized:+,.2f} USDT",GREEN if unrealized>=0 else RED,26,True)
    txt(48,385,"LEVERAGE",MUTED,18,True); txt(48,412,f"{p.get('lev',7)}x",WHITE,27,True)
    txt(310,385,"MARGIN ALLOC",MUTED,18,True); txt(310,412,f"{float(p.get('alloc',.5))*100:.0f}%",WHITE,27,True)
    txt(580,385,"WIN RATE",MUTED,18,True); txt(580,412,win_rate_str,WHITE,25,True)
    txt(810,385,"TARGET R:R",MUTED,18,True); txt(810,412,f"1:{float(p.get('rr',2.0)):.1f}",WHITE,27,True)
    txt(44,468,f"OPEN POSITIONS  ({len(positions)})",BLUE,23,True)
    y=510
    if not positions:
        rect((42,y,W-42,y+150),PANEL,20); txt(72,y+47,"NO OPEN POSITIONS",MUTED,28,True)
    else:
        for sym,x in positions[:8]:
            pnl=float(x.get("upnl",0)); is_long=x.get("side")=="long"; accent=GREEN if is_long else RED
            rect((42,y,W-42,y+196),PANEL,20); rect((42,y,50,y+196),accent)
            be_badge = "  [BE LOCKED]" if x.get("tp1_done") else ""
            ew_b = ("  [" + str(x.get("ew_tag")) + "]") if x.get("ew_tag") else ""
            txt(72,y+17,sym + ew_b + be_badge,WHITE,25,True)
            txt(72,y+58,("LONG" if is_long else "SHORT")+"  /  "+str(x.get("tf","")).upper()+" E"+str(x.get("ema","?")),accent,20,True)
            txt(72,y+106,"ENTRY  "+fmt_p(float(x.get("entry",0))),MUTED,17)
            txt(72,y+143,"NOW    "+fmt_p(float(x.get("last",x.get("entry",0)))),WHITE,17,True)
            txt(540,y+17,"UNREALIZED P&L",MUTED,17,True)
            txt(540,y+48,f"{pnl:+,.2f} USDT",GREEN if pnl>=0 else RED,27,True)
            txt(540,y+106,"SL  "+fmt_p(float(x.get("sl",0))),RED,17)
            txt(540,y+143,"TP  "+fmt_p(float(x.get("tp",0))),GREEN,17)
            y+=222
    fy=H-62; rect((42,fy-18,W-42,fy-16),LINE)
    txt(44,fy,f"FEES APPLIED ({float(p.get('fee_rate',0.0004))*100:.2f}%/SIDE)  /  1M HIGH-LOW SL/TP",MUTED,16)
    out=BytesIO(); im.save(out,format="PNG",optimize=True); return out.getvalue()


def paper_entry_image(symbol, tf, side, entry, sl, tp, tp1=None, s_data=None, ew_tag=None, N=48):
    from PIL import Image, ImageDraw, ImageFont
    from io import BytesIO
    if s_data and s_data.get("candles") and s_data.get("ser"):
        cds = s_data["candles"]
        sers = s_data["ser"]
    else:
        cds = get_candles(symbol, tf)
        closes = [c["c"] for c in cds]
        sers = {n: ema_series(closes, n) for n in EMA_LIST}
    cs = cds[-N:]
    off = len(cds) - len(cs)
    W, H = 1200, 700
    L, R, T, B = 24, W - 210, 80, H - 30
    is_long = side == "long"
    lo = min(min(c["l"] for c in cs), sl, tp, entry)
    hi = max(max(c["h"] for c in cs), sl, tp, entry)
    pad = (hi - lo) * 0.08 or hi * 0.001
    lo, hi = lo - pad, hi + pad

    def Y(v):
        return int(B - (v - lo) / (hi - lo) * (B - T))

    def font(size, bold=False):
        names = (["/system/fonts/Roboto-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"] if bold
                 else ["/system/fonts/Roboto-Regular.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"])
        for path in names:
            try:
                return ImageFont.truetype(path, size)
            except OSError:
                pass
        return ImageFont.load_default()

    GREEN, RED, WHITE, CYAN = (38, 166, 154), (239, 83, 80), (230, 235, 240), (0, 229, 255)
    img = Image.new("RGBA", (W, H), (18, 23, 28, 255))
    ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    od = ImageDraw.Draw(ov)
    ye, ys, yt = Y(entry), Y(sl), Y(tp)
    od.rectangle((L, min(ye, yt), R, max(ye, yt)), fill=GREEN + (60,))
    od.rectangle((L, min(ye, ys), R, max(ye, ys)), fill=RED + (60,))
    img = Image.alpha_composite(img, ov)
    d = ImageDraw.Draw(img)
    bw = (R - L) / float(len(cs))
    for k, c in enumerate(cs):
        x = int(L + (k + 0.5) * bw)
        col = GREEN if c["c"] >= c["o"] else RED
        d.line((x, Y(c["h"]), x, Y(c["l"])), fill=col, width=2)
        half = max(2, int(bw * 0.33))
        y1, y2 = sorted((Y(c["o"]), Y(c["c"])))
        d.rectangle((x - half, y1, x + half, max(y2, y1 + 2)), fill=col)
    ecol = {7: (255, 193, 7), 25: (206, 92, 230), 99: (66, 165, 245)}
    for n, col in ecol.items():
        prev = None
        for k in range(len(cs)):
            v = sers[n][off + k]
            if not (lo <= v <= hi):
                prev = None
                continue
            pt = (int(L + (k + 0.5) * bw), Y(v))
            if prev:
                d.line((prev, pt), fill=col, width=2)
            prev = pt

    def dash(y, col):
        x = L
        while x < R + 12:
            d.line((x, y, min(x + 14, R + 12), y), fill=col, width=2)
            x += 22

    def tag(y, text, col):
        d.rectangle((R + 16, y - 16, W - 8, y + 16), fill=col)
        d.text((R + 22, y - 12), text, font=font(20, True), fill=(10, 14, 18))

    dash(ye, WHITE)
    dash(ys, RED)
    dash(yt, GREEN)
    if tp1 is not None:
        yt1 = Y(tp1)
        dash(yt1, CYAN)
        tag(yt1, "TP1 " + fmt_p(tp1), CYAN)
    tag(ye, "IN " + fmt_p(entry), WHITE)
    tag(ys, "SL " + fmt_p(sl), RED)
    tag(yt, "TP2 " + fmt_p(tp), GREEN)
    ex = int(L + (len(cs) - 0.5) * bw)
    d.line((ex, T, ex, B), fill=(120, 130, 140), width=1)
    d.ellipse((ex - 9, ye - 9, ex + 9, ye + 9), outline=WHITE, width=3)
    if is_long:
        arrow = [(ex, ye + 12), (ex - 16, ye + 40), (ex + 16, ye + 40)]
    else:
        arrow = [(ex, ye - 12), (ex - 16, ye - 40), (ex + 16, ye - 40)]
    d.polygon(arrow, fill=GREEN if is_long else RED)
    ew_str = ("  [" + ew_tag + "]") if ew_tag else ""
    head = "%s %s  %s ENTRY%s" % (symbol, tf.upper(), "LONG" if is_long else "SHORT", ew_str)
    d.text((L, 20), head, font=font(34, True), fill=GREEN if is_long else RED)
    d.text((L, 58), datetime.now(KST).strftime("%m/%d %H:%M KST") + "  (EMA 7/25/99 · ELLIOTT SL & FIB EXT TP)",
           font=font(18), fill=(150, 160, 170))
    out = BytesIO()
    img.convert("RGB").save(out, format="PNG")
    return out.getvalue()


def send_paper_photo(png, caption, p=None, keyboard=True):
    p = p or load_paper()
    if not p.get("token") or not p.get("chat_id"):
        print("[가상매매 텔레그램 설정 없음]\n" + str(caption))
        return
    data = {"chat_id": p["chat_id"], "caption": str(caption)[:900]}
    if keyboard:
        data["reply_markup"] = json.dumps(PAPER_INLINE_MARKUP, ensure_ascii=False)
    try:
        r = paper_tg(p, "sendPhoto", data=data,
                      files={"photo": ("paper_status.png", png, "image/png")})
        if r is not None: r.raise_for_status()
    except Exception as e:
        print("가상매매 카드 이미지 전송 실패, 텍스트로 대체:", e)
        send_paper_msg(str(caption) + "\n\n" + paper_status_text(p), p, keyboard)


def send_paper_status(p, intro=None):
    caption = (str(intro).strip() + "\n" if intro else "") + "📊 자동 가상매매 현황 · 실제 주문 없음"
    try:
        png = paper_status_image(p)
        send_paper_photo(png, caption, p, True)
    except Exception as e:
        print("가상매매 현황 이미지 생성 실패, 텍스트 현황으로 대체:", repr(e))
        send_paper_msg(caption + "\n\n" + paper_status_text(p), p, True)


def paper_hist_text(p):
    hist = p.get("hist", [])[-12:]
    if not hist:
        return "📜 아직 완료된 가상 거래가 없습니다."
    lines = ["📜 최근 가상 거래 내역 (최대 12건)"]
    for x in reversed(hist):
        ew = (" " + x["ew_tag"]) if x.get("ew_tag") else ""
        lines.append("%s %s %s(%s%s) | 진입 %s → 청산 %s | 순손익 %+.2f USDT (%s)" %
            (x.get("time", ""), x.get("symbol", ""), "롱" if x.get("side") == "long" else "숏",
             str(x.get("tf", "")).upper(), ew, fmt_p(x.get("entry", 0)), fmt_p(x.get("exit", 0)),
             float(x.get("pnl", 0)), x.get("reason", "청산")))
    return "\n".join(lines)


def paper_close_position(p, symbol, price, reason):
    x = p.get("pos", {}).pop(symbol, None)
    if not x:
        return None
    direction = 1 if x.get("side") == "long" else -1
    qty = float(x["qty"])
    entry = float(x["entry"])
    exit_p = float(price)
    fee_rate = float(p.get("fee_rate", 0.0004))
    exit_fee = exit_p * qty * fee_rate
    gross_pnl = (exit_p - entry) * qty * direction
    net_pnl = gross_pnl - exit_fee
    p["bal"] = float(p.get("bal", p.get("init_bud", 300.0))) + net_pnl
    p["total_fees"] = float(p.get("total_fees", 0.0)) + exit_fee
    total_trade_pnl = net_pnl + float(x.get("realized_part", 0.0))
    record = {
        "symbol": symbol, "side": x["side"], "tf": x.get("tf", ""), "ema": x.get("ema", "?"),
        "ew_tag": x.get("ew_tag", ""),
        "entry": entry, "exit": exit_p, "pnl": total_trade_pnl,
        "reason": reason, "time": datetime.now(KST).strftime("%m/%d %H:%M:%S"),
    }
    p.setdefault("hist", []).append(record)
    p["hist"] = p["hist"][-100:]
    save_paper(p)
    part_note = ("\n(1차 반익절 기확보 %+.2f USDT 포함 총합 %+.2f USDT)" % (float(x.get("realized_part", 0.0)), total_trade_pnl)
                 if x.get("tp1_done") else "")
    ew_str = (" · " + x["ew_tag"]) if x.get("ew_tag") else ""
    send_paper_msg(
        "🏁 가상 포지션 청산: %s %s (%s E%s%s)\n사유: %s\n진입 %s → 청산 %s\n이번 청산 손익: %+.2f USDT%s\n현재 잔고: %.2f USDT" %
        (symbol, "롱" if x["side"] == "long" else "숏", str(x.get("tf", "")).upper(), x.get("ema", "?"), ew_str,
         reason, fmt_p(entry), fmt_p(exit_p), net_pnl, part_note, p["bal"]), p, True)
    return record


def calc_elliott_sl_tp(s_data, tf, side, price, rr, use_ew=True, fib=None):
    min_r = {"5m": 0.0035, "15m": 0.0045, "1h": 0.006, "4h": 0.009, "12h": 0.012, "1d": 0.015, "1w": 0.025}.get(tf, 0.005)
    max_r = {"5m": 0.012,  "15m": 0.018,  "1h": 0.025, "4h": 0.040, "12h": 0.050, "1d": 0.065, "1w": 0.085}.get(tf, 0.025)
    atr_val = float(s_data.get("atr", 0.0)) if s_data else 0.0
    atr_pct = (atr_val * 1.5 / price) if (atr_val > 0 and price > 0) else 0.005
    risk = max(min_r, min(max_r, atr_pct))
    direction = 1 if side == "long" else -1
    sl_label = "ATR동적"

    if use_ew and fib and ((direction == 1 and fib["mode"] == "up") or (direction == -1 and fib["mode"] == "down")):
        ew_sl = fib.get("ew_sl")
        if ew_sl:
            ew_dist_pct = (price - ew_sl) / price if direction == 1 else (ew_sl - price) / price
            if min_r * 0.8 <= ew_dist_pct <= max_r * 1.25:
                risk = ew_dist_pct
                sl_label = "EW무효화(%s)" % fib.get("ew_tag", "FIB")

    sl = price * (1 - risk) if direction == 1 else price * (1 + risk)
    tp1 = price * (1 + risk * 1.0) if direction == 1 else price * (1 - risk * 1.0)
    tp2 = price * (1 + risk * rr) if direction == 1 else price * (1 - risk * rr)

    if use_ew and fib and ((direction == 1 and fib["mode"] == "up") or (direction == -1 and fib["mode"] == "down")):
        t1_ext = fib.get("tp1_ext")
        t2_ext = fib.get("tp2_ext")
        if t1_ext:
            r1_pct = (t1_ext - price) / price if direction == 1 else (price - t1_ext) / price
            if risk * 0.85 <= r1_pct <= risk * 3.5:
                tp1 = t1_ext
        if t2_ext:
            r2_pct = (t2_ext - price) / price if direction == 1 else (price - t2_ext) / price
            if max(risk * 1.4, abs(tp1 - price) / price * 1.15) <= r2_pct <= risk * 6.0:
                tp2 = t2_ext
                sl_label += "+확장TP"

    return sl, tp1, tp2, risk, sl_label


def paper_open_position(symbol, tf, side, price, signal_key, ema_n=None, s_data=None, conf=None, cfg=None):
    p = load_paper()
    if not p.get("on", True) or price <= 0:
        return
    if symbol not in PAPER_ALLOC:
        return
    seen = p.setdefault("seen", [])
    if signal_key in seen:
        return

    if (cfg is None or cfg.get("mtf_on", True)) and conf and not conf.get("mtf_aligned", True):
        seen.append(signal_key); p["seen"] = seen[-500:]; save_paper(p)
        print("[가상매매 MTF 필터] %s %s %s 진입 보류: 상위봉(%s) 강한 역추세" % (symbol, tf, side, conf.get("htf")))
        return

    use_ew = True if cfg is None else cfg.get("ew_on", True)
    if use_ew and conf and not conf.get("ew_aligned", True):
        seen.append(signal_key); p["seen"] = seen[-500:]; save_paper(p)
        print("[가상매매 EW 필터] %s %s %s 진입 보류: 다이아고날/0.786초과 경고 구간" % (symbol, tf, side))
        return

    existing = p.get("pos", {}).get(symbol)
    if existing and existing.get("side") == side:
        seen.append(signal_key); p["seen"] = seen[-500:]; save_paper(p)
        return

    if existing:
        ex_tf = existing.get("tf", "15m")
        if p.get("mtf_protect", True) and TF_RANK.get(tf, 0) < TF_RANK.get(ex_tf, 0):
            seen.append(signal_key); p["seen"] = seen[-500:]; save_paper(p)
            print("[가상매매 위계 보호] %s 기존 %s 포지션 유지 (%s 반대 신호 무시)" % (symbol, ex_tf, tf))
            return
        paper_close_position(p, symbol, price, "반대 신호(%s E%s)" % (tf.upper(), ema_n or "?"))
        p = load_paper()

    balance = float(p.get("bal", 300.0))
    margin = max(0.0, balance * float(PAPER_ALLOC[symbol]))
    lev = max(1.0, float(p.get("lev", 7)))
    notional = margin * lev
    if notional <= 0:
        return

    fib = conf.get("fib") if conf else (calc_fib_info(s_data["candles"], FULL_N) if s_data else None)
    rr = float(p.get("rr", 2.0))
    if p.get("dyn_sl_on", True):
        sl, tp1, tp, risk, sl_label = calc_elliott_sl_tp(s_data, tf, side, price, rr, use_ew=use_ew, fib=fib)
    else:
        risk = 0.005
        direction = 1 if side == "long" else -1
        sl = price * (1 - risk) if direction == 1 else price * (1 + risk)
        tp1 = price * (1 + risk) if direction == 1 else price * (1 - risk)
        tp = price * (1 + risk * rr) if direction == 1 else price * (1 - risk * rr)
        sl_label = "고정(0.5%)"

    qty = notional / price
    fee_rate = float(p.get("fee_rate", 0.0004))
    entry_fee = notional * fee_rate
    p["bal"] = balance - entry_fee
    p["total_fees"] = float(p.get("total_fees", 0.0)) + entry_fee

    ew_tag = fib.get("ew_tag", "FIB") if fib else ""
    now_ms = int(time.time() * 1000)
    pos = {
        "symbol": symbol, "tf": tf, "ema": ema_n or "?", "ew_tag": ew_tag, "side": side,
        "entry": float(price), "last": float(price),
        "qty": qty, "init_qty": qty, "margin": margin,
        "sl": sl, "tp1": tp1, "tp": tp, "risk_pct": risk * 100.0,
        "tp1_done": False, "realized_part": -entry_fee,
        "upnl": 0.0, "time": datetime.now(KST).strftime("%m/%d %H:%M:%S"),
        "check_from": (now_ms // 60000) * 60000,
    }
    p.setdefault("pos", {})[symbol] = pos
    seen.append(signal_key); p["seen"] = seen[-500:]
    save_paper(p)

    ew_line = ("\n파동 판별: %s" % fib["ew_label"]) if fib and fib.get("ew_label") else ""
    conf_line = ""
    if conf and conf.get("reasons"):
        conf_line = "\n합류(%d/5): %s" % (conf["score"], " · ".join(conf["reasons"]))
    text = (
        "🧪 자동 가상매매 진입\n%s %s (%s EMA%s)%s%s\n"
        "진입가: %s\n가상수량: %.6f (명목 %.2f USDT)\n"
        "증거금: %.2f USDT · 레버리지 %sx\n"
        "손절(SL, -%.2f%% · %s): %s\n"
        "1차 반익절(TP1): %s\n"
        "최종 익절(TP2): %s\n"
        "현재 잔고: %.2f USDT (진입수수료 -%.2f 반영)"
        % (symbol, "롱" if side == "long" else "숏", tf.upper(), ema_n or "?", ew_line, conf_line,
           fmt_p(price), qty, notional, margin, p.get("lev", 7),
           risk * 100.0, sl_label, fmt_p(sl), fmt_p(tp1), fmt_p(tp), p["bal"], entry_fee)
    )
    try:
        png = paper_entry_image(symbol, tf, side, float(price), sl, tp, tp1=tp1, s_data=s_data, ew_tag=ew_tag)
        send_paper_photo(png, text, p, True)
    except Exception as e:
        print("진입 차트 생성 실패, 글로 대체:", e)
        send_paper_msg(text, p, True)


def update_paper_positions():
    p = load_paper()
    if not p.get("pos"):
        return
    now_ms = int(time.time() * 1000)
    cur_min = (now_ms // 60000) * 60000
    for symbol in list(p["pos"].keys()):
        try:
            p = load_paper()
            x = p.get("pos", {}).get(symbol)
            if not x:
                continue
            start_ms = int(x.get("check_from", cur_min))
            limit = int(min(60, max(3, (now_ms - start_ms) // 60000 + 2)))
            candles = get_candles(symbol, "1m", limit=limit, ttl=2.0)
            if not candles:
                continue
            price = float(candles[-1]["c"])
            part = [c for c in candles if c["t"] >= start_ms] or [candles[-1]]
            hi = max([price] + [float(c["h"]) for c in part])
            lo = min([price] + [float(c["l"]) for c in part])

            x["last"] = price
            x["check_from"] = cur_min
            direction = 1 if x.get("side") == "long" else -1
            entry = float(x["entry"])
            sl = float(x["sl"])
            tp = float(x["tp"])
            tp1 = float(x.get("tp1", tp))

            sl_hit = (lo <= sl) if direction == 1 else (hi >= sl)
            if sl_hit:
                reason = "본절 스탑(BE)" if x.get("tp1_done") else "손절(SL)"
                paper_close_position(p, symbol, sl, reason)
                continue

            tp_hit = (hi >= tp) if direction == 1 else (lo <= tp)
            if tp_hit:
                paper_close_position(p, symbol, tp, "최종 익절(TP2)")
                continue

            if p.get("partial_tp_on", True) and not x.get("tp1_done", False):
                tp1_hit = (hi >= tp1) if direction == 1 else (lo <= tp1)
                if tp1_hit:
                    half_qty = float(x["qty"]) * 0.5
                    fee_rate = float(p.get("fee_rate", 0.0004))
                    part_fee = tp1 * half_qty * fee_rate
                    part_pnl = (tp1 - entry) * half_qty * direction - part_fee
                    x["qty"] = float(x["qty"]) - half_qty
                    x["margin"] = float(x.get("margin", 0.0)) * 0.5
                    x["tp1_done"] = True
                    x["realized_part"] = float(x.get("realized_part", 0.0)) + part_pnl
                    be_buf = 0.0010
                    x["sl"] = entry * (1 + be_buf) if direction == 1 else entry * (1 - be_buf)
                    p["bal"] = float(p.get("bal", 300.0)) + part_pnl
                    p["total_fees"] = float(p.get("total_fees", 0.0)) + part_fee
                    x["upnl"] = (price - entry) * float(x["qty"]) * direction
                    save_paper(p)
                    send_paper_msg(
                        "🎯 1차 목표가(TP1) 반익절 & 본절 스탑 완료: %s %s\n"
                        "1차 목표가(%s) 도달로 물량 50%% 익절 (%+.2f USDT 확정)\n"
                        "남은 50%%의 손절가(SL)를 본절가(%s)로 이동했습니다.\n"
                        "현재 잔고: %.2f USDT"
                        % (symbol, "롱" if direction == 1 else "숏", fmt_p(tp1),
                           part_pnl, fmt_p(x["sl"]), p["bal"]), p, True)
                    continue

            x["upnl"] = (price - entry) * float(x["qty"]) * direction
            save_paper(p)
        except Exception as e:
            print("가상 포지션 가격 확인 실패(%s): %s" % (symbol, e))


def handle_paper_callback(cq, p):
    try:
        paper_tg(p, "answerCallbackQuery", data={"callback_query_id": cq["id"]})
    except Exception:
        pass
    action = (cq.get("data") or "").partition(":")[2]
    if action == "status":
        try:
            send_paper_status(p)
        except Exception as e:
            print("가상매매 현황 버튼 처리 실패:", repr(e))
            send_paper_msg("⚠️ 현황 조회 중 오류가 발생했습니다.\n" + paper_status_text(p), p, True)
    elif action == "stats":
        send_paper_msg(paper_stats_text(p), p, True)
    elif action == "hist":
        send_paper_msg(paper_hist_text(p), p, True)
    elif action == "closeall":
        for symbol, x in list(p.get("pos", {}).items()):
            paper_close_position(p, symbol, float(x.get("last", x.get("entry", 0))), "수동 전량청산")
        p = load_paper()
        send_paper_status(p, "전량 가상청산 완료")
    elif action == "reset":
        p["pos"] = {}
        p["hist"] = []
        p["bal"] = float(p.get("init_bud", 300.0))
        p["total_fees"] = 0.0
        p["seen"] = []
        save_paper(p)
        send_paper_status(p, "가상매매 잔고와 내역을 초기화했습니다")


def handle_paper_updates():
    p = load_paper()
    if not p.get("token"):
        return
    try:
        r = paper_tg(p, "getUpdates", timeout=4,
            params={"offset": int(p.get("offset", 0)), "timeout": 0,
                     "allowed_updates": json.dumps(["message", "callback_query"])})
        r.raise_for_status()
        updates = r.json().get("result", [])
    except Exception as e:
        print("두 번째 봇 업데이트 확인 실패:", e)
        return
    for u in updates:
        p["offset"] = int(u["update_id"]) + 1
        try:
            save_paper(p)
        except Exception as e:
            print("가상매매 offset 저장 실패:", e)
        try:
            if "callback_query" in u:
                cq = u["callback_query"]
                chat = str((cq.get("message") or {}).get("chat", {}).get("id", ""))
                if p.get("chat_id") and chat == str(p["chat_id"]):
                    handle_paper_callback(cq, p)
                else:
                    print("가상매매 버튼 무시: chat_id 불일치 또는 미등록 (받음=%s, 설정=%s)" % (chat, p.get("chat_id", "")))
            else:
                m = u.get("message") or {}
                chat = str((m.get("chat") or {}).get("id", ""))
                text = (m.get("text") or "").strip()
                if text.startswith("/start") and not p.get("chat_id"):
                    p["chat_id"] = chat
                    save_paper(p)
                    send_paper_status(p, "가상매매 전용 채팅방 등록 완료 · 기존 알림봇과 분리된 두 번째 봇")
                elif p.get("chat_id") and chat == str(p.get("chat_id")):
                    cmd = text.split()[0].lower() if text else ""
                    if cmd in ("/status", "/잔고", "/가상", "현황"):
                        send_paper_status(p)
                    elif cmd in ("/stats", "/통계", "/승률", "통계", "승률"):
                        send_paper_msg(paper_stats_text(p), p, True)
                    elif cmd in ("/hist", "/내역", "내역"):
                        send_paper_msg(paper_hist_text(p), p, True)
                    elif cmd in ("/closeall", "/전량청산"):
                        handle_paper_callback({"id": "", "data": "p:closeall"}, p)
                    elif cmd in ("/reset", "/초기화"):
                        handle_paper_callback({"id": "", "data": "p:reset"}, p)
                    elif cmd == "/start":
                        send_paper_status(p)
        except Exception as e:
            print("두 번째 봇 메시지 처리 오류:", e)


# ---------------- 텔레그램 ----------------
def tg(method, timeout=20, **kw):
    token = os.environ.get("TELEGRAM_TOKEN")
    return HTTP.post("https://api.telegram.org/bot%s/%s" % (token, method), timeout=timeout, **kw)


def send_telegram(text, keyboard=True, markup=None):
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not os.environ.get("TELEGRAM_TOKEN") or not chat_id:
        print("[텔레그램 설정 없음]\n" + text)
        return
    data = {"chat_id": chat_id, "text": text}
    if markup is not None:
        data["reply_markup"] = json.dumps(markup)
    elif keyboard:
        data["reply_markup"] = json.dumps(MAIN_INLINE_MARKUP)
    try:
        tg("sendMessage", data=data).raise_for_status()
    except Exception as e:
        print("텔레그램 전송 실패:", e)


def send_photo(png, caption, keyboard=True, chart_tf=None, badge_drawn=False):
    """차트 사진을 전송하고 하단 배율 변경 버튼(120봉/80봉/25봉/15봉/자동봉)도 해당 시간봉으로 연동한다."""
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not os.environ.get("TELEGRAM_TOKEN") or not chat_id:
        print("[텔레그램 설정 없음]\n" + caption)
        return

    photo = png
    if chart_tf in ALLOWED_TF and not badge_drawn:
        try:
            from io import BytesIO
            from PIL import Image, ImageDraw, ImageFont
            image = Image.open(BytesIO(png)).convert("RGB")
            draw = ImageDraw.Draw(image)
            font_path = "/system/fonts/NotoSansCJK-Regular.ttc"
            try:
                font = ImageFont.truetype(font_path, max(18, image.width // 70))
            except Exception:
                font = ImageFont.load_default()
            label = chart_tf.upper()
            bbox = draw.textbbox((0, 0), label, font=font)
            tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
            pad_x, pad_y = max(8, image.width // 180), max(5, image.width // 300)
            margin = max(10, image.width // 120)
            x1 = image.width - tw - 2 * pad_x - margin
            y1 = image.height - th - 2 * pad_y - margin
            draw.rounded_rectangle((x1, y1, image.width - margin, image.height - margin),
                                   radius=max(5, image.width // 180), fill=(26, 33, 41),
                                   outline=(220, 225, 230), width=max(1, image.width // 1000))
            draw.text((x1 + pad_x, y1 + pad_y - bbox[1]), label, font=font, fill=(255, 255, 255))
            out = BytesIO()
            image.save(out, format="PNG")
            photo = out.getvalue()
        except Exception as e:
            print("차트 시간봉 라벨 추가 실패:", e)

    data = {"chat_id": chat_id, "caption": caption[:1000]}
    if keyboard:
        markup = copy.deepcopy(MAIN_INLINE_MARKUP)
        if chart_tf in ALLOWED_TF:
            for row in markup.get("inline_keyboard", []):
                for button in row:
                    cbd = button.get("callback_data", "")
                    if cbd.startswith("c15:"):
                        button["text"] = "🕯15봉(%s)" % chart_tf.upper()
                        button["callback_data"] = "c15:%s" % chart_tf
                    elif cbd.startswith("cb:"):
                        parts = cbd.split(":")
                        bars = parts[2] if len(parts) > 2 else "80"
                        icon = "🔭" if int(bars) >= 100 else ("📊" if int(bars) >= 60 else "🔍")
                        button["text"] = "%s%s봉" % (icon, bars)
                        button["callback_data"] = "cb:%s:%s" % (chart_tf, bars)
                    elif cbd.startswith("cba:"):
                        button["text"] = "🤖자동봉(%s)" % chart_tf.upper()
                        button["callback_data"] = "cba:%s" % chart_tf
        data["reply_markup"] = json.dumps(markup, ensure_ascii=False)
    try:
        tg("sendPhoto", data=data,
           files={"photo": ("chart.png", photo, "image/png")}).raise_for_status()
    except Exception as e:
        print("사진 전송 실패, 글자로 대신 보냄:", e)
        send_telegram(caption, keyboard=keyboard)


def trend_read(candles, ser):
    price = candles[-1]["c"]
    e7, e25, e99 = ser[7][-1], ser[25][-1], ser[99][-1]
    k = min(10, len(candles) - 1)
    slope = (ser[25][-1] / ser[25][-1 - k] - 1) * 100
    sl = 1 if slope > 0.02 else (-1 if slope < -0.02 else 0)
    checks = [1 if price > e7 else -1, 1 if e7 > e25 else -1, 1 if e25 > e99 else -1,
              sl, 1 if price > e99 else -1]
    score = sum(checks)
    if score >= 4:
        label, icon = "강한 상승", "📈"
    elif score >= 2:
        label, icon = "상승 우세", "📈"
    elif score == 1:
        label, icon = "약한 상승", "↗️"
    elif score == 0:
        label, icon = "횡보(방향 불분명)", "↔️"
    elif score == -1:
        label, icon = "약한 하락", "↘️"
    elif score > -4:
        label, icon = "하락 우세", "📉"
    else:
        label, icon = "강한 하락", "📉"
    if e7 > e25 > e99:
        align = "정배열(7>25>99)"
    elif e7 < e25 < e99:
        align = "역배열(7<25<99)"
    else:
        align = "혼조"
    return {"score": score, "label": label, "icon": icon, "align": align, "slope": slope,
            "price": price, "e7": e7, "e25": e25, "e99": e99, "k": k}


def trend_short(candles, ser, show_fib=True, n_bars=FULL_N):
    t = trend_read(candles, ser)
    rsis = rsi_series([c["c"] for c in candles], 14)
    rsi_val = rsis[-1] if rsis else 50.0
    base = "%s 추세: %s (%+d/5) · RSI %.0f" % (t["icon"], t["label"], t["score"], rsi_val)
    if show_fib:
        fib = calc_fib_info(candles, n_bars)
        if fib:
            if fib.get("ew_wave") != "SWING":
                base += "\n" + fib["ew_label"]
            elif fib["retracing"] and fib["in_zone"]:
                base += " · 🎯골든존(%s)" % fib.get("zone_label", "0.382~0.618")
            if fib.get("tp1_ext") and fib["retracing"]:
                base += " · 🎯목표 %s" % fmt_p(fib["tp1_ext"])
    return base


def send_photos(pngs, caption):
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not os.environ.get("TELEGRAM_TOKEN") or not chat_id:
        print("[텔레그램 설정 없음]\n" + caption)
        return
    try:
        media = [{"type": "photo", "media": "attach://p%d" % i} for i in range(len(pngs))]
        media[0]["caption"] = caption[:1000]
        tg("sendMediaGroup", data={"chat_id": chat_id, "media": json.dumps(media)},
           files={"p%d" % i: ("chart%d.png" % i, png, "image/png") for i, png in enumerate(pngs)}
           ).raise_for_status()
    except Exception as e:
        print("사진 묶음 전송 실패:", e)
        send_photo(pngs[0], caption)


def send_chart_pair(s, sym, tf, cfg, head, hi=None):
    """1번째 사진: 큰 그림(파동 크기에 맞춰 65~150봉 유동 확장)
    2번째 사진: 확대 차트(현재 진행 중인 스윙/눌림목 길이에 맞춰 16~42봉 유동 축소)"""
    zoom = cfg.get("zoom_on", True)
    show_fib = cfg.get("fib_on", True)
    show_vol = cfg.get("vol_on", True)
    dyn_on = cfg.get("dyn_bars_on", True)
    full_n, zoom_n = calc_dynamic_window(s["candles"], cfg)
    mode_tag = "유동파동맞춤" if dyn_on else "고정봉"

    cap1 = "%s\n[1번] 큰 그림 (%d봉·%s) · 현재가 %s\n%s" % (
        head, full_n, mode_tag, "{:,.2f}".format(s["price"]),
        trend_short(s["candles"], s["ser"], show_fib, n_bars=full_n))
    png1 = draw_chart(s["candles"], s["ser"], hi, N=full_n, show_fib=show_fib,
                      tag="MACRO %dB" % full_n, show_vol=show_vol, chart_tf=tf)
    send_photo(png1, cap1, keyboard=not zoom, chart_tf=tf, badge_drawn=True)
    if not zoom:
        return
    try:
        zfib = calc_fib_info(s["candles"], zoom_n)
        z_ew = (" · " + zfib["ew_label"]) if zfib and zfib.get("ew_wave") != "SWING" else ""
        cap2 = "🔍 %s %s [2번] 타점 확대 (%d봉·%s) · 현재가 %s%s" % (
            sym, tf.upper(), zoom_n, mode_tag, "{:,.2f}".format(s["price"]), z_ew)
        zpng = draw_chart(s["candles"], s["ser"], hi, N=zoom_n, show_fib=True,
                          tag="ZOOM %dB" % zoom_n, show_vol=show_vol, chart_tf=tf)
        send_photo(zpng, cap2, chart_tf=tf, badge_drawn=True)
    except Exception as ex:
        print("확대 차트 생성 실패:", ex)
        send_telegram("🔍 %s %s 확대 차트를 만들지 못했어요." % (sym, tf.upper()))


def send_chart_custom_bars(sym, tf, n_bars, cfg):
    """사용자가 버튼(120봉/80봉/25봉/15봉)이나 명령어로 지정한 봉 개수(n_bars)로 즉시 차트를 그려 전송한다."""
    n_bars = max(10, min(240, int(n_bars)))
    s = summarize(sym, tf, cfg)
    if not s:
        send_telegram("%s %s 데이터가 부족해요." % (sym, tf.upper()))
        return
    show_fib = cfg.get("fib_on", True)
    show_vol = cfg.get("vol_on", True)
    view_type = "큰그림" if n_bars >= 75 else ("확대분석" if n_bars <= 35 else "표준차트")
    png = draw_chart(s["candles"], s["ser"], N=n_bars, show_fib=show_fib,
                     tag="CUSTOM %dB" % n_bars, show_vol=show_vol, chart_tf=tf)
    caption = "🕯 %s %s · 최근 %d개 봉 (%s) · 현재가 %s\n%s" % (
        sym, tf.upper(), n_bars, view_type, "{:,.2f}".format(s["price"]),
        trend_short(s["candles"], s["ser"], show_fib, n_bars=n_bars))
    send_photo(png, caption, keyboard=True, chart_tf=tf, badge_drawn=True)


def send_chart_15(sym, tf, cfg):
    """선택한 시간봉(tf)의 최근 15개 봉을 분석·표시한다."""
    send_chart_custom_bars(sym, tf, 15, cfg)


def send_chart(sym, tf, cfg, head=None, hi=None):
    s = summarize(sym, tf, cfg)
    if not s:
        send_telegram("%s %s 데이터가 부족해요." % (sym, tf))
        return
    send_chart_pair(s, sym, tf, cfg, head or ("📈 %s %s (선물)" % (sym, tf.upper())), hi)


# ---------------- 5분봉 급변·거래량 급증 감지 ----------------
def check_sudden_moves(cfg):
    if not cfg.get("surge_on", True):
        return
    change_limit = float(cfg.get("surge_change_pct", 0.7))
    volume_mult = float(cfg.get("surge_volume_mult", 2.5))
    for sym in active_symbols(cfg):
        try:
            candles = get_candles(sym, "5m", limit=25)
            if len(candles) < 22:
                continue
            live = candles[-1]
            closed_volumes = [c.get("v", 0.0) for c in candles[-21:-1]]
            avg_volume = sum(closed_volumes) / len(closed_volumes) if closed_volumes else 0
            vol_ratio = live.get("v", 0.0) / avg_volume if avg_volume > 0 else 0
            change = (live["c"] / live["o"] - 1) * 100 if live["o"] else 0
            abs_change = abs(change)
            price_surge = abs_change >= change_limit
            volume_confirmed_move = abs_change >= change_limit * 0.5 and vol_ratio >= volume_mult
            if not (price_surge or volume_confirmed_move):
                continue
            side = "상승" if change > 0 else "하락"
            key = (sym, live["t"], side)
            if key in surge_alerted:
                continue
            surge_alerted[key] = True
            save_alert_state()
            strength = "🚨 거래량 동반 급변" if vol_ratio >= volume_mult else "⚡ 가격 급변"
            candles_for_trend = candles[:-1] + [dict(live)]
            closes = [c["c"] for c in candles_for_trend]
            ser = {n: ema_series(closes, n) for n in EMA_LIST}
            trend = trend_read(candles_for_trend, ser)
            sent = get_futures_sentiment(sym)
            sent_line = ""
            if sent.get("funding") is not None:
                sent_line = "\n펀딩비: %+.4f%%" % sent["funding"]
                if sent.get("oi"):
                    sent_line += " · 미결제약정(OI): {:,.0f}".format(sent["oi"])
                    if abs(sent.get("oi_chg", 0.0)) >= 0.05:
                        sent_line += " (%+.2f%%)" % sent["oi_chg"]
            msg = (
                "%s | %s %s\n"
                "5분봉 시가 대비: %+.2f%% (%s)\n"
                "현재가: %s\n"
                "거래량: 직전 20개 마감봉 평균의 %.2f배\n"
                "%s · EMA 배열 %s (%+d/5)%s\n"
                "※ 진행 중인 봉이라 변동률·거래량은 마감 전 바뀔 수 있어요."
            ) % (strength, sym, side, change, side, "{:,.4f}".format(live["c"]),
                 vol_ratio, trend["label"], trend["align"], trend["score"], sent_line)
            send_telegram(msg)
        except Exception as e:
            print("[%s 5m 급변 감지] 오류: %s" % (sym, e))
    if len(surge_alerted) > 2000:
        for old_k in list(surge_alerted.keys())[:1000]:
            surge_alerted.pop(old_k, None)


# ---------------- 알림 ----------------
def check_closed(s, sym, tf, cfg):
    """1시간/4시간/12시간/일봉이 마감되면 마감 브리핑을 유동 큰그림 차트 사진과 함께 보낸다."""
    if tf not in ("1h", "4h", "12h", "1d") or len(s["candles"]) < 31:
        return
    closed_candles = s["candles"][:-1]
    closed = closed_candles[-1]
    close_key = (sym, tf, closed["t"])
    stream_key = (sym, tf)
    if stream_key not in closed_candle_seen:
        closed_candle_seen.add(stream_key)
        mark_alerted(("closed",) + close_key)
        return
    if ("closed",) + close_key in alerted:
        return
    mark_alerted(("closed",) + close_key)
    close_price = closed["c"]
    prev_price = closed_candles[-2]["c"]
    change = (close_price / prev_price - 1) * 100 if prev_price else 0
    closed_ser = {n: values[:-1] for n, values in s["ser"].items()}
    trend = trend_read(closed_candles, closed_ser)
    rsis = rsi_series([c["c"] for c in closed_candles], 14)
    rsi_val = rsis[-1] if rsis else 50.0
    full_n, _ = calc_dynamic_window(closed_candles, cfg)
    fib = calc_fib_info(closed_candles, full_n)
    ew_line = ("\n" + fib["ew_label"]) if fib and fib.get("ew_wave") != "SWING" else ""
    candle_icon = "🟢" if close_price >= closed["o"] else "🔴"
    secs = {"1h": 3600000, "4h": 14400000, "12h": 43200000, "1d": 86400000}[tf]
    close_time = datetime.fromtimestamp((closed["t"] + secs) / 1000, KST).strftime("%m/%d %H:%M")
    brief = (
        "🕯️ %s 마감 브리핑 (%d봉) | %s %s\n"
        "마감: %s KST\n"
        "%s 종가: %s (%+.2f%%) · RSI %.0f\n"
        "%s 추세 (%+d/5) · EMA 배열: %s%s\n"
        "EMA7 %s / EMA25 %s / EMA99 %s\n"
        "※ 마감 기준 참고용 요약이며 매매 신호 보장은 없어요."
    ) % (
        TF_LABEL[tf], full_n, sym, tf.upper(), close_time, candle_icon,
        "{:,.2f}".format(close_price), change, rsi_val,
        trend["icon"], trend["score"], trend["align"], ew_line,
        "{:,.2f}".format(trend["e7"]),
        "{:,.2f}".format(trend["e25"]),
        "{:,.2f}".format(trend["e99"])
    )
    try:
        png = draw_chart(closed_candles, closed_ser, N=full_n,
                         show_fib=cfg.get("fib_on", True),
                         show_vol=cfg.get("vol_on", True),
                         chart_tf=tf)
        send_photo(png, brief, keyboard=True, chart_tf=tf, badge_drawn=True)
    except Exception as ex:
        print("마감 차트 생성 실패:", ex)
        send_telegram(brief)


def check_all(cfg):
    for sym in active_symbols(cfg):
        for tf in active_tfs(cfg):
            try:
                s = summarize(sym, tf, cfg)
            except Exception as e:
                print("[%s %s] 오류: %s" % (sym, tf, e))
                continue
            if not s:
                continue

            check_closed(s, sym, tf, cfg)

            for n, e in s["emas"].items():
                side = e["side"]
                if not side:
                    continue
                up = side == "long"
                rep = (tf == "15m" and n == 7 and cfg["rep_on"]
                       and e.get("touches_prev", 0) >= cfg["rep_touch_min"])
                key = (sym, tf, n, s["t"], side, rep)
                if key in alerted:
                    continue

                conf = calc_confluence(s, sym, tf, side, n, cfg=cfg)
                conf_badge = ""
                if conf["score"] >= 3:
                    conf_badge = "\n🔥 강합류(%d/5): %s" % (conf["score"], " · ".join(conf["reasons"]))
                elif conf["reasons"]:
                    conf_badge = "\n✨ 합류(%d/5): %s" % (conf["score"], " · ".join(conf["reasons"]))

                if rep:
                    title = "🔁🟢 반복 터치 후 다시 반등" if up else "🔁🔴 반복 터치 후 다시 하락"
                    body = ("최근 %d개 15분봉(약 %.1f시간) 동안 EMA7을 %d번 터치했고,\n"
                            "이번에도 %s 중이에요. → %s%s"
                            % (cfg["rep_window"], cfg["rep_window"] * 0.25, e["touches_prev"],
                               "위로 올라가는" if up else "아래로 내려가는",
                               "롱 우세" if up else "숏 우세", conf_badge))
                else:
                    count = e["longs"] if up else e["shorts"]
                    if count < cfg["min_count"]:
                        continue
                    title = "🟢 롱 우세" if up else "🔴 숏 우세"
                    body = ("%s이 EMA%d에 닿고 %s 중이에요.\n최근 %s 같은 신호 %d번째%s"
                            % (TF_LABEL[tf], n, "위로 올라가는" if up else "아래로 내려가는",
                               LOOK_LABEL[tf], count, conf_badge))

                paper_open_position(
                    sym, tf, side, float(s["price"]),
                    "%s|%s|%s|%s|%s|%s" % (sym, tf, n, s["t"], side, int(rep)),
                    ema_n=n, s_data=s, conf=conf, cfg=cfg
                )
                mark_alerted(key)
                head = "%s | %s %s EMA%d\n%s" % (title, sym, tf.upper(), n, body)
                try:
                    send_chart_pair(s, sym, tf, cfg, head, n)
                except Exception as ex:
                    print("차트 생성 실패:", ex)
                    send_telegram(head)


def status_blocks(cfg):
    syms, tfs = active_symbols(cfg), active_tfs(cfg)
    if not syms or not tfs or not active_emas(cfg):
        return ["켜져 있는 종목/봉/EMA가 없어요. ⚙️ 설정에서 켜주세요."]
    now = datetime.now(KST).strftime("%m/%d %H:%M:%S")
    blocks = ["📊 현황 (%s KST, 바이낸스 선물)\n숫자 = 현재가가 EMA보다 위(+)/아래(-) 몇 %%\n🟢🔴 = 지금 터치 후 반등/거절 중" % now]
    for sym in syms:
        head, rows = "", []
        sent = get_futures_sentiment(sym)
        sent_str = ("  [펀딩 %+.4f%%]" % sent["funding"]) if sent.get("funding") is not None else ""
        for tf in tfs:
            try:
                s = summarize(sym, tf, cfg)
            except Exception:
                rows.append("%s 조회 실패" % tf.upper())
                continue
            if not s:
                continue
            head = "{:,.2f}".format(s["price"]) + sent_str
            parts = []
            for n, e in s["emas"].items():
                mark = "🟢" if e["side"] == "long" else ("🔴" if e["side"] == "short" else "")
                parts.append("E%d %+.2f%%%s" % (n, e["diff"], mark))
            parts.append("R%.0f" % s.get("rsi", 50))
            if cfg.get("ew_on", True):
                full_n, _ = calc_dynamic_window(s["candles"], cfg)
                fib = calc_fib_info(s["candles"], full_n)
                if fib and fib.get("ew_tag") and fib["ew_tag"] != "FIB":
                    parts.append(fib["ew_tag"].replace("EW:", ""))
            rows.append("%s  %s" % (tf.upper().ljust(3), " | ".join(parts)))
        blocks.append("%s  %s\n%s" % (sym, head, "\n".join(rows)))
    blocks.append("갱신: 약 %d초마다 · %s" % (POLL_SECONDS, VERSION))
    return blocks


def send_status(cfg):
    send_telegram("조회 중... 잠깐만요", keyboard=False)
    buf = ""
    for b in status_blocks(cfg):
        if len(buf) + len(b) > 3500:
            send_telegram(buf)
            buf = ""
        buf += ("\n\n" if buf else "") + b
    if buf:
        send_telegram(buf)


# ---------------- 설정 화면 (켜기/끄기 버튼) ----------------
def tick(on):
    return "🔔 " if on else "🔕 "


def chunk_rows(btns, n):
    return [btns[i:i + n] for i in range(0, len(btns), n)]


def settings_markup(cfg):
    rows = chunk_rows([{"text": tick(on) + s.replace("USDT", ""), "callback_data": "s:" + s}
                       for s, on in cfg["symbols"].items()], 3)
    rows += chunk_rows([{"text": tick(cfg["tf_on"].get(tf)) + tf.upper(), "callback_data": "t:" + tf}
                        for tf in ALLOWED_TF], 3)
    rows.append([{"text": tick(cfg["ema_on"].get(str(n))) + "EMA%d" % n, "callback_data": "e:%d" % n}
                 for n in EMA_LIST])
    rows.append([{"text": tick(cfg["rep_on"]) + "15분 EMA7 반복터치 알림", "callback_data": "r:1"}])
    rows.append([{"text": tick(cfg.get("surge_on", True)) + "5분 급변·거래량 급증 알림", "callback_data": "g:1"}])
    rows.append([{"text": tick(cfg.get("fib_on", True)) + "엘리어트 파동 & 피보나치 작도", "callback_data": "f:1"}])
    rows.append([{"text": tick(cfg.get("ew_on", True)) + "엘리어트 무효화 SL & 확장 TP 적용", "callback_data": "w:1"}])
    rows.append([{"text": tick(cfg.get("vol_on", True)) + "거래량 바·20MA·POC 매물대 표시", "callback_data": "v:1"}])
    rows.append([{"text": tick(cfg.get("mtf_on", True)) + "가상매매 상위봉(MTF) 역추세 차단", "callback_data": "m:1"}])
    rows.append([{"text": tick(cfg.get("dyn_bars_on", True)) + "유동적 봉 개수 (1번 큰그림 확장·2번 파동맞춤 축소)", "callback_data": "b:1"}])
    rows.append([{"text": tick(cfg.get("zoom_on", True)) + "2번째 확대 차트 사진 함께 전송", "callback_data": "z:1"}])
    rows.append([{"text": "🔙 메인 메뉴 버튼 보기", "callback_data": "act:menu"}])
    return {"inline_keyboard": rows}


def settings_text(cfg):
    dyn_desc = ("자동(큰그림 %d~%d봉 / 확대 %d~%d봉)" % (FULL_MIN_N, FULL_MAX_N, ZOOM_MIN_N, ZOOM_MAX_N)
                if cfg.get("dyn_bars_on", True)
                else "고정(큰그림 %d봉 / 확대 %d봉)" % (int(cfg.get("full_n", FULL_N)), int(cfg.get("zoom_n", ZOOM_N))))
    return (
        "⚙️ 설정 (%s)\n버튼을 눌러 알림과 차트 기능을 켜고(🔔) 끄세요(🔕)\n"
        "· 종목 / 봉 / EMA / 엘리어트·피보나치 / 거래량·POC / 유동적 봉 개수\n\n"
        "글자로 바꾸는 것\n"
        "종목추가 XRP  (또는 XRPUSDT)\n종목삭제 XRP  (또는 XRPUSDT)\n"
        "전체봉 %d  (수동 모드 시 1번 큰그림 봉 개수, 30~200)\n"
        "확대봉 %d  (수동 모드 시 2번 확대차트 봉 개수, 12~80)\n"
        "차트 BTC 4h 120  (원하는 종목·시간봉·봉수로 즉시 차트 호출)\n"
        "횟수 %d | 15분터치 %d | 15분범위 %d\n"
        "급변기준 0.7 | 거래량배수 2.5\n"
        "업데이트주소 https://github.com/hoho1556/alertbot\n"
        "현재 봉 표시 모드: %s\n"
        % (VERSION, int(cfg.get("full_n", FULL_N)), int(cfg.get("zoom_n", ZOOM_N)),
           cfg["min_count"], cfg["rep_touch_min"], cfg["rep_window"], dyn_desc)
    )


def chart_markup():
    return {"inline_keyboard": chunk_rows(
        [{"text": tf.upper(), "callback_data": "ct:" + tf} for tf in ALLOWED_TF], 3)}


def edit_setting(cfg, word, args):
    if word in ("종목추가", "종목삭제"):
        if not args:
            return "예: %s XRPUSDT" % word
        sym = args[0].upper()
        if not sym.endswith("USDT"):
            sym += "USDT"
        if word == "종목추가":
            if len(cfg["symbols"]) >= 12:
                return "종목은 최대 12개까지예요. 하나 삭제해 주세요."
            try:
                get_candles(sym, "1h", limit=2)
            except Exception:
                return "%s 는 바이낸스 선물에서 못 찾았어요" % sym
            cfg["symbols"][sym] = True
        else:
            cfg["symbols"].pop(sym, None)
    elif word in ("전체봉", "확대봉"):
        try:
            v = int(args[0])
        except Exception:
            return "예: 전체봉 100 또는 확대봉 22"
        if word == "전체봉":
            cfg["full_n"] = max(30, min(200, v))
        else:
            cfg["zoom_n"] = max(12, min(80, v))
    elif word in ("횟수", "15분터치", "15분범위"):
        try:
            v = max(1, int(args[0]))
        except Exception:
            return "예: %s 2" % word
        cfg[{"횟수": "min_count", "15분터치": "rep_touch_min", "15분범위": "rep_window"}[word]] = v
    elif word in ("급변기준", "거래량배수"):
        try:
            v = float(args[0])
            if v <= 0:
                raise ValueError()
        except Exception:
            return "예: 급변기준 0.7 또는 거래량배수 2.5"
        cfg["surge_change_pct" if word == "급변기준" else "surge_volume_mult"] = v
    elif word == "업데이트주소":
        if not args or not args[0].startswith("https://"):
            return "예: 업데이트주소 https://github.com/hoho1556/alertbot"
        cfg["update_url"] = args[0]
    save_cfg(cfg)
    return "✅ 저장했어요. ⚙️ 설정을 눌러 확인하세요."


# ---------------- 업데이트 ----------------
def confirm_updates():
    try:
        tg("getUpdates", params={"offset": update_offset[0], "timeout": 0})
    except Exception:
        pass


def fetch_latest_source(url):
    m = re.match(r"https://github\.com/([^/]+)/([^/]+)(?:/(?:blob|tree)/([^/]+)(?:/.*)?)?(?:\?.*)?$", url)
    if not m:
        raw = re.match(r"https://raw\.githubusercontent\.com/([^/]+)/([^/]+)/([^/]+)/.+", url)
        if raw:
            owner, repo, branch = raw.groups()
        else:
            r = HTTP.get(url, timeout=20)
            r.raise_for_status()
            return r.text
    else:
        owner, repo, branch = m.groups()
    repo = repo.removesuffix(".git")
    api_headers = {"Accept": "application/vnd.github+json", "User-Agent": "TradingAlertBot-Updater"}
    api = "https://api.github.com/repos/%s/%s" % (owner, repo)
    info = HTTP.get(api, headers=api_headers, timeout=20)
    info.raise_for_status()
    default_branch = info.json().get("default_branch", "main")
    branch = branch or default_branch

    commits_url = api + "/commits"
    commits = HTTP.get(commits_url, params={"sha": branch, "per_page": 30},
                       headers=api_headers, timeout=20)
    commits.raise_for_status()
    for commit_item in commits.json():
        sha = commit_item.get("sha")
        if not sha:
            continue
        detail = HTTP.get(api + "/commits/" + sha, headers=api_headers, timeout=20)
        detail.raise_for_status()
        files = detail.json().get("files", [])
        py_files = [f for f in files if f.get("filename", "").lower().endswith(".py")
                    and f.get("status") != "removed"]
        py_files = [f for f in py_files if not f.get("filename", "").startswith(".")]
        if not py_files:
            continue
        py_files.sort(key=lambda f: (
            0 if "alert_bot" in f.get("filename", "").lower() else 1,
            0 if f.get("filename", "").lower().endswith(".py") else 1
        ))
        chosen = py_files[0]["filename"]
        raw_url = "https://raw.githubusercontent.com/%s/%s/%s/%s" % (owner, repo, sha, chosen)
        r = HTTP.get(raw_url, headers={"User-Agent": "TradingAlertBot-Updater"}, timeout=20)
        r.raise_for_status()
        return r.text
    raise FileNotFoundError("저장소에서 최근에 수정된 Python 파일을 찾지 못했습니다")


def do_update(cfg):
    url = cfg.get("update_url", "").strip()
    if not url:
        send_telegram("업데이트 주소가 없어요. 먼저 이렇게 보내세요:\n업데이트주소 https://github.com/내아이디/저장소이름")
        return
    try:
        src = fetch_latest_source(url)
        compile(src, "alert_bot_live.py", "exec")
        if "def main" not in src:
            raise ValueError("봇 코드가 아닌 것 같아요")
    except Exception as e:
        send_telegram("업데이트 실패(기존 버전 유지): %s" % e)
        return
    path = os.path.abspath(__file__)
    try:
        with open(path, "r", encoding="utf-8") as f:
            old = f.read()
        with open(path + ".bak", "w", encoding="utf-8") as f:
            f.write(old)
        with open(path, "w", encoding="utf-8") as f:
            f.write(src)
    except Exception as e:
        send_telegram("파일 교체 실패: %s" % e)
        return
    save_alert_state()
    send_telegram("✅ 새 코드를 받았어요. 다시 시작합니다...")
    confirm_updates()
    os.execv(sys.executable, [sys.executable] + sys.argv)


# ---------------- 텔레그램 채팅 패치 (함수/변수 단위 교체) ----------------
PATCH_HELP = (
    "🛠 패치 사용법\n"
    "첫 줄에 '패치', 그 아래에 교체할 함수나 변수(예: DEFAULTS = {...}) 전체를 보내세요.\n"
    "· 같은 이름의 기존 함수/변수가 통째로 교체되고, 없으면 새로 추가돼요.\n"
    "· 문법 검사 + 불러오기 검사를 통과해야만 적용되고, 직전 파일은 .bak으로 백업돼요.\n"
    "· 한 메시지는 4096자까지라 큰 함수는 하나씩 나눠 보내세요.\n"
    "· import 가 필요하면 함수 안에 적어주세요. 함수/변수 밖의 줄은 무시돼요.\n"
    "· 적용되면 봇이 자동으로 재시작해요.\n"
    "되돌리기: 패치취소"
)


def _patch_extract_code(raw):
    raw = raw.replace("\r\n", "\n").replace("\r", "\n")
    first, _, rest = raw.partition("\n")
    code = rest if rest.strip() else first[len("패치"):]
    lines = code.splitlines()
    if lines and lines[0].strip().startswith("```"):
        lines = lines[1:]
    if lines and lines[-1].strip().startswith("```"):
        lines = lines[:-1]
    return "\n".join(lines).strip() + "\n" if lines else ""


def _patch_normalize(code):
    for a, b in (("\u201c", '"'), ("\u201d", '"'), ("\u2018", "'"), ("\u2019", "'"),
                 ("\u00a0", " "), ("\u200b", "")):
        code = code.replace(a, b)
    return code


def _patch_name(node):
    import ast
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return node.name
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        return node.targets[0].id
    return None


def _patch_start(node):
    return min([node.lineno] + [d.lineno for d in getattr(node, "decorator_list", [])]) - 1


def _patch_targets(code):
    import ast
    tree = ast.parse(code)
    lines = code.splitlines(True)
    out, ignored = {}, 0
    for node in tree.body:
        name = _patch_name(node)
        if not name:
            ignored += 1
            continue
        seg = "".join(lines[_patch_start(node):node.end_lineno])
        out[name] = seg if seg.endswith("\n") else seg + "\n"
    return out, ignored


def _patch_validate(src):
    import subprocess
    if "def main" not in src:
        return "def main 이 없어요"
    try:
        compile(src, "patched_bot.py", "exec")
    except Exception as e:
        return "문법 오류: %s" % e
    tmp = os.path.abspath(__file__) + ".check.py"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(src)
        chk = ("import importlib.util,sys\n"
               "spec=importlib.util.spec_from_file_location('chk',sys.argv[1])\n"
               "m=importlib.util.module_from_spec(spec)\n"
               "spec.loader.exec_module(m)\n"
               "assert callable(m.main)\n")
        r = subprocess.run([sys.executable, "-c", chk, tmp], capture_output=True, text=True, timeout=30)
        if r.returncode != 0:
            tail = (r.stderr.strip().splitlines() or ["알 수 없는 오류"])[-1]
            return "불러오기 오류: %s" % tail
    except Exception as e:
        return "검사 실패: %s" % e
    finally:
        try:
            os.remove(tmp)
        except Exception:
            pass
    return None


def apply_hot_patch(raw):
    import ast
    code = _patch_extract_code(raw)
    if not code.strip():
        send_telegram(PATCH_HELP)
        return
    code = _patch_normalize(code)
    try:
        targets, ignored = _patch_targets(code)
    except SyntaxError as e:
        lines = code.splitlines()
        bad_line = lines[e.lineno - 1] if e.lineno and 0 < e.lineno <= len(lines) else ""
        detail = "❌ 패치 코드 문법 오류 (%d번째 줄): %s" % (e.lineno or 0, e.msg)
        if bad_line:
            detail += "\n문제 줄: " + bad_line[:180]
        detail += "\n원본은 그대로예요. 함수 전체를 다시 보내주세요."
        send_telegram(detail)
        return
    except Exception as e:
        send_telegram("❌ 패치 코드를 읽지 못했어요: %s" % e)
        return
    if not targets:
        send_telegram("⚠️ 교체할 함수나 변수(def ... / 이름 = ...)를 찾지 못했어요.\n\n" + PATCH_HELP)
        return

    path = os.path.abspath(__file__)
    with open(path, "r", encoding="utf-8") as f:
        orig_src = f.read()
    orig_lines = orig_src.splitlines(True)
    orig_tree = ast.parse(orig_src)

    ops, replaced, guard_start = [], set(), None
    for node in orig_tree.body:
        name = _patch_name(node)
        if name in targets:
            ops.append((_patch_start(node), node.end_lineno, targets[name]))
            replaced.add(name)
        if (guard_start is None and isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
                and isinstance(node.test.left, ast.Name) and node.test.left.id == "__name__"):
            guard_start = _patch_start(node)
    added = [n for n in targets if n not in replaced]
    if added:
        text = "\n\n".join(targets[n] for n in added) + "\n\n"
        at = guard_start if guard_start is not None else len(orig_lines)
        if guard_start is None:
            text = "\n\n" + text
        ops.append((at, at, text))
    for start, end, text in sorted(ops, key=lambda o: o[0], reverse=True):
        orig_lines[start:end] = [text]
    new_src = "".join(orig_lines)

    err = _patch_validate(new_src)
    if err:
        send_telegram("❌ 패치 적용 안 함(원본 유지): %s" % err)
        return
    try:
        with open(path + ".bak", "w", encoding="utf-8") as f:
            f.write(orig_src)
        with open(path, "w", encoding="utf-8") as f:
            f.write(new_src)
    except Exception as e:
        send_telegram("❌ 파일 저장 실패: %s" % e)
        return
    parts = []
    if replaced:
        parts.append("교체: " + ", ".join(sorted(replaced)))
    if added:
        parts.append("추가: " + ", ".join(added))
    if ignored:
        parts.append("무시한 줄: %d개" % ignored)
    save_alert_state()
    send_telegram("✅ 패치 완료 (%s)\n봇을 재시작합니다... 되돌리려면 '패치취소'" % " / ".join(parts), keyboard=False)
    confirm_updates()
    os.execv(sys.executable, [sys.executable] + sys.argv)


def rollback_patch():
    path = os.path.abspath(__file__)
    bak = path + ".bak"
    if not os.path.exists(bak):
        send_telegram("되돌릴 백업(.bak)이 없어요.")
        return
    try:
        with open(bak, "r", encoding="utf-8") as f:
            old_src = f.read()
        with open(path, "r", encoding="utf-8") as f:
            cur_src = f.read()
    except Exception as e:
        send_telegram("❌ 백업 읽기 실패: %s" % e)
        return
    err = _patch_validate(old_src)
    if err:
        send_telegram("❌ 백업 파일에 문제가 있어 되돌리지 않았어요: %s" % err)
        return
    try:
        with open(path + ".prev", "w", encoding="utf-8") as f:
            f.write(cur_src)
        with open(path, "w", encoding="utf-8") as f:
            f.write(old_src)
    except Exception as e:
        send_telegram("❌ 되돌리기 실패: %s" % e)
        return
    save_alert_state()
    send_telegram("↩️ 직전 파일로 되돌렸어요. 봇을 재시작합니다...", keyboard=False)
    confirm_updates()
    os.execv(sys.executable, [sys.executable] + sys.argv)


# ---------------- 가격 목표 알림 (예: "이더리움 2784") ----------------
PRICE_ALERT_FILE = os.path.expanduser("~/price_alerts.json")

KR_COINS = {
    "비트코인": "BTC", "비트": "BTC", "이더리움": "ETH", "이더": "ETH", "리플": "XRP", "솔라나": "SOL",
    "도지코인": "DOGE", "도지": "DOGE", "에이다": "ADA", "카르다노": "ADA", "바이낸스코인": "BNB", "비앤비": "BNB",
    "트론": "TRX", "아발란체": "AVAX", "아박": "AVAX", "체인링크": "LINK", "링크": "LINK", "폴카닷": "DOT",
    "라이트코인": "LTC", "라이트": "LTC", "시바이누": "SHIB", "시바": "SHIB", "페페": "PEPE", "수이": "SUI",
    "앱토스": "APT", "아비트럼": "ARB", "옵티미즘": "OP", "니어": "NEAR", "니어프로토콜": "NEAR",
    "유니스왑": "UNI", "코스모스": "ATOM", "아톰": "ATOM", "비트코인캐시": "BCH", "이더리움클래식": "ETC",
    "이클": "ETC", "스텔라루멘": "XLM", "스텔라": "XLM", "헤데라": "HBAR", "파일코인": "FIL", "톤코인": "TON",
    "톤": "TON", "인젝티브": "INJ", "셀레스티아": "TIA", "월드코인": "WLD", "엑스알피": "XRP", "이오스": "EOS",
    "비체인": "VET", "알고랜드": "ALGO", "샌드박스": "SAND", "디센트럴랜드": "MANA", "에이브": "AAVE",
    "메이커": "MKR", "렌더": "RENDER", "페치": "FET", "그래프": "GRT", "아이오타": "IOTA", "퀀텀": "QTUM",
    "시세": "XEM", "엔진": "ENJ", "더그래프": "GRT", "세이": "SEI", "스택스": "STX", "도지캐시": "DOGE",
}

_NUM_RE = re.compile(r"^\d[\d,]*(\.\d+)?$|^\.\d+$")


def _num_or_none(s):
    s = s.strip()
    if not _NUM_RE.match(s):
        return None
    try:
        v = float(s.replace(",", ""))
    except ValueError:
        return None
    return v if v > 0 and math.isfinite(v) else None


def load_price_alerts():
    try:
        with open(PRICE_ALERT_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, list) else []
    except FileNotFoundError:
        return []
    except Exception as e:
        print("가격 알림 파일 읽기 실패:", e)
        return []


def save_price_alerts(lst):
    tmp = PRICE_ALERT_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(lst, f, ensure_ascii=False, indent=2)
    os.replace(tmp, PRICE_ALERT_FILE)


def get_all_prices():
    last_err = None
    for base in BASES:
        try:
            r = HTTP.get(base + "/fapi/v1/ticker/price", timeout=10)
            r.raise_for_status()
            return {x["symbol"]: float(x["price"]) for x in r.json()}
        except Exception as e:
            last_err = e
    raise RuntimeError("바이낸스 선물 접속 실패: %s" % last_err)


def resolve_symbol(name, prices):
    n = name.strip()
    base = KR_COINS.get(n)
    if base is None and n.endswith("코인"):
        base = KR_COINS.get(n[:-2])
    if base is None:
        u = n.upper().replace("/", "").replace("-", "")
        if not re.fullmatch(r"[A-Z0-9]{2,15}", u):
            return None, None
        if u.endswith("USDT"):
            u = u[:-4]
        base = u
    for cand in (base + "USDT", "1000" + base + "USDT"):
        if cand in prices:
            return cand, prices[cand]
    return None, None


def _fmt_target(v):
    return fmt_p(v) if v >= 1 else ("%.6g" % v)


def price_alert_list_text():
    lst = load_price_alerts()
    if not lst:
        return ("등록된 가격 알림이 없어요.\n\n"
                "등록: 이더리움 2784\n"
                "삭제: 알림삭제 이더리움 (또는 알림삭제 이더리움 2784 / 알림삭제 전체)")
    lines = ["🔔 가격 알림 %d개" % len(lst)]
    for a in lst:
        lines.append("%s %s (%s) %s  %s" % (
            "📈" if a["dir"] == "up" else "📉", a.get("name", a["sym"]), a["sym"],
            _fmt_target(a["target"]), "이상 도달 시" if a["dir"] == "up" else "이하 도달 시"))
    lines.append("\n삭제: 알림삭제 이더리움 / 알림삭제 전체")
    return "\n".join(lines)


def add_price_alert(name, target):
    try:
        prices = get_all_prices()
    except Exception as e:
        return "⚠️ 현재가 조회 실패: %s" % str(e)[:200]
    sym, cur = resolve_symbol(name, prices)
    if not sym:
        return ("'%s' 종목을 바이낸스 선물에서 못 찾았어요.\n"
                "영문 티커로 다시 입력해 보세요. 예) ETH 2784 / SOL 150\n"
                "(코인만 지원, 주식은 안 돼요)" % name)
    if abs(target - cur) / cur < 1e-9:
        return "%s 현재가가 이미 %s 이에요." % (sym, _fmt_target(cur))
    direction = "up" if target > cur else "down"
    now_ms = int(time.time() * 1000)
    lst = [a for a in load_price_alerts() if not (a["sym"] == sym and abs(a["target"] - target) < 1e-12)]
    lst.append({"sym": sym, "name": name, "target": target, "dir": direction, "created": now_ms,
                "from": (now_ms // 60000 + 1) * 60000})
    save_price_alerts(lst)
    gap = (target - cur) / cur * 100
    return ("✅ 가격 알림 등록\n%s (%s)\n현재가 %s → 목표 %s (%+.2f%%)\n%s 알려드릴게요 (1회)"
            % (name, sym, _fmt_target(cur), _fmt_target(target), gap,
               "위로 올라가 닿으면" if direction == "up" else "아래로 내려가 닿으면"))


def remove_price_alerts(args):
    lst = load_price_alerts()
    if not lst:
        return "등록된 가격 알림이 없어요."
    if args and args[0] in ("전체", "모두", "all"):
        save_price_alerts([])
        return "🗑 가격 알림 %d개를 전부 삭제했어요." % len(lst)
    if not args:
        return "삭제할 종목을 적어주세요. 예) 알림삭제 이더리움 / 알림삭제 이더리움 2784 / 알림삭제 전체"
    try:
        prices = get_all_prices()
    except Exception:
        prices = {}
    sym, _ = resolve_symbol(args[0], prices)
    if not sym:
        sym = next((a["sym"] for a in lst if a.get("name") == args[0] or a["sym"] == args[0].upper()
                    or a["sym"] == args[0].upper() + "USDT"), None)
    if not sym:
        return "'%s' 종목의 알림이 없어요." % args[0]
    tgt = _num_or_none(args[1]) if len(args) > 1 else None
    keep, gone = [], []
    for a in lst:
        hit = a["sym"] == sym and (tgt is None or abs(a["target"] - tgt) < 1e-9 * max(1.0, tgt))
        (gone if hit else keep).append(a)
    if not gone:
        return "일치하는 알림이 없어요. '내알림'으로 목록을 확인해 보세요."
    save_price_alerts(keep)
    return "🗑 %s 알림 %d개 삭제: %s" % (sym, len(gone), ", ".join(_fmt_target(a["target"]) for a in gone))


def check_price_alerts():
    lst = load_price_alerts()
    if not lst:
        return
    now_ms = int(time.time() * 1000)
    cur_min = now_ms // 60000 * 60000
    by_sym = {}
    for a in lst:
        by_sym.setdefault(a["sym"], []).append(a)
    triggered, changed = [], False
    for sym, alerts in by_sym.items():
        start = min(a.get("from", cur_min) for a in alerts)
        limit = int(min(1500, max(5, (now_ms - start) // 60000 + 3)))
        try:
            candles = get_candles(sym, "1m", limit=limit, ttl=2.0)
        except Exception as e:
            print("[가격알림 %s] 시세 조회 실패: %s" % (sym, e))
            continue
        if not candles:
            continue
        price = candles[-1]["c"]
        for a in alerts:
            part = [c for c in candles if c["t"] >= a.get("from", cur_min)]
            hi = max([price] + [c["h"] for c in part])
            lo = min([price] + [c["l"] for c in part])
            hit = hi >= a["target"] if a["dir"] == "up" else lo <= a["target"]
            if hit:
                triggered.append((a, price))
            elif cur_min > a.get("from", 0):
                a["from"] = cur_min
                changed = True
    if triggered:
        gone = {id(a) for a, _ in triggered}
        keep = [a for a in lst if id(a) not in gone]
        save_price_alerts(keep)
        for a, price in triggered:
            send_telegram("🔔 가격 도달!\n%s (%s)\n목표 %s %s\n현재가 %s"
                          % (a.get("name", a["sym"]), a["sym"], _fmt_target(a["target"]),
                             "돌파(이상)" if a["dir"] == "up" else "하락(이하)", _fmt_target(price)))
    elif changed:
        save_price_alerts(lst)


def price_alert_route(words):
    w = words[0]
    if len(words) == 1 and w in ("내알림", "알림목록", "알림", "가격알림", "알림확인"):
        send_telegram(price_alert_list_text())
        return True
    if w in ("알림삭제", "알림취소", "삭제") and len(words) >= 2:
        send_telegram(remove_price_alerts(words[1:]))
        return True
    if w in ("알림삭제", "알림취소"):
        send_telegram(remove_price_alerts([]))
        return True
    if len(words) == 2:
        target = _num_or_none(words[1])
        if target is not None:
            send_telegram(add_price_alert(w, target))
            return True
    return False


PRICE_UPDATE_FLAG = os.path.expanduser("~/price_bot_update.flag")
PRICE_HEARTBEAT = os.path.expanduser("~/price_bot.heartbeat")


def request_price_bot_update():
    try:
        age = time.time() - os.path.getmtime(PRICE_HEARTBEAT)
    except OSError:
        age = None
    try:
        with open(PRICE_UPDATE_FLAG, "w") as f:
            f.write(str(int(time.time())))
    except OSError as e:
        send_telegram("가격봇 업데이트 요청 실패: %s" % e)
        return
    if age is None or age > 60:
        send_telegram("📨 가격봇에 업데이트 요청은 남겼는데, 가격봇이 꺼져 있는 것 같아요.\n"
                      "run_all.py 로 같이 켜져 있는지 확인하세요. 켜지면 바로 업데이트됩니다.")
    else:
        send_telegram("📨 가격봇에 업데이트를 요청했어요. 결과는 가격알림 채팅방으로 가요.")


def update_bots(cfg, target):
    if target in ("가격봇", "전체", "all"):
        request_price_bot_update()
    if target in ("알림봇", "전체", "all"):
        do_update(cfg)


def _extract_caption_tf_and_sym(msg, cfg):
    """버튼을 누른 차트 메시지의 캡션에서 시간봉(tf)과 종목(symbol)을 추출한다."""
    caption_src = str((msg or {}).get("caption") or "").upper()
    tf_match = re.search(r"\b(5M|15M|1H|4H|12H|1D|1W)\b", caption_src)
    caption_tf = {
        "5M": "5m", "15M": "15m", "1H": "1h", "4H": "4h",
        "12H": "12h", "1D": "1d", "1W": "1w"
    }.get(tf_match.group(1)) if tf_match else None
    sym_match = re.search(r"\b([A-Z0-9]{2,12}USDT)\b", caption_src)
    caption_sym = sym_match.group(1) if sym_match else None
    syms = [caption_sym] if (caption_sym and caption_sym in cfg.get("symbols", {})) else active_symbols(cfg)
    return caption_tf, syms


def route(text, cfg):
    raw = text.strip()
    if raw.startswith("/"):
        raw = raw[1:]
    if raw.startswith("패치취소") or raw.startswith("롤백"):
        if HOT_PATCH_ENABLED:
            rollback_patch()
        else:
            send_telegram("패치 기능이 꺼져 있어요.")
        return
    if raw.startswith("패치"):
        if HOT_PATCH_ENABLED:
            apply_hot_patch(raw)
        else:
            send_telegram("패치 기능이 꺼져 있어요. (HOT_PATCH_ENABLED = False)")
        return
    t = text.strip()
    if t.startswith("/"):
        t = t[1:]
    words = t.split()
    if not words:
        return
    w = words[0]
    if w in ("종목추가", "종목삭제", "전체봉", "확대봉", "횟수", "15분터치", "15분범위", "업데이트주소", "급변기준", "거래량배수"):
        send_telegram(edit_setting(cfg, w, words[1:]))
    elif price_alert_route(words):
        pass
    elif t in CHART_BUTTONS:
        tf = CHART_BUTTONS[t]
        for sym in active_symbols(cfg):
            try:
                send_chart(sym, tf, cfg)
            except Exception as e:
                send_telegram("%s 차트 실패: %s" % (sym, e))
    elif w == "차트" and len(words) > 1:
        sym = words[1].upper()
        sym = sym if sym.endswith("USDT") else sym + "USDT"
        tf = words[2].lower() if len(words) > 2 else "1h"
        if tf not in ALLOWED_TF:
            send_telegram("가능한 봉: " + " ".join(ALLOWED_TF))
        elif len(words) > 3 and words[3].isdigit():
            send_chart_custom_bars(sym, tf, int(words[3]), cfg)
        else:
            send_chart(sym, tf, cfg)
    elif "차트" in t:
        send_telegram("어떤 봉 차트를 볼까요? (켜져 있는 종목 전부)", markup=chart_markup())
    elif "현황" in t or w.lower() == "status":
        send_status(cfg)
    elif w.lower() in ("통계", "승률", "stats"):
        send_telegram(paper_stats_text(load_paper()))
    elif w.lower() in ("업데이트", "update") and len(words) > 1 and words[1] in ("가격봇", "알림봇", "전체", "all"):
        update_bots(cfg, words[1])
    elif "업데이트" in t or w.lower() == "update":
        do_update(cfg)
    elif "설정" in t or w.lower() == "settings":
        send_telegram(settings_text(cfg), markup=settings_markup(cfg))
    elif w.lower().startswith("start") or "메뉴" in t:
        send_telegram("하단 입력창 자판이 올라오지 않도록 인라인 버튼 모드로 전환했습니다.", markup=REMOVE_KEYBOARD)
        send_telegram("버전 %s 실행 중입니다. 아래 버튼을 눌러 대형 차트와 현황을 바로 확인하세요." % VERSION)


def handle_callback(cq, cfg):
    try:
        tg("answerCallbackQuery", data={"callback_query_id": cq["id"]})
    except Exception:
        pass
    data_str = cq.get("data") or ""
    kind, _, val = data_str.partition(":")
    msg = cq.get("message") or {}
    if kind == "ct":
        for sym in active_symbols(cfg):
            try:
                send_chart(sym, val, cfg)
            except Exception as e:
                send_telegram("%s 차트 실패: %s" % (sym, e))
        return
    if kind == "cb":
        # cb:<tf>:<bars> -> 차트 하단의 [🔭120봉] [📊80봉] [🔍25봉] 버튼 클릭 시 원하는 봉 개수로 즉시 재렌더링
        tf_part, _, bars_part = val.partition(":")
        caption_tf, syms = _extract_caption_tf_and_sym(msg, cfg)
        tf = caption_tf or (tf_part if tf_part in ALLOWED_TF else "15m")
        n_bars = int(bars_part) if bars_part.isdigit() else 80
        for sym in syms:
            try:
                send_chart_custom_bars(sym, tf, n_bars, cfg)
            except Exception as e:
                send_telegram("%s %d봉 차트 실패: %s" % (sym, n_bars, e))
        return
    if kind == "cba":
        # cba:<tf> -> [🤖자동봉] 버튼 클릭 시 유동적 봉 개수(큰그림+확대차트 쌍)로 즉시 재전송
        caption_tf, syms = _extract_caption_tf_and_sym(msg, cfg)
        tf = caption_tf or (val if val in ALLOWED_TF else "15m")
        for sym in syms:
            try:
                send_chart(sym, tf, cfg)
            except Exception as e:
                send_telegram("%s 자동봉 차트 실패: %s" % (sym, e))
        return
    if kind == "c15":
        caption_tf, syms = _extract_caption_tf_and_sym(msg, cfg)
        tf = caption_tf or (val if val in ALLOWED_TF else "15m")
        for sym in syms:
            try:
                send_chart_15(sym, tf, cfg)
            except Exception as e:
                send_telegram("%s 최근 15봉 차트 실패: %s" % (sym, e))
        return
    if kind == "act":
        if val == "status":
            try:
                send_status(cfg)
            except Exception as e:
                print("현황 버튼 처리 실패:", repr(e))
                send_telegram("⚠️ 현황 조회 중 오류가 발생했습니다. 잠시 후 다시 눌러주세요.\n오류: %s" % str(e)[:250])
        elif val == "settings":
            send_telegram(settings_text(cfg), markup=settings_markup(cfg))
        elif val == "update":
            do_update(cfg)
        elif val == "menu":
            send_telegram("📌 메인 메뉴입니다. 원하는 시간봉이나 배율 버튼을 선택하세요.")
        elif val == "alerts":
            send_telegram(price_alert_list_text())
        return
    if kind == "s":
        cfg["symbols"][val] = not cfg["symbols"].get(val, False)
    elif kind == "t":
        cfg["tf_on"][val] = not cfg["tf_on"].get(val, False)
    elif kind == "e":
        cfg["ema_on"][val] = not cfg["ema_on"].get(val, False)
    elif kind == "r":
        cfg["rep_on"] = not cfg["rep_on"]
    elif kind == "g":
        cfg["surge_on"] = not cfg.get("surge_on", True)
    elif kind == "f":
        cfg["fib_on"] = not cfg.get("fib_on", True)
    elif kind == "w":
        cfg["ew_on"] = not cfg.get("ew_on", True)
    elif kind == "v":
        cfg["vol_on"] = not cfg.get("vol_on", True)
    elif kind == "m":
        cfg["mtf_on"] = not cfg.get("mtf_on", True)
    elif kind == "b":
        cfg["dyn_bars_on"] = not cfg.get("dyn_bars_on", True)
    elif kind == "z":
        cfg["zoom_on"] = not cfg.get("zoom_on", True)
    else:
        return
    save_cfg(cfg)
    try:
        tg("editMessageReplyMarkup", data={
            "chat_id": msg["chat"]["id"], "message_id": msg["message_id"],
            "reply_markup": json.dumps(settings_markup(cfg))})
    except Exception as e:
        print("설정 화면 갱신 실패:", e)


def handle_updates(wait, cfg):
    chat_id = str(os.environ.get("TELEGRAM_CHAT_ID", ""))
    if not os.environ.get("TELEGRAM_TOKEN"):
        time.sleep(wait)
        return
    try:
        r = tg("getUpdates", timeout=max(6, wait + 5), params={"offset": update_offset[0], "timeout": wait,
                                     "allowed_updates": json.dumps(["message", "callback_query"])})
        r.raise_for_status()
        for u in r.json().get("result", []):
            update_offset[0] = u["update_id"] + 1
            try:
                if "callback_query" in u:
                    cq = u["callback_query"]
                    if str((cq.get("message") or {}).get("chat", {}).get("id")) == chat_id:
                        handle_callback(cq, cfg)
                else:
                    m = u.get("message") or {}
                    if str(m.get("chat", {}).get("id")) == chat_id:
                        route(m.get("text") or "", cfg)
            except Exception as e:
                print("처리 오류:", e)
    except requests.exceptions.Timeout:
        pass
    except Exception as e:
        print("업데이트 확인 오류:", e)
        time.sleep(2)


def single_instance():
    old = 0
    try:
        with open(PID_FILE, "r") as f:
            old = int(f.read().strip())
    except Exception:
        pass
    if old and old != os.getpid():
        try:
            with open("/proc/%d/cmdline" % old, "rb") as f:
                is_bot = b"alert_bot" in f.read()
            if is_bot:
                os.kill(old, signal.SIGTERM)
                time.sleep(2)
        except Exception:
            pass
    with open(PID_FILE, "w") as f:
        f.write(str(os.getpid()))


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        send_telegram("✅ 알림봇 연결 테스트 성공!\n버전: %s\n파일: %s" % (VERSION, VERSION_FILE))
        return
    single_instance()
    load_alert_state()
    cfg = load_cfg()
    print("실시간 감시 시작:", ", ".join(active_symbols(cfg)), "/", ", ".join(active_tfs(cfg)))
    paper = load_paper()
    print("가상매매 봇:", "토큰 설정됨" if paper.get("token") else "토큰 미설정 (~/paper_config.json 확인)")
    send_telegram("🧹 기존 하단 키보드를 숨기고 자판이 올라오지 않는 인라인 버튼 모드로 전환합니다.", markup=REMOVE_KEYBOARD)
    send_telegram(
        "🚀 알림봇 시작!\n"
        "버전: %s\n"
        "파일: %s\n"
        "기능: 유동적 봉 개수(1번 큰그림 65~150봉 자동확장 · 2번 확대차트 16~42봉 파동맞춤 축소) + 원터치 배율 버튼(120/80/25/15/자동봉)\n"
        "엘리어트 파동(2파·4파·삼각형·다이아고날) + 맞춤 피보나치 + 무효화 SL & 확장 TP + 1초 즉시 응답\n"
        "🔔 가격 알림: '이더리움 2784' (내알림 / 알림삭제 이더리움)\n"
        "🔄 업데이트 가격봇 / 업데이트 알림봇 / 업데이트 전체" % (VERSION, VERSION_FILE)
    )
    last_full_scan = 0.0
    last_fast_scan = 0.0
    while True:
        now = time.monotonic()
        cfg = load_cfg()

        if now - last_fast_scan >= FAST_CHECK_SECONDS:
            last_fast_scan = now
            try:
                check_price_alerts()
            except Exception as e:
                print("가격 알림 검사 오류:", e)
            try:
                update_paper_positions()
            except Exception as e:
                print("가상 포지션 업데이트 오류:", e)

        if now - last_full_scan >= POLL_SECONDS:
            last_full_scan = now
            try:
                check_sudden_moves(cfg)
                check_all(cfg)
            except Exception as e:
                print("감시 오류:", e)

        handle_paper_updates()
        handle_updates(BOT_TICK_SECONDS, cfg)


if __name__ == "__main__":
    main()