"""
바이낸스 선물 EMA 터치 실시간 알림봇 (텔레그램) v3.34-paper (최근15봉 원본 시간봉 강제연동)
- 15분/1시간/4시간/12시간/일/주봉 x EMA 7, 25, 99 터치 후 반등/거절 알림 (고해상도 대형 차트 첨부)
- 차트에 피보나치 시작점(START 1.0)·끝지점(END 0.0) 마커 및 우측 0.382 / 0.618 / NOW 가격 라벨 표시
- 15분봉 EMA7 반복 터치 후 다시 반등/거절 알림
- 요일 제한 없이 매일 알림, 5분봉 신호 집계 범위는 최근 2시간
- 버튼: 휴대폰/PC 키보드 자판이 절대 뜨지 않는 인라인 메뉴 버튼 적용
- 최적화: 메모리 슬라이싱 고속 렌더링 + HTTP 세션 재사용 + 스마트 알림 캐시 관리
- v3.18: 사진 캡션에서 차트에 이미 보이는 정보(피보나치 값/색상 범례/면책/긴 전망) 제거, 한 줄 추세만 표시
- v3.19: 기존 전체 차트(1번째 사진) 뒤에 최근 30개 캔들 피보나치 확대 차트(2번째 사진)를 따로 전송, 설정에서 켜기/끄기
- v3.21: 피보나치를 "최근 유효 스윙 파동(Pivot Swing)" 방식으로 정밀화, 차트에 보이는 봉(60/30) 기준으로 각각 계산,
         업데이트 실패 원인(괄호 문법 오류) 수정, 확대 차트 설정 버튼(zoom_on) 유지
- v3.22: 텔레그램 getUpdates 롱폴링(20초)과 요청 타임아웃(20초)이 겹쳐 "Read timed out"이 반복되던 문제 수정
- v3.23: 텔레그램 채팅방에서 "패치" + 함수/변수 코드를 보내면 봇 파일의 같은 이름 함수가 교체되고 자동 재시작(내 채팅방 전용, "패치취소"로 되돌리기)
- v3.34: 최근15봉 버튼을 누른 원본 차트 캡션의 시간봉으로 우선 결정해 구버전 버튼 데이터가 남아도 4H→15M 오작동 방지; 최근15봉 캡션 명확화
- 실행: python alert_bot_v3.34_paper.py     연결 테스트: python alert_bot_v3.34_paper.py --test
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

VERSION = "v3.34-paper (최근15봉 원본 시간봉 강제연동)"
VERSION_FILE = "alert_bot_v3.34_paper.py"
HOT_PATCH_ENABLED = True  # 텔레그램 채팅 "패치" 기능 (TELEGRAM_CHAT_ID 로 등록된 내 채팅방에서만 동작)
FULL_N = 60  # 1번째(전체) 차트에 표시할 캔들 개수
ZOOM_N = 30  # 2번째(확대) 차트에 표시할 최근 캔들 개수
POLL_SECONDS = 20  # 시세 확인 주기(초). 버튼은 누르면 바로 응답

# 네트워크 속도 및 안정성 최적화를 위한 전역 세션(Connection Pool)
HTTP = requests.Session()
HTTP.headers.update({"User-Agent": "TradingAlertBot/3.25"})

ALLOWED_TF = ["5m", "15m", "1h", "4h", "12h", "1d", "1w"]
EMA_LIST = [7, 25, 99]

DEFAULTS = {
    "symbols": {"BTCUSDT": True, "ETHUSDT": True, "SOLUSDT": True},
    "tf_on": {tf: (tf != "5m") for tf in ALLOWED_TF},  # 5분봉은 차트용(일반 EMA 알림은 설정에서 켜기)
    "ema_on": {"7": True, "25": True, "99": True},
    "config_version": 315,
    "min_count": 1,              # 최근 기간 안에 같은 방향 신호가 이 횟수 이상일 때만 알림 (5분봉은 최근 2시간)
    "rep_on": True,              # 15분봉 EMA7 반복 터치 알림
    "rep_touch_min": 2,          # 이전에 EMA7을 이 횟수 이상 터치했어야 함
    "rep_window": 24,            # 최근 몇 개 15분봉을 볼지 (24개 = 6시간)
    "update_url": "",
    "surge_on": True,
    "surge_change_pct": 0.7,     # 5분봉 시가 대비 급변 기준(%)
    "surge_volume_mult": 2.5,    # 이전 20개 마감봉 평균 거래량 배수
    "fib_on": True,              # 차트에 피보나치 0.382 / 0.618 되돌림 및 텍스트 라벨 표시
    "zoom_on": True,             # 최근 30개 캔들 피보나치 확대 차트를 두 번째 사진으로 추가 전송
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
PID_FILE = os.path.expanduser("~/alert_bot.pid")
alerted = {}             # 순서 유지 딕셔너리로 오래된 알림만 선별 정리
closed_candle_seen = set()
update_offset = [0]

CHART_BUTTONS = {
    "📈5분": "5m",
    "📈15분": "15m",
    "📈1시간": "1h",
    "📈4시간": "4h",
    "📈12시간": "12h",
    "📈일봉": "1d",
    "📈주봉": "1w",
}

# 자판이 절대 올라오지 않는 인라인 메뉴 버튼
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
            {"text": "🕯 최근15봉 (선택 봉)", "callback_data": "c15:15m"},
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
    " ": ["00000", "00000", "00000", "00000", "00000", "00000", "00000"],
    "A": ["01110", "10001", "10001", "11111", "10001", "10001", "10001"],
    "B": ["11110", "10001", "10001", "11110", "10001", "10001", "11110"],
    "D": ["11110", "10001", "10001", "10001", "10001", "10001", "11110"],
    "E": ["11111", "10000", "10000", "11110", "10000", "10000", "11111"],
    "F": ["11111", "10000", "10000", "11110", "10000", "10000", "10000"],
    "I": ["01110", "00100", "00100", "00100", "00100", "00100", "01110"],
    "M": ["10001", "11011", "10101", "10101", "10001", "10001", "10001"],
    "N": ["10001", "11001", "10101", "10011", "10001", "10001", "10001"],
    "O": ["01110", "10001", "10001", "10001", "10001", "10001", "01110"],
    "R": ["11110", "10001", "10001", "11110", "10100", "10010", "10001"],
    "S": ["01111", "10000", "10000", "01110", "00001", "00001", "11110"],
    "T": ["11111", "00100", "00100", "00100", "00100", "00100", "00100"],
    "W": ["10001", "10001", "10001", "10101", "10101", "11011", "10001"],
    "Z": ["11111", "00001", "00010", "00100", "01000", "10000", "11111"],
    "=": ["00000", "00000", "11111", "00000", "11111", "00000", "00000"],
}


def mark_alerted(key):
    alerted[key] = True
    if len(alerted) > 3000:
        # 전체 초기화 대신 오래된 절반만 제거하여 진행 중인 봉의 중복 알림 방지
        for old_k in list(alerted.keys())[:1500]:
            alerted.pop(old_k, None)


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
              "surge_on", "surge_change_pct", "surge_volume_mult", "fib_on", "zoom_on"):
        if k in raw:
            cfg[k] = raw[k]

    cfg["config_version"] = 315
    if raw.get("config_version", 0) != 315:
        try:
            save_cfg(cfg)
        except Exception:
            pass
    return cfg


def save_cfg(cfg):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)


def active_symbols(cfg):
    return [s for s, on in cfg["symbols"].items() if on]


def active_tfs(cfg):
    return [tf for tf in ALLOWED_TF if cfg["tf_on"].get(tf)]


def active_emas(cfg):
    return [n for n in EMA_LIST if cfg["ema_on"].get(str(n))]


# ---------------- 시세/지표 (바이낸스 선물) ----------------
def get_candles(symbol, interval, limit=500):
    """진행 중인 봉 포함. 마지막 봉의 종가 = 현재가"""
    last_err = None
    for base in BASES:
        try:
            r = HTTP.get(
                base + "/fapi/v1/klines",
                params={"symbol": symbol, "interval": interval, "limit": limit},
                timeout=10,
            )
            r.raise_for_status()
            return [{"t": k[0], "o": float(k[1]), "h": float(k[2]),
                     "l": float(k[3]), "c": float(k[4]), "v": float(k[5])} for k in r.json()]
        except Exception as e:
            last_err = e
    raise RuntimeError("바이낸스 선물 접속 실패: %s" % last_err)


def ema_series(closes, n):
    a = 2.0 / (n + 1)
    out = [closes[0]]
    for x in closes[1:]:
        out.append(a * x + (1 - a) * out[-1])
    return out


def classify(c, v, move):
    """위에서 내려와 터치 후 위로 = long / 아래에서 올라와 터치 후 아래로 = short"""
    if c["o"] >= v and c["l"] <= v and c["c"] >= v * (1 + move):
        return "long"
    if c["o"] <= v and c["h"] >= v and c["c"] <= v * (1 - move):
        return "short"
    return None


def fmt_p(v):
    """가격 크기에 따라 소수점 자리수를 깔끔하게 포맷"""
    if v >= 1000:
        return "{:,.1f}".format(v)
    elif v >= 10:
        return "{:,.2f}".format(v)
    else:
        return "{:,.4f}".format(v)


def calc_fib_info(candles, N=60):
    """최근 유효 스윙 파동(Pivot Swing) 역추적. 인덱스는 마지막 N개 봉 기준(차트 좌표)"""
    cs = candles[-N:] if len(candles) >= N else candles
    L = len(cs)
    if L < 15:
        return None

    overall_hi = max(c["h"] for c in cs)
    overall_lo = min(c["l"] for c in cs)
    total_span = overall_hi - overall_lo
    if total_span <= 0:
        return None

    piv_hi, piv_lo = [], []
    for i in range(2, L - 1):
        h = cs[i]["h"]
        l = cs[i]["l"]
        left_h = [cs[j]["h"] for j in range(max(0, i - 2), i)]
        right_h = [cs[j]["h"] for j in range(i + 1, min(L, i + 3))]
        if h >= max(left_h) and h >= max(right_h):
            piv_hi.append(i)

        left_l = [cs[j]["l"] for j in range(max(0, i - 2), i)]
        right_l = [cs[j]["l"] for j in range(i + 1, min(L, i + 3))]
        if l <= min(left_l) and l <= min(right_l):
            piv_lo.append(i)

    recent_cut = max(0, L - 40)
    cand_hi = [i for i in piv_hi if i >= recent_cut] or [max(range(recent_cut, L), key=lambda i: cs[i]["h"])]
    cand_lo = [i for i in piv_lo if i >= recent_cut] or [min(range(recent_cut, L), key=lambda i: cs[i]["l"])]

    hi_end = max(cand_hi, key=lambda i: cs[i]["h"])
    lo_end = min(cand_lo, key=lambda i: cs[i]["l"])

    up_wave = None
    if hi_end >= 4:
        lo_start = min(range(0, hi_end), key=lambda i: cs[i]["l"])
        amp = cs[hi_end]["h"] - cs[lo_start]["l"]
        if amp >= total_span * 0.28 and (hi_end - lo_start) >= 3:
            up_wave = (lo_start, hi_end, amp)

    down_wave = None
    if lo_end >= 4:
        hi_start = max(range(0, lo_end), key=lambda i: cs[i]["h"])
        amp = cs[hi_start]["h"] - cs[lo_end]["l"]
        if amp >= total_span * 0.28 and (lo_end - hi_start) >= 3:
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
        swing_low = cs[start_idx]["l"]
        swing_high = cs[end_idx]["h"]
        diff = swing_high - swing_low
        if diff <= 0:
            return None
        mode_label = "상승파동 눌림"
        start_val, end_val = swing_low, swing_high
        fib_382 = swing_high - diff * 0.382
        fib_500 = swing_high - diff * 0.500
        fib_618 = swing_high - diff * 0.618
        hi_idx, lo_idx = end_idx, start_idx
    else:
        for k in range(end_idx + 1, L):
            if cs[k]["l"] <= cs[end_idx]["l"]:
                end_idx = k
        swing_high = cs[start_idx]["h"]
        swing_low = cs[end_idx]["l"]
        diff = swing_high - swing_low
        if diff <= 0:
            return None
        mode_label = "하락파동 반등"
        start_val, end_val = swing_high, swing_low
        fib_382 = swing_low + diff * 0.382
        fib_500 = swing_low + diff * 0.500
        fib_618 = swing_low + diff * 0.618
        hi_idx, lo_idx = start_idx, end_idx

    price = cs[-1]["c"]
    in_golden_zone = min(fib_382, fib_618) <= price <= max(fib_382, fib_618)
    retracing = (end_idx < (L - 1) or (mode == "up" and price < swing_high * 0.998)
                 or (mode == "down" and price > swing_low * 1.002))

    return {
        "mode": mode,
        "mode_label": mode_label,
        "high": swing_high,
        "low": swing_low,
        "hi_idx": hi_idx,
        "lo_idx": lo_idx,
        "start_idx": start_idx,
        "end_idx": end_idx,
        "start_val": start_val,
        "end_val": end_val,
        "382": fib_382,
        "500": fib_500,
        "618": fib_618,
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
    res = {"price": price, "t": candles[last]["t"], "emas": {},
           "candles": candles, "ser": ser_all}
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


# ---------------- 대형 고해상도 차트 (고속 슬라이싱 렌더링 + 피보나치 라벨) ----------------
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


def draw_chart(candles, ser, hi=None, N=60, K=3, show_fib=True, tag=None):
    """K=3 기준 1680x840 대형 고해상도 차트 (메모리 슬라이싱으로 고속 생성)"""
    W, H = (560 * K if show_fib else 480 * K), 280 * K
    BG, GRID = (18, 23, 28), (38, 46, 54)
    GREEN, RED, WHITE = (38, 166, 154), (239, 83, 80), (220, 225, 230)
    EMA_COL = {7: (255, 193, 7), 25: (206, 92, 230), 99: (66, 165, 245)}
    FIB_382_COL = (0, 229, 255)      # 밝은 하늘색 - 0.382
    FIB_618_COL = (255, 150, 0)      # 선명한 주황/골드 - 0.618
    FIB_START_COL = (175, 185, 200)  # 피보나치 시작/끝 기준색
    FIB_TREND_COL = (240, 215, 95)   # 시작점 -> 끝점 연결 대각선 색상
    ZONE_BG = (30, 44, 58)           # 0.382 ~ 0.618 골든 존 배경색
    LABEL_BG = (26, 33, 41)          # 텍스트 라벨 가독성 박스 배경색

    pix = bytearray(bytes(BG) * (W * H))
    row_stride = W * 3

    def put(x, y, c):
        if 0 <= x < W and 0 <= y < H:
            i = y * row_stride + x * 3
            pix[i], pix[i + 1], pix[i + 2] = c

    def rect(x1, y1, x2, y2, c):
        """C언어 속도의 메모리 슬라이싱 직사각형 채우기"""
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
        """비트맵 폰트로 선명한 텍스트와 배경 박스를 렌더링"""
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
    pad = (top - lo) * 0.13 or top * 0.001
    lo, top = lo - pad, top + pad

    L = 8 * K
    R = W - (136 * K if show_fib else 16 * K)
    T, B = 20 * K, H - 10 * K
    bw = (R - L) / float(len(cs))

    def Y(v):
        return int(B - (v - lo) / (top - lo) * (B - T))

    fib = calc_fib_info(cs, len(cs)) if show_fib else None
    if fib and fib["retracing"]:
        fx0 = int(L + (fib["start_idx"] + 0.5) * bw)
        y382 = Y(fib["382"])
        y618 = Y(fib["618"])
        ya, yb = sorted((y382, y618))
        # 0.382 ~ 0.618 골든 존 배경 채우기 (슬라이싱으로 즉시 처리)
        rect(fx0, max(T, ya), R, min(B, yb), ZONE_BG)

    for k in range(1, 5):                                  # 가로 격자
        gy = T + (B - T) * k // 5
        rect(L, gy, R, gy, GRID)

    if fib:
        fx0 = int(L + (fib["start_idx"] + 0.5) * bw)
        fx1 = int(L + (fib["end_idx"] + 0.5) * bw)
        fy0 = Y(fib["start_val"])
        fy1 = Y(fib["end_val"])
        y382 = Y(fib["382"])
        y618 = Y(fib["618"])

        # 시작점(1.0)과 끝지점(0.0) 수평 기준 점선
        dashed_hline(L, R, fy0, FIB_START_COL, dash=3 * K, gap=3 * K, th=max(1, K - 1))
        dashed_hline(L, R, fy1, FIB_START_COL, dash=3 * K, gap=3 * K, th=max(1, K - 1))

        # 0.382 / 0.618 수평 되돌림 점선 (되돌림 중일 때만)
        if fib["retracing"]:
            dashed_hline(L, R + 4 * K, y382, FIB_382_COL, dash=6 * K, gap=3 * K, th=K)
            dashed_hline(L, R + 4 * K, y618, FIB_618_COL, dash=6 * K, gap=3 * K, th=K)

        # 시작점 -> 끝지점 연결 대각선
        dashed_line(fx0, fy0, fx1, fy1, FIB_TREND_COL, dash=5 * K, gap=3 * K, th=K)

    # ---- 캔들 그리기 ----
    for k, c in enumerate(cs):
        xc = int(L + (k + 0.5) * bw)
        half = max(1, int(bw * 0.33))
        col = GREEN if c["c"] >= c["o"] else RED
        line(xc, Y(c["h"]), xc, Y(c["l"]), col, K)
        y1, y2 = sorted((Y(c["o"]), Y(c["c"])))
        rect(xc - half, y1, xc + half, max(y2, y1 + K), col)

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

    ly = Y(cs[-1]["c"])                                    # 현재가 가로 점선
    dashed_hline(L, R + 4 * K, ly, WHITE, dash=3 * K, gap=3 * K, th=K)

    # ---- 피보나치 시작점/끝지점 마커 및 오른쪽 숫자 텍스트 렌더링 ----
    if fib:
        fx0 = int(L + (fib["start_idx"] + 0.5) * bw)
        fx1 = int(L + (fib["end_idx"] + 0.5) * bw)
        fy0 = Y(fib["start_val"])
        fy1 = Y(fib["end_val"])
        y382 = Y(fib["382"])
        y618 = Y(fib["618"])

        # 시작점(START 1.0) & 끝지점(END 0.0) 이중 타겟 마커
        draw_circle(fx0, fy0, 5 * K, FIB_TREND_COL, th=K)
        rect(fx0 - 2 * K, fy0 - 2 * K, fx0 + 2 * K, fy0 + 2 * K, FIB_TREND_COL)
        draw_circle(fx1, fy1, 5 * K, WHITE, th=K)
        rect(fx1 - 2 * K, fy1 - 2 * K, fx1 + 2 * K, fy1 + 2 * K, WHITE)

        # 시작점/끝지점 캔들 위아래에 START / END 직접 표기
        s_tag_y = fy0 + 8 * K if fib["mode"] == "up" else fy0 - 15 * K
        e_tag_y = fy1 - 15 * K if fib["mode"] == "up" else fy1 + 8 * K
        draw_text(max(L, min(R - 35 * K, fx0 - 14 * K)), max(T, min(B - 8 * K, s_tag_y)), "START", FIB_TREND_COL, scale=K)
        draw_text(max(L, min(R - 25 * K, fx1 - 10 * K)), max(T, min(B - 8 * K, e_tag_y)), "END", WHITE, scale=K)

        # 오른쪽 여백에 0.382 / 0.618 / 시작(1.0) / 끝(0.0) / 현재가(NOW) 숫자 텍스트 작성
        labels = [
            {"y": fy0,  "text": "1.0(S) " + fmt_p(fib["start_val"]), "col": FIB_START_COL},
            {"y": fy1,  "text": "0.0(E) " + fmt_p(fib["end_val"]), "col": FIB_START_COL},
            {"y": ly,   "text": "NOW " + fmt_p(cs[-1]["c"]), "col": WHITE},
        ]
        if fib["retracing"]:
            labels.append({"y": y382, "text": "0.382 " + fmt_p(fib["382"]), "col": FIB_382_COL})
            labels.append({"y": y618, "text": "0.618 " + fmt_p(fib["618"]), "col": FIB_618_COL})
        labels.sort(key=lambda item: item["y"])
        min_gap = 11 * K
        for i in range(1, len(labels)):
            if labels[i]["y"] - labels[i - 1]["y"] < min_gap:
                labels[i]["y"] = labels[i - 1]["y"] + min_gap

        for lb in labels:
            ty = max(T, min(B - 8 * K, lb["y"] - 3 * K))
            draw_text(R + 6 * K, ty, lb["text"], lb["col"], scale=K, bg_box=True)

    if hi in ser:                                          # EMA 터치 지점 흰 원
        cx, cy = int(L + (len(cs) - 0.5) * bw), Y(ser[hi][-1])
        draw_circle(cx, cy, 9 * K, WHITE, th=K + 1)

    # 상단 범례 바 (색상 + 텍스트로 한눈에 구분)
    lx = 8 * K
    for n in EMA_LIST:
        rect(lx, 5 * K, lx + 8 * K, 11 * K, EMA_COL[n])
        draw_text(lx + 10 * K, 5 * K, "EMA%d" % n, EMA_COL[n], scale=K, bg_box=False)
        lx += 48 * K
    if fib:
        draw_text(lx + 4 * K, 5 * K, "FIB (N=%d)" % N, FIB_382_COL, scale=K, bg_box=False)
    if tag:                                                # 확대 차트 등 구분용 태그
        draw_text(lx + (80 * K if fib else 4 * K), 5 * K, tag, WHITE, scale=K, bg_box=False)

    return png_bytes(W, H, pix)


# ---------------- 두 번째 텔레그램 봇: 자동 가상매매 ----------------
# 실제 주문은 전혀 전송하지 않습니다. 두 번째 봇 토큰은 ~/paper_config.json에 직접 입력하세요.
PAPER_FILE = os.path.expanduser("~/paper_config.json")
PAPER_DEFAULTS = {
    "on": True, "token": "", "chat_id": "", "offset": 0,
    "init_bud": 300.0, "bal": 300.0, "lev": 7, "alloc": 0.2,
    "rr": 2.0, "pos": {}, "hist": [], "seen": []
}
PAPER_INLINE_MARKUP = {"inline_keyboard": [
    [{"text": "📊 가상매매 현황", "callback_data": "p:status"},
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
    alloc_vals = list(globals().get("PAPER_ALLOC", {}).values())
    if alloc_vals:
        d["alloc"] = max(alloc_vals)
    return d


def save_paper(p):
    # 환경변수로만 전달된 토큰은 설정 파일에 기록하지 않음
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
    initial = float(p.get("init_bud", 1000.0))
    balance = float(p.get("bal", initial))
    realized = balance - initial
    lines = ["📊 자동 가상매매 현황 (실제 주문 없음)",
             "잔고: %.2f USDT | 실현손익: %+.2f USDT" % (balance, realized),
             "레버리지: %sx | 증거금 배분: %.0f%% | 목표 손익비: 1:%.1f" %
             (p.get("lev", 5), float(p.get("alloc", .2))*100, p.get("rr", 2.0))]
    positions = p.get("pos", {})
    if not positions:
        lines.append("\n열린 포지션 없음")
    else:
        lines.append("\n열린 포지션:")
        for sym, x in positions.items():
            side = "롱" if x.get("side") == "long" else "숏"
            lines.append("%s %s (%s) 진입 %s | 현재가 %s | SL %s | TP %s | 미실현 %+.2f USDT" %
                (sym, side, x.get("tf", ""), fmt_p(x.get("entry", 0)), fmt_p(x.get("last", x.get("entry", 0))),
                 fmt_p(x.get("sl", 0)), fmt_p(x.get("tp", 0)), float(x.get("upnl", 0))))
    lines.append("\n※ 가상 잔고·손익이며 수수료/펀딩비는 제외합니다.")
    return "\n".join(lines)


# 카드형 현황 이미지용 5x7 영문 비트맵 폰트 (외부 이미지 라이브러리 불필요)
PAPER_FONT = {
    "A": ["01110","10001","10001","11111","10001","10001","10001"],
    "B": ["11110","10001","10001","11110","10001","10001","11110"],
    "C": ["01111","10000","10000","10000","10000","10000","01111"],
    "D": ["11110","10001","10001","10001","10001","10001","11110"],
    "E": ["11111","10000","10000","11110","10000","10000","11111"],
    "F": ["11111","10000","10000","11110","10000","10000","10000"],
    "G": ["01111","10000","10000","10111","10001","10001","01111"],
    "H": ["10001","10001","10001","11111","10001","10001","10001"],
    "I": ["01110","00100","00100","00100","00100","00100","01110"],
    "J": ["00111","00010","00010","00010","10010","10010","01100"],
    "K": ["10001","10010","10100","11000","10100","10010","10001"],
    "L": ["10000","10000","10000","10000","10000","10000","11111"],
    "M": ["10001","11011","10101","10101","10001","10001","10001"],
    "N": ["10001","11001","10101","10011","10001","10001","10001"],
    "O": ["01110","10001","10001","10001","10001","10001","01110"],
    "P": ["11110","10001","10001","11110","10000","10000","10000"],
    "Q": ["01110","10001","10001","10001","10101","10010","01101"],
    "R": ["11110","10001","10001","11110","10100","10010","10001"],
    "S": ["01111","10000","10000","01110","00001","00001","11110"],
    "T": ["11111","00100","00100","00100","00100","00100","00100"],
    "U": ["10001","10001","10001","10001","10001","10001","01110"],
    "V": ["10001","10001","10001","10001","10001","01010","00100"],
    "W": ["10001","10001","10001","10101","10101","10101","01010"],
    "X": ["10001","10001","01010","00100","01010","10001","10001"],
    "Y": ["10001","10001","01010","00100","00100","00100","00100"],
    "Z": ["11111","00001","00010","00100","01000","10000","11111"],
    "/": ["00001","00010","00010","00100","01000","01000","10000"],
    "%": ["11001","11010","00100","01000","10110","00110","00000"],
    "|": ["00100","00100","00100","00100","00100","00100","00100"],
}
for _ch, _pat in FONT_5X7.items():
    PAPER_FONT.setdefault(_ch, _pat)


def paper_status_image(p):
    """태블릿 화면에 맞춘 컴팩트 카드 PNG를 생성한다."""
    try:
        from PIL import Image, ImageDraw, ImageFont
        from io import BytesIO
    except ImportError as e:
        raise RuntimeError("현황 이미지 폰트 렌더링에는 Pillow가 필요합니다: pip install pillow") from e

    positions = list((p.get("pos") or {}).items())
    initial = float(p.get("init_bud", 1000.0))
    balance = float(p.get("bal", initial))
    realized = balance - initial
    unrealized = sum(float(x.get("upnl", 0)) for _, x in positions)
    # 태블릿 텔레그램 화면에 맞춰 기존 레이아웃을 약 18% 축소해
    # 글자와 카드 간격, 바깥 여백을 함께 줄인다.
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
    txt(42,27,"PAPER TRADING",WHITE,34,True)
    txt(43,76,"LIVE STATUS  /  NO REAL ORDERS",MUTED,20)
    rect((42,126,W-42,128),LINE)
    rect((42,153,W-42,355),PANEL,22); rect((42,153,51,355),BLUE)
    txt(72,174,"TOTAL BALANCE",MUTED,21,True)
    txt(72,210,f"{balance:,.2f} USDT",WHITE,54,True)
    txt(72,294,"REALIZED P&L",MUTED,18,True)
    txt(72,321,f"{realized:+,.2f} USDT",GREEN if realized>=0 else RED,26,True)
    rect((510,291,512,339),LINE)
    txt(548,294,"UNREALIZED P&L",MUTED,18,True)
    txt(548,321,f"{unrealized:+,.2f} USDT",GREEN if unrealized>=0 else RED,26,True)
    txt(48,385,"LEVERAGE",MUTED,18,True); txt(48,412,f"{p.get('lev',5)}x",WHITE,27,True)
    txt(340,385,"MARGIN ALLOCATION",MUTED,18,True); txt(340,412,f"{float(p.get('alloc',.2))*100:.0f}%",WHITE,27,True)
    txt(690,385,"TARGET R:R",MUTED,18,True); txt(690,412,f"1:{float(p.get('rr',2.0)):.1f}",WHITE,27,True)
    txt(44,468,f"OPEN POSITIONS  ({len(positions)})",BLUE,23,True)
    y=510
    if not positions:
        rect((42,y,W-42,y+150),PANEL,20); txt(72,y+47,"NO OPEN POSITIONS",MUTED,28,True)
    else:
        for sym,x in positions[:8]:
            pnl=float(x.get("upnl",0)); is_long=x.get("side")=="long"; accent=GREEN if is_long else RED
            rect((42,y,W-42,y+196),PANEL,20); rect((42,y,50,y+196),accent)
            txt(72,y+17,sym,WHITE,28,True)
            txt(72,y+58,("LONG" if is_long else "SHORT")+"  /  "+str(x.get("tf","")).upper(),accent,20,True)
            txt(72,y+106,"ENTRY  "+fmt_p(float(x.get("entry",0))),MUTED,17)
            txt(72,y+143,"NOW    "+fmt_p(float(x.get("last",x.get("entry",0)))),WHITE,17,True)
            txt(540,y+17,"UNREALIZED P&L",MUTED,17,True)
            txt(540,y+48,f"{pnl:+,.2f} USDT",GREEN if pnl>=0 else RED,27,True)
            txt(540,y+106,"SL  "+fmt_p(float(x.get("sl",0))),RED,17)
            txt(540,y+143,"TP  "+fmt_p(float(x.get("tp",0))),GREEN,17)
            y+=222
    fy=H-62; rect((42,fy-18,W-42,fy-16),LINE)
    txt(44,fy,"VIRTUAL P&L  /  FEES AND FUNDING EXCLUDED",MUTED,16)
    out=BytesIO(); im.save(out,format="PNG",optimize=True); return out.getvalue()


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
    # 이미지 생성 단계에서 예외가 나도 현황 버튼이 무반응처럼 보이지 않게 텍스트로 대체한다.
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
        lines.append("%s %s %s | 진입 %s → 청산 %s | 손익 %+.2f USDT (%s)" %
            (x.get("time", ""), x.get("symbol", ""), "롱" if x.get("side") == "long" else "숏",
             fmt_p(x.get("entry", 0)), fmt_p(x.get("exit", 0)), float(x.get("pnl", 0)), x.get("reason", "청산")))
    return "\n".join(lines)


def paper_close_position(p, symbol, price, reason):
    x = p.get("pos", {}).pop(symbol, None)
    if not x:
        return None
    direction = 1 if x.get("side") == "long" else -1
    pnl = (float(price) - float(x["entry"])) * float(x["qty"]) * direction
    p["bal"] = float(p.get("bal", p.get("init_bud", 1000.0))) + pnl
    record = {"symbol": symbol, "side": x["side"], "tf": x.get("tf", ""),
              "entry": x["entry"], "exit": float(price), "pnl": pnl,
              "reason": reason, "time": datetime.now(KST).strftime("%m/%d %H:%M:%S")}
    p.setdefault("hist", []).append(record)
    p["hist"] = p["hist"][-100:]
    save_paper(p)
    send_paper_msg("🏁 가상 포지션 청산: %s %s\n사유: %s\n진입 %s → 청산 %s\n손익: %+.2f USDT\n잔고: %.2f USDT" %
        (symbol, "롱" if x["side"] == "long" else "숏", reason, fmt_p(x["entry"]), fmt_p(price), pnl, p["bal"]), p, True)
    return record


def paper_open_position(symbol, tf, side, price, signal_key):
    p = load_paper()
    if not p.get("on", True) or price <= 0:
        return
    if symbol not in PAPER_ALLOC:
        return
    seen = p.setdefault("seen", [])
    if signal_key in seen:
        return
    existing = p.get("pos", {}).get(symbol)
    if existing and existing.get("side") == side:
        seen.append(signal_key); p["seen"] = seen[-500:]; save_paper(p)
        return
    if existing:
        paper_close_position(p, symbol, price, "반대 신호")
        p = load_paper()
    balance = float(p.get("bal", 1000.0))
    margin = max(0.0, balance * float(PAPER_ALLOC[symbol]))
    notional = margin * max(1.0, float(p.get("lev", 5)))
    if notional <= 0:
        return
    risk = 0.005
    direction = 1 if side == "long" else -1
    sl = price * (1 - risk) if direction == 1 else price * (1 + risk)
    tp = price * (1 + risk * float(p.get("rr", 2.0))) if direction == 1 else price * (1 - risk * float(p.get("rr", 2.0)))
    pos = {"symbol": symbol, "tf": tf, "side": side, "entry": float(price), "last": float(price),
           "qty": notional / price, "margin": margin, "sl": sl, "tp": tp,
           "upnl": 0.0, "time": datetime.now(KST).strftime("%m/%d %H:%M:%S")}
    p.setdefault("pos", {})[symbol] = pos
    seen.append(signal_key); p["seen"] = seen[-500:]
    save_paper(p)
    send_paper_msg("🧪 자동 가상매매 진입\n%s %s (%s)\n진입가: %s\n가상수량: %.6f\n포지션 규모(명목가치): %.2f USDT\n투입 증거금: %.2f USDT · 레버리지 %sx\n손절: %s\n익절: %s\n현재 잔고: %.2f USDT\n※ 실제 주문 아님" %
        (symbol, "롱" if side == "long" else "숏", tf.upper(), fmt_p(price), pos["qty"], notional, margin,
         p.get("lev", 5), fmt_p(sl), fmt_p(tp), balance), p, True)


def update_paper_positions():
    p = load_paper()
    if not p.get("pos"):
        return
    for symbol in list(p["pos"].keys()):
        try:
            p = load_paper()
            x = p.get("pos", {}).get(symbol)
            if not x:
                continue
            candles = get_candles(symbol, "1m", limit=2)
            price = float(candles[-1]["c"])
            x["last"] = price
            direction = 1 if x.get("side") == "long" else -1
            x["upnl"] = (price - float(x["entry"])) * float(x["qty"]) * direction
            reason = None
            if direction == 1 and price <= float(x["sl"]): reason = "손절(SL)"
            elif direction == 1 and price >= float(x["tp"]): reason = "익절(TP)"
            elif direction == -1 and price >= float(x["sl"]): reason = "손절(SL)"
            elif direction == -1 and price <= float(x["tp"]): reason = "익절(TP)"
            if reason:
                paper_close_position(p, symbol, price, reason)
            else:
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
        p["bal"] = float(p.get("init_bud", 1000.0))
        p["seen"] = []
        save_paper(p)
        send_paper_status(p, "가상매매 잔고와 내역을 초기화했습니다")


def handle_paper_updates():
    p = load_paper()
    if not p.get("token"):
        return
    try:
        r = paper_tg(p, "getUpdates", timeout=8,
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
                    elif cmd in ("/hist", "/내역"):
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


def send_photo(png, caption, keyboard=True, chart_tf=None):
    """차트 우측 하단에 실제 시간봉을 표시하고 최근15봉 버튼도 같은 시간봉으로 설정한다."""
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not os.environ.get("TELEGRAM_TOKEN") or not chat_id:
        print("[텔레그램 설정 없음]\n" + caption)
        return

    # 시간봉 라벨은 차트 이미지 자체에 그려 기존 차트 전송 경로에서도 항상 보이게 한다.
    photo = png
    if chart_tf in ALLOWED_TF:
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
                    if button.get("callback_data", "").startswith("c15:"):
                        button["text"] = "🕯 최근15봉 (%s)" % chart_tf.upper()
                        button["callback_data"] = "c15:%s" % chart_tf
        data["reply_markup"] = json.dumps(markup, ensure_ascii=False)
    try:
        tg("sendPhoto", data=data,
           files={"photo": ("chart.png", photo, "image/png")}).raise_for_status()
    except Exception as e:
        print("사진 전송 실패, 글자로 대신 보냄:", e)
        send_telegram(caption, keyboard=keyboard)


def trend_read(candles, ser):
    """EMA 배열·기울기·현재가 위치로 보는 규칙 기반 추세 판단"""
    price = candles[-1]["c"]
    e7, e25, e99 = ser[7][-1], ser[25][-1], ser[99][-1]
    k = min(10, len(candles) - 1)
    slope = (ser[25][-1] / ser[25][-1 - k] - 1) * 100
    sl = 1 if slope > 0.02 else (-1 if slope < -0.02 else 0)
    checks = [1 if price > e7 else -1, 1 if e7 > e25 else -1, 1 if e25 > e99 else -1,
              sl, 1 if price > e99 else -1]
    score = sum(checks)  # -5 ~ +5
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


def trend_short(candles, ser, show_fib=True):
    t = trend_read(candles, ser)
    base = "%s 추세: %s (%+d/5)" % (t["icon"], t["label"], t["score"])
    if show_fib:
        fib = calc_fib_info(candles, FULL_N)
        if fib and fib["retracing"] and fib["in_zone"]:
            base += " · 🎯골든존(0.382~0.618)"
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
    """1번째 사진: 전체(FULL_N봉) 차트 / 2번째 사진: 최근 ZOOM_N봉 피보나치 확대 차트(설정에서 끄기 가능)
    사진은 각각 따로 전송하며, 하단 메뉴 버튼은 마지막으로 보내는 사진에 붙인다."""
    zoom = cfg.get("zoom_on", True)
    show_fib = cfg.get("fib_on", True)
    cap1 = "%s\n[1번] 전체 차트 (%d봉) · 현재가 %s\n%s" % (
        head, FULL_N, "{:,.2f}".format(s["price"]),
        trend_short(s["candles"], s["ser"], show_fib))
    send_photo(draw_chart(s["candles"], s["ser"], hi, N=FULL_N, show_fib=show_fib), cap1, keyboard=not zoom, chart_tf=tf)
    if not zoom:
        return
    try:
        cap2 = "🔍 %s %s [2번] 최근 %d봉 확대 (피보나치 정밀) · 현재가 %s" % (
            sym, tf.upper(), ZOOM_N, "{:,.2f}".format(s["price"]))
        zpng = draw_chart(s["candles"], s["ser"], hi, N=ZOOM_N, show_fib=True,
                          tag="ZOOM %d" % ZOOM_N)
        send_photo(zpng, cap2, chart_tf=tf)
    except Exception as ex:
        print("확대 차트 생성 실패:", ex)
        send_telegram("🔍 %s %s 확대 차트를 만들지 못했어요." % (sym, tf.upper()))


def send_chart_15(sym, tf, cfg):
    """선택한 시간봉(tf)의 최근 15개 봉을 분석·표시한다. 15분봉으로 고정하지 않는다."""
    s = summarize(sym, tf, cfg)
    if not s:
        send_telegram("%s %s 데이터가 부족해요." % (sym, tf.upper()))
        return
    show_fib = cfg.get("fib_on", True)
    png = draw_chart(s["candles"], s["ser"], N=15, show_fib=show_fib, tag="LAST 15")
    caption = "🕯 %s %s · 해당 시간봉 최근 15개 봉 분석 · 현재가 %s\n%s" % (
        sym, tf.upper(), "{:,.2f}".format(s["price"]),
        trend_short(s["candles"], s["ser"], show_fib))
    send_photo(png, caption, keyboard=True, chart_tf=tf)


def send_chart(sym, tf, cfg, head=None, hi=None):
    s = summarize(sym, tf, cfg)
    if not s:
        send_telegram("%s %s 데이터가 부족해요." % (sym, tf))
        return
    send_chart_pair(s, sym, tf, cfg, head or ("📈 %s %s (선물)" % (sym, tf.upper())), hi)


# ---------------- 5분봉 급변·거래량 급증 감지 ----------------
surge_alerted = {}

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
            strength = "🚨 거래량 동반 급변" if vol_ratio >= volume_mult else "⚡ 가격 급변"
            candles_for_trend = candles[:-1] + [dict(live)]
            closes = [c["c"] for c in candles_for_trend]
            ser = {n: ema_series(closes, n) for n in EMA_LIST}
            trend = trend_read(candles_for_trend, ser)
            msg = (
                "%s | %s %s\n"
                "5분봉 시가 대비: %+.2f%% (%s)\n"
                "현재가: %s\n"
                "거래량: 직전 20개 마감봉 평균의 %.2f배\n"
                "%s · EMA 배열 %s (%+d/5)\n"
                "※ 진행 중인 봉이라 변동률·거래량은 마감 전 바뀔 수 있어요."
            ) % (strength, sym, side, change, side, "{:,.4f}".format(live["c"]),
                 vol_ratio, trend["label"], trend["align"], trend["score"])
            send_telegram(msg)
        except Exception as e:
            print("[%s 5m 급변 감지] 오류: %s" % (sym, e))
    if len(surge_alerted) > 2000:
        for old_k in list(surge_alerted.keys())[:1000]:
            surge_alerted.pop(old_k, None)


# ---------------- 알림 ----------------
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
                if rep:
                    title = "🔁🟢 반복 터치 후 다시 반등" if up else "🔁🔴 반복 터치 후 다시 하락"
                    body = ("최근 %d개 15분봉(약 %.1f시간) 동안 EMA7을 %d번 터치했고,\n"
                            "이번에도 %s 중이에요. → %s"
                            % (cfg["rep_window"], cfg["rep_window"] * 0.25, e["touches_prev"],
                               "위로 올라가는" if up else "아래로 내려가는",
                               "롱 우세" if up else "숏 우세"))
                else:
                    count = e["longs"] if up else e["shorts"]
                    if count < cfg["min_count"]:
                        continue
                    title = "🟢 롱 우세" if up else "🔴 숏 우세"
                    body = ("%s이 EMA%d에 닿고 %s 중이에요.\n최근 %s 같은 신호 %d번째"
                            % (TF_LABEL[tf], n, "위로 올라가는" if up else "아래로 내려가는",
                               LOOK_LABEL[tf], count))
                paper_open_position(sym, tf, side, float(s["price"]), "%s|%s|%s|%s|%s|%s" % (sym, tf, n, s["t"], side, int(rep)))
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
        for tf in tfs:
            try:
                s = summarize(sym, tf, cfg)
            except Exception:
                rows.append("%s 조회 실패" % tf.upper())
                continue
            if not s:
                continue
            head = "{:,.2f}".format(s["price"])
            parts = []
            for n, e in s["emas"].items():
                mark = "🟢" if e["side"] == "long" else ("🔴" if e["side"] == "short" else "")
                parts.append("E%d %+.2f%%%s" % (n, e["diff"], mark))
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
    rows.append([{"text": tick(cfg.get("fib_on", True)) + "피보나치(0.382/0.618) 차트 표시", "callback_data": "f:1"}])
    rows.append([{"text": tick(cfg.get("zoom_on", True)) + "최근 %d봉 피보나치 확대 차트(2번째 사진)" % ZOOM_N, "callback_data": "z:1"}])
    rows.append([{"text": "🔙 메인 메뉴 버튼 보기", "callback_data": "act:menu"}])
    return {"inline_keyboard": rows}


def settings_text(cfg):
    return (
        "⚙️ 설정 (%s)\n버튼을 눌러 알림과 차트 기능을 켜고(🔔) 끄세요(🔕)\n"
        "· 종목 / 봉 / EMA / 5분 급변 알림 / 피보나치 작도 / 확대 차트\n\n"
        "글자로 바꾸는 것\n"
        "종목추가 XRP  (또는 XRPUSDT)\n종목삭제 XRP  (또는 XRPUSDT)\n횟수 %d  (같은 신호 최소 횟수)\n"
        "15분터치 %d  (반복터치 알림에 필요한 이전 터치 수)\n"
        "15분범위 %d  (반복터치를 볼 15분봉 개수)\n"
        "업데이트주소 https://github.com/hoho1556/alertbot\n"
        "급변기준 0.7 (5분봉 시가 대비 %%)\n거래량배수 2.5 (직전 20개 마감봉 평균 대비)\n"
        "현재 급변 설정: %s | 피보나치: %s | 확대 차트: %s\n"
        % (VERSION, cfg["min_count"], cfg["rep_touch_min"], cfg["rep_window"],
           "켜짐" if cfg.get("surge_on", True) else "꺼짐",
           "켜짐" if cfg.get("fib_on", True) else "꺼짐",
           "켜짐" if cfg.get("zoom_on", True) else "꺼짐")
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
    send_telegram("✅ 새 코드를 받았어요. 다시 시작합니다...")
    confirm_updates()
    os.execv(sys.executable, [sys.executable] + sys.argv)


# ---------------- 메시지/버튼 처리 ----------------
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
    """텔레그램 메시지에서 코드만 추출하고 코드블록 표시/CRLF를 정리"""
    raw = raw.replace("\r\n", "\n").replace("\r", "\n")
    first, _, rest = raw.partition("\n")
    code = rest if rest.strip() else first[len("패치"):]
    lines = code.splitlines()
    # ```python 또는 ```py 같은 시작 표시와 닫는 ``` 제거
    if lines and lines[0].strip().startswith("```"):
        lines = lines[1:]
    if lines and lines[-1].strip().startswith("```"):
        lines = lines[:-1]
    return "\n".join(lines).strip() + "\n" if lines else ""


def _patch_normalize(code):
    """휴대폰 키보드가 바꿔 넣는 둥근 따옴표/특수 공백을 일반 문자로 되돌림"""
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
    """패치 코드에서 최상위 함수/변수 조각을 {이름: 소스} 로 뽑는다. (조각 dict, 무시한 줄 개수)"""
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
    """새 파일 내용 검사: 문법 -> 별도 프로세스에서 불러오기(봇은 실행하지 않음). 문제 없으면 None"""
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
    """텔레그램으로 받은 함수/변수 조각을 현재 봇 파일에 반영하고 재시작"""
    import ast
    code = _patch_extract_code(raw)
    if not code.strip():
        send_telegram(PATCH_HELP)
        return
    # 스마트 따옴표/특수 공백은 파싱 전에 먼저 정리해 불필요한 문법 오류를 줄임
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
    send_telegram("✅ 패치 완료 (%s)\n봇을 재시작합니다... 되돌리려면 '패치취소'" % " / ".join(parts), keyboard=False)
    confirm_updates()
    os.execv(sys.executable, [sys.executable] + sys.argv)


def rollback_patch():
    """직전 패치/업데이트 전 파일(.bak)로 되돌리고 재시작"""
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
    send_telegram("↩️ 직전 파일로 되돌렸어요. 봇을 재시작합니다...", keyboard=False)
    confirm_updates()
    os.execv(sys.executable, [sys.executable] + sys.argv)


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
    if w in ("종목추가", "종목삭제", "횟수", "15분터치", "15분범위", "업데이트주소", "급변기준", "거래량배수"):
        send_telegram(edit_setting(cfg, w, words[1:]))
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
        else:
            send_chart(sym, tf, cfg)
    elif "차트" in t:
        send_telegram("어떤 봉 차트를 볼까요? (켜져 있는 종목 전부)", markup=chart_markup())
    elif "현황" in t or w.lower() == "status":
        send_status(cfg)
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
    kind, _, val = (cq.get("data") or "").partition(":")
    msg = cq.get("message") or {}
    if kind == "ct":
        for sym in active_symbols(cfg):
            try:
                send_chart(sym, val, cfg)
            except Exception as e:
                send_telegram("%s 차트 실패: %s" % (sym, e))
        return
    if kind == "c15":
        # 버튼 데이터가 구버전(예: c15:15m)으로 남아 있어도, 누른 원본 차트 캡션의
        # 시간봉(예: ETHUSDT 4H [2번])을 우선 사용해 4H 차트에서 15M으로 잘못 바뀌지 않게 한다.
        caption_src = str(msg.get("caption") or "")
        tf_match = re.search(r"\b(5M|15M|1H|4H|12H|1D|1W)\b", caption_src.upper())
        caption_tf = {
            "5M": "5m", "15M": "15m", "1H": "1h", "4H": "4h",
            "12H": "12h", "1D": "1d", "1W": "1w"
        }.get(tf_match.group(1)) if tf_match else None
        tf = caption_tf or (val if val in ALLOWED_TF else "15m")
        for sym in active_symbols(cfg):
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
            send_telegram("📌 메인 메뉴입니다. 원하는 시간봉이나 기능을 선택하세요.")
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
        # 롱폴링은 최대 wait초 동안 응답을 붙잡고 있으므로, 요청 타임아웃은 그보다 넉넉히 길게 잡는다
        r = tg("getUpdates", timeout=wait + 15, params={"offset": update_offset[0], "timeout": wait,
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
        pass  # 일시적인 응답 지연: 조용히 다음 확인으로 넘어감
    except Exception as e:
        print("업데이트 확인 오류:", e)
        time.sleep(5)


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
    cfg = load_cfg()
    print("실시간 감시 시작:", ", ".join(active_symbols(cfg)), "/", ", ".join(active_tfs(cfg)))
    paper = load_paper()
    print("가상매매 봇:", "토큰 설정됨" if paper.get("token") else "토큰 미설정 (~/paper_config.json 확인)")
    send_telegram("🧹 기존 하단 키보드를 숨기고 자판이 올라오지 않는 인라인 버튼 모드로 전환합니다.", markup=REMOVE_KEYBOARD)
    send_telegram(
        "🚀 알림봇 시작!\n"
        "버전: %s\n"
        "파일: %s\n"
        "기능: 대형 고해상도 차트 + 피보나치 + 봉 마감 브리핑 + 5분 급변 감지\n"
        "두 번째 봇은 자동 가상매매 전용이며 실제 주문을 보내지 않습니다.\n"
        "시간봉 버튼을 눌러도 키보드 자판이 올라오지 않습니다." % (VERSION, VERSION_FILE)
    )
    while True:
        cfg = load_cfg()
        try:
            check_sudden_moves(cfg)
            check_all(cfg)
        except Exception as e:
            print("감시 오류:", e)
        update_paper_positions()
        handle_paper_updates()
        handle_updates(POLL_SECONDS, cfg)


PAPER_ALLOC = {"BTCUSDT": 0.5, "ETHUSDT": 0.5}


def check_closed(s, sym, tf, cfg):
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
    candle_icon = "🟢" if close_price >= closed["o"] else "🔴"
    secs = {"1h": 3600000, "4h": 14400000, "12h": 43200000, "1d": 86400000}[tf]
    close_time = datetime.fromtimestamp((closed["t"] + secs) / 1000, KST).strftime("%m/%d %H:%M")
    brief = (
        "🕯️ %s 마감 브리핑 | %s %s\n"
        "마감: %s KST\n"
        "%s 종가: %s (%+.2f%%)\n"
        "%s 추세 (%+d/5) · EMA 배열: %s\n"
        "EMA7 %s / EMA25 %s / EMA99 %s\n"
        "※ 마감 기준 참고용 요약이며 매매 신호 보장은 없어요."
    ) % (
        TF_LABEL[tf], sym, tf.upper(), close_time, candle_icon,
        "{:,.2f}".format(close_price), change,
        trend["icon"], trend["score"], trend["align"],
        "{:,.2f}".format(trend["e7"]),
        "{:,.2f}".format(trend["e25"]),
        "{:,.2f}".format(trend["e99"])
    )
    try:
        png = draw_chart(closed_candles, closed_ser, N=FULL_N,
                         show_fib=cfg.get("fib_on", True))
        send_photo(png, brief, keyboard=True, chart_tf=tf)
    except Exception as ex:
        print("마감 차트 생성 실패:", ex)
        send_telegram(brief)


if __name__ == "__main__":
    main()
