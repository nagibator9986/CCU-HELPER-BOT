# main.py
# -*- coding: utf-8 -*-
"""
Телеграм-бот приёмной комиссии Колледжа Каспийского университета.
Один файл: aiogram v3 + SQLite + OpenAI + ВНУТРЕННЯЯ БАЗА ЗНАНИЙ.

Установка:
  pip install aiogram==3.* openai python-dotenv

.env:
  BOT_TOKEN=...
  OPENAI_API_KEY=...
  ADMIN_IDS=111111111,222222222
  OPENAI_CONTEXT_MODE=all   # all | topk | none
"""

import os
import re
import csv
import sqlite3
import difflib
from datetime import datetime, timedelta, time
from zoneinfo import ZoneInfo
from typing import List, Dict, Any, Optional, Tuple

from dotenv import load_dotenv
from aiogram import Bot, Dispatcher, Router, F
from aiogram.enums import ParseMode
from aiogram.client.default import DefaultBotProperties
from aiogram.filters import CommandStart, Command
from aiogram.filters.command import CommandObject
from aiogram.types import (
    Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton,
    ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove, FSInputFile
)
from aiogram.fsm.state import StatesGroup, State
from aiogram.fsm.context import FSMContext
from html import escape as html_escape_py

# =========================
# Markdown → plain/HTML utils
# =========================
MD_BOLD = re.compile(r'(\*\*|__)(.*?)\1', re.DOTALL)
MD_ITAL = re.compile(r'(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)')
MD_CODE_FENCE = re.compile(r'```([a-zA-Z0-9_-]+)?\n(.*?)```', re.DOTALL)
MD_CODE_INLINE = re.compile(r'`([^`]+)`')
MD_LINK = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
MD_HEADER = re.compile(r'(?m)^\s{0,3}#{1,6}\s+(.+)$')
MD_BULLET = re.compile(r'(?m)^\s*[-*]\s+')

def strip_markdown_to_plain(s: str) -> str:
    s = MD_CODE_FENCE.sub(lambda m: m.group(2), s)
    s = MD_CODE_INLINE.sub(lambda m: m.group(1), s)
    s = MD_LINK.sub(r'\1 (\2)', s)
    s = MD_BOLD.sub(r'\2', s)
    s = MD_ITAL.sub(r'\1', s)
    s = MD_HEADER.sub(r'\1', s)
    s = MD_BULLET.sub('• ', s)
    s = s.replace('**', '').replace('__', '')
    return s.strip()

# --- Telegram HTML sanitizer ---
ALLOWED_HTML_TAGS = {"b","strong","i","em","u","ins","s","strike","del","code","pre","a","br","tg-spoiler","span"}
_ESC_TAG = re.compile(r"&lt;(/?)([a-zA-Z0-9]+)(\s[^&<>]*)?&gt;")

def sanitize_html_for_telegram(s: str) -> str:
    if not s:
        return ""
    # 1) превратим любые HTML-списки в простой текст
    s = re.sub(r"</?\s*ul\s*>", "", s, flags=re.I)
    s = re.sub(r"<\s*li\s*>", "• ", s, flags=re.I)
    s = re.sub(r"<\s*/\s*li\s*>", "\n", s, flags=re.I)
    # 2) экранируем всё
    s = (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))
    # 3) whitelisted-теги (href у <a>)
    def _restore(m):
        slash, tag, attrs = m.group(1), m.group(2).lower(), m.group(3) or ""
        if tag not in ALLOWED_HTML_TAGS:
            return m.group(0)
        if tag == "a" and slash == "":
            href = re.search(r'href\s*=\s*"([^"]+)"', attrs, flags=re.I)
            href_attr = f' href="{href.group(1)}"' if href else ""
            return f"<a{href_attr}>"
        if tag == "br":
            return "<br>"
        return f"</{tag}>" if slash else f"<{tag}>"
    s = _ESC_TAG.sub(_restore, s)
    s = s.replace("&lt;br/&gt;", "<br>")
    return s

# «Вы/Ваш» с заглавной
_VY_RE = re.compile(
    r"\b(вы|вас|вам|вами|ваш|ваша|ваше|ваши|вашего|вашей|вашему|вашим|вашем|ваших|вашими)\b",
    flags=re.IGNORECASE
)
def formalize_vy(text: str) -> str:
    return _VY_RE.sub(lambda m: m.group(0)[0].upper() + m.group(0)[1:].lower(), text or "")

# ---- OpenAI (новая SDK) ----
try:
    from openai import OpenAI
except Exception:
    OpenAI = None

# =========================
# Конфиг
# =========================
load_dotenv()
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "").strip()
ADMIN_IDS = [int(x.strip()) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()]
OPENAI_CONTEXT_MODE = os.getenv("OPENAI_CONTEXT_MODE", "all").lower()  # all | topk | none

if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN не задан в .env")

TZ = ZoneInfo("Asia/Almaty")
DB_PATH = "admissions_bot.db"
OPENAI_MODEL = "gpt-4o-mini"

# Настройки записи
WORK_DAYS_AHEAD = 14
SLOT_STEP_MIN = 30
DAY_START = time(10, 0)
DAY_END = time(18, 0)
LUNCH_START = time(13, 0)
LUNCH_END = time(14, 0)

# =========================
# Базовая карточка колледжа (обновлено)
# =========================
COLLEGE = {
    "name": "Колледж Каспийского университета",
    "city": "Алматы",
    "address": "г. Алматы, проспект Сейфуллина, 521 (уг. ул. Айтеке би) https://2gis.kz/almaty?m=76.941783%2C43.261981%2F18.95%2Fr%2F0.6 ",
    "phones": ["+7 (727) 279 3777", "+7 706 430 84 61"],
    "email": "college.kou@gmail.com",
    "website": "https://ccu.edu.kz",
    "work_hours": "Пн–Пт 09:00–17:00, обед 13:00–14:00",
    "map_link": "https://2gis.kz/almaty?m=76.941783%2C43.261981%2F18.95%2Fr%2F0.6",
    "socials": "@college.caspian"  # Instagram/Facebook/TikTok
}

CONTACTS_TEMPLATE = f"""
<b>Контакты приёмной комиссии</b>
{COLLEGE['name']}
Адрес: {COLLEGE['address']}
Тел.: {', '.join(COLLEGE['phones'])}
E-mail: {COLLEGE['email']}
Сайт: {COLLEGE['website']}
Instagram/Facebook/TikTok: {COLLEGE['socials']}
Часы работы: {COLLEGE['work_hours']}
Карта (2ГИС): {COLLEGE['map_link']}
""".strip()

# =========================
# База знаний (обновлённые куски)
# =========================
KB_DATA: List[Dict[str, str]] = [

    {
        "title": "Приветственное слово директора",
        "tags": "директор приветствие миссия ценности студент абитуриент",
        "lang": "ru",
        "content": """
Ануаш Жигер Дуйсенбекулы — директор Колледжа Каспийского университета.

Выбор колледжа и профессии — важный шаг. В ККУ перед абитуриентом открываются большие перспективы: обучение по современным программам, научные исследования под руководством опытных преподавателей, участие в молодежных проектах и внедрение идей в реальную жизнь.

Студенты ККУ отличаются высоким уровнем профессиональной подготовки и нестандартным мышлением, что делает их конкурентоспособными на рынке труда. Выпускники работают на крупных предприятиях, в гос- и коммерческих структурах, международных компаниях, образовательных и научных организациях.

В колледже созданы условия не только для профессиональной подготовки, но и для гармоничного развития личности: культура, спорт, общественная жизнь, проекты, открытия, новые знакомства.

Успешное будущее начинается с правильного выбора!
""".strip()
    },

    {
        "title": "Администрация колледжа",
        "tags": "администрация руководство сотрудники отделы заместитель заведующий методист психолог маркетинг библиотека медсестра системный администратор",
        "lang": "mixed",
        "content": """
Администрация и сотрудники:

• СУЛТАНОВ Нурлан Мерленович — Заместитель директора по IT
• БЕРДЕНОВА Гулзира Ешмұратқызы — Заместитель директора по учебной работе
• АКСЁНОВА-ГЯУРОВА Оксана Викторовна — Заместитель директора по воспитательной работе
• ЭРНАЗАРОВА Асель Байбулатовна — Заместитель директора по учебно-методической работе
• НУРДАВЛЕТОВА Лаура Моряковна — Заместитель директора по развитию и профессиональному обучению
• Бастасов Сакен Егеутаевич — Заместитель директора по учебно-производственной работе
• ТОКТАРБАЕВА Айнур Смаиловна — Заведующая учебной частью
• ЕГЕМБЕРДИЕВА Раушан Кизатолдаевна — Методист
• ЦЫГАНКОВА Евгения Викторовна — Методист по английскому языку
• ЕНБАЕВА Рәбина Қобланқызы — Секретарь учебной части
• ӘБДІХАН Айгерім Қанышқызы — Диспетчер учебной части
• НҰРДАНИЯҚЫЗЫ Гүлнұр — Педагог-психолог
• АКМУРЗИНА Акнур Айболовна — И.о. руководителя отдела маркетинга
• Ли Александр Дмитриевич — Специалист отдела маркетинга
• Федорова Янита Сергеевна — Специалист отдела маркетинга
• Әнуарбекова Аяулы Құрманбекқызы — Руководитель бизнес-инкубатора
• Бижігіт Дана — Специалист отдела практики
• Душова Нургуль Кошкинбаевна — Председатель ЦМК специальных дисциплин
• КОЗБЕКОВА Ляззат Джапархановна — Председатель ЦМК общеобразовательных дисциплин
• ТӨЛЕНДІ Әділет Арманұлы — Специалист по ДОТ (SmartNation)
• ОШАКБАЕВА Нургуль Крыкбаевна — Заведующая библиотекой
• ТУГУРОВА Қамаргуль Мухамедказиевна — Медицинская сестра
• Абдуалиев Алмаз Едігеұлы — Системный администратор
""".strip()
    },

    {
        "title": "Студенческие организации",
        "tags": "клубы организации студенты парламент дебаты спорт творчество elevate speak up жаст сарбаз arena мнений caspers art ravens starlight",
        "lang": "mixed",
        "content": """
• Students’ Government — активная студенческая жизнь и коммуникация с администрацией.
• NewCast — команда студентов при отделе маркетинга: профориентация, ДОД, консультации, соцсети.
• Саналы Ұрпақ — культура честности и прозрачности в учебной среде.
• Starlight — творческое объединение (актёрское мастерство, сценическая речь, командная работа).
• Art Ravens — студенческая ивент-организация, мероприятия и декорации.
• On the Scene (OTS) — сценическая организация: танцы, вокал, музыка.
• Elevate — еженедельные квесты и тимбилдинги.
• Speak Up — разговорный клуб английского (при поддержке FLEX).
• Blitz — студенческий спортивный клуб.
• Жас Сарбаз — военно-патриотическая организация.
• Арена Мнений — дебатный клуб.
• Caspers — музыкальное объединение (инструменты, выступления).
""".strip()
    },

    # --- Образовательные программы ---
    {
        "title": "Маркетинг — образовательная программа",
        "tags": "обучение маркетинг 04140100 4S04140103 сроки языки квалификация",
        "lang": "ru",
        "content": """
Шифр: 04140100
Квалификация: 4S04140103 — Маркетолог

Язык обучения: казахский, русский
Сроки:
• На базе 9 классов — 2 года 10 месяцев
• На базе 11 классов — 1 год 10 месяцев
""".strip()
    },
    {
        "title": "Менеджмент — образовательная программа",
        "tags": "обучение менеджмент 04130100 4S04130101 сроки навыки квалификация",
        "lang": "ru",
        "content": """
Шифр: 04130100
Квалификация: 4S04130101 — Менеджер

Язык обучения: казахский, русский
Сроки:
• На базе 9 классов — 2 года 10 месяцев
• На базе 11 классов — 1 год 10 месяцев
""".strip()
    },
    {
        "title": "Правоведение — образовательная программа",
        "tags": "обучение право юрист 04210100 4S04210101 сроки специализации",
        "lang": "ru",
        "content": """
Шифр: 04210100
Квалификация: 4S04210101 — Юрист

Язык обучения: казахский, русский
Сроки:
• На базе 9 классов — 2 года 10 месяцев
• На базе 11 классов — 1 год 10 месяцев
""".strip()
    },
    {
        "title": "Гостиничный бизнес — образовательная программа",
        "tags": "обучение гостиничный бизнес 10130100 4S10130103 отель туризм сроки",
        "lang": "ru",
        "content": """
Шифр: 10130100
Квалификация: 4S10130103 — Оперативный менеджер гостиницы

Язык обучения: казахский, русский
Сроки:
• На базе 9 классов — 2 года 10 месяцев
• На базе 11 классов — 1 год 10 месяцев
""".strip()
    },
    {
        "title": "Туризм — образовательная программа",
        "tags": "обучение туризм 10150100 4S10150104 менеджер по туризму сроки",
        "lang": "ru",
        "content": """
Шифр: 10150100
Квалификация: 4S10150104 — Менеджер по туризму

Язык обучения: казахский, русский
Сроки:
• На базе 9 классов — 2 года 10 месяцев
• На базе 11 классов — 1 год 10 месяцев
""".strip()
    },
    {
        "title": "Переводческое дело — образовательная программа",
        "tags": "обучение переводчик 02310100 4S02310101 языки сроки китайский турецкий",
        "lang": "ru",
        "content": """
Шифр: 02310100
Квалификация: 4S02310101 — Переводчик

Дополнительно: иностранные языки — китайский и турецкий с носителями.
Язык обучения: казахский, русский
Сроки:
• На базе 9 классов — 2 года 10 месяцев
• На базе 11 классов — 1 год 10 месяцев
""".strip()
    },
    {
        "title": "Программное обеспечение — образовательная программа",
        "tags": "обучение программирование 06130100 4S06130103 разработчик сроки",
        "lang": "ru",
        "content": """
Шифр: 06130100
Квалификация: 4S06130103 — Разработчик программного обеспечения

Язык обучения: русский
Сроки:
• На базе 9 класса — 3 года 10 месяцев
• На базе 11 класса — 2 года 10 месяцев
""".strip()
    },

    # --- Контакты, оплата, быстрые сведения ---
    {
        "title": "Контакты, реквизиты, общая информация",
        "tags": "контакты адрес телефоны email сайт реквизиты оплата часы работы карта соцсети вопрос",
        "lang": "ru",
        "content": f"""
Контакты:
Адрес: {COLLEGE['address']}
Телефоны: {', '.join(COLLEGE['phones'])}
E-mail: {COLLEGE['email']}
Сайт: {COLLEGE['website']}
Соцсети: {COLLEGE['socials']}
Часы работы: {COLLEGE['work_hours']}
Карта (2ГИС): {COLLEGE['map_link']}
""".strip()
    },
]

# =========================
# SQLite
# =========================
_conn = sqlite3.connect(DB_PATH, check_same_thread=False)
_conn.execute("PRAGMA journal_mode=WAL")
_conn.execute("PRAGMA foreign_keys=ON")

def init_db():
    cur = _conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS users(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        tg_id INTEGER UNIQUE,
        first_name TEXT,
        last_name TEXT,
        username TEXT,
        created_at TEXT
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS user_profiles(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        tg_id INTEGER UNIQUE,
        full_name TEXT,
        phone TEXT,
        created_at TEXT
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS faq(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        question TEXT,
        answer TEXT,
        tags TEXT
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS bookings(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        full_name TEXT,
        phone TEXT,
        date TEXT,
        time TEXT,
        topic TEXT,
        status TEXT DEFAULT 'confirmed',
        created_at TEXT,
        UNIQUE(date, time),
        FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE SET NULL
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS logs(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        user_text TEXT,
        bot_reply TEXT,
        ts TEXT,
        FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE SET NULL
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS kb(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT,
        tags TEXT,
        content TEXT,
        lang TEXT
    )""")
    _conn.commit()

    # Seed KB once
    cur.execute("SELECT COUNT(*) FROM kb")
    if cur.fetchone()[0] == 0:
        cur.executemany(
            "INSERT INTO kb(title, tags, content, lang) VALUES(?,?,?,?)",
            [(x["title"], x["tags"], x["content"], x["lang"]) for x in KB_DATA]
        )
        _conn.commit()

    # Seed FAQ (обновлённые быстрые ответы)
    cur.execute("SELECT COUNT(*) FROM faq")
    if cur.fetchone()[0] == 0:
        faq_items = [
            ("адрес", f"Наш адрес: {COLLEGE['address']}\nКарта (2ГИС): {COLLEGE['map_link']}"),
            ("контакты телефон whatsapp email соцсети", CONTACTS_TEMPLATE),
            ("график работа часы режим", f"Часы работы: {COLLEGE['work_hours']}"),
            ("программы специальности направления сроки", "Список программ и сроки обучения: /programs"),
            ("стоимость цена оплата", "Стоимость обучения: от 600 000 до 1 000 000 за учебный год."),
            ("документы поступление список", "Полный перечень документов: /docs"),
            ("общежитие", "Сведения об общежитии: кнопка «🏨 Общежитие» в главном меню."),
            ("гранты скидки", "Информация о грантах/скидках: раздел «🎓 Гранты и скидки»."),
            ("как поступить этапы шаги", "Этапы: консультация → подача документов → договор и оплата → зачисление. Запишитесь на консультацию: /book"),
            ("сроки приема приемная кампания дедлайны", "Сроки приёма документов: с 25 июня по 25 августа."),
            ("дни открытых дверей дод", "График ДОД: https://ccu.edu.kz/den-otkrytyx-dverej/"),
        ]
        cur.executemany("INSERT INTO faq(question, answer, tags) VALUES(?,?,?)", faq_items)
        _conn.commit()

def upsert_user(tg_id: int, first: str, last: str, uname: str) -> int:
    cur = _conn.cursor()
    cur.execute("SELECT id FROM users WHERE tg_id=?", (tg_id,))
    row = cur.fetchone()
    if row:
        return row[0]
    cur.execute("INSERT INTO users(tg_id, first_name, last_name, username, created_at) VALUES(?,?,?,?,?)",
                (tg_id, first, last, uname, datetime.now(TZ).isoformat()))
    _conn.commit()
    return cur.lastrowid

def get_profile(tg_id: int) -> Optional[Dict[str, str]]:
    cur = _conn.cursor()
    cur.execute("SELECT full_name, phone FROM user_profiles WHERE tg_id=?", (tg_id,))
    row = cur.fetchone()
    if not row:
        return None
    return {"full_name": row[0] or "", "phone": row[1] or ""}

def save_profile(tg_id: int, full_name: str, phone: str):
    cur = _conn.cursor()
    cur.execute("""
        INSERT INTO user_profiles(tg_id, full_name, phone, created_at)
        VALUES(?,?,?,?)
        ON CONFLICT(tg_id) DO UPDATE SET full_name=excluded.full_name, phone=excluded.phone
    """, (tg_id, full_name, phone, datetime.now(TZ).isoformat()))
    _conn.commit()

def add_log(user_id: Optional[int], user_text: str, bot_reply: str):
    cur = _conn.cursor()
    cur.execute("INSERT INTO logs(user_id, user_text, bot_reply, ts) VALUES(?,?,?,?)",
                (user_id, user_text, bot_reply, datetime.now(TZ).isoformat()))
    _conn.commit()

def last_dialog_for_user(user_id: int, limit: int = 8) -> List[Tuple[str, str]]:
    cur = _conn.cursor()
    cur.execute("SELECT user_text, bot_reply FROM logs WHERE user_id=? ORDER BY id DESC LIMIT ?", (user_id, limit))
    rows = cur.fetchall()
    rows.reverse()
    return rows

def html_escape(text: str) -> str:
    return (text or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

def normalize(s: str) -> str:
    s = s.lower()
    s = re.sub(r"ё", "е", s)
    s = re.sub(r"[^a-zа-я0-9ӘәҒғҚқҢңӨөҰұҮүҺһІі\s]", " ", s, flags=re.IGNORECASE)
    s = re.sub(r"\s+", " ", s).strip()
    return s

def is_kazakh_text(s: str) -> bool:
    return bool(re.search(r"[ӘәҒғҚқҢңӨөҰұҮүҺһІі]", s))

# =========================
# Поиск по FAQ/KB (улучшен роутинг)
# =========================
def search_faq_answer(user_text: str) -> Optional[str]:
    q = normalize(user_text)

    # приоритетные ключевые маршруты
    if re.search(r"общежит", q):
        return ("Общежитие: условия, порядок заселения и стоимость — в разделе «🏨 Общежитие». "
                "Кратко: стоимость 36 000 ₸/мес; адрес — г. Алматы, Суюнбая 66–68; карта: https://go.2gis.com/z3c8o")
    if re.search(r"(скидк|грант)", q):
        return ("Гранты и скидки: гранты по ОП (Гостиничный бизнес, Маркетинг, Менеджмент, Программное обеспечение, Туризм); "
                "скидки — индивидуально по Положению. Подробнее — раздел «🎓 Гранты и скидки» или /book.")
    if re.search(r"(стоим|цена|оплат)", q):
        return "Стоимость обучения: 950 000 ₸ за учебный год."
    if re.search(r"(дод|день открытых двер|открытых дверей)", q):
        return ("Дни открытых дверей: график — https://ccu.edu.kz/den-otkrytyx-dverej/ "
                "Регистрация: https://docs.google.com/forms/d/e/1FAIpQLSfyB6uCrHzA0Dqr8ymlM-KKtAQ2cGNCCE_e7ROVIAeyOYXGig/viewform")
    if re.search(r"(сроки|прием|приём)", q):
        return "Сроки приёма документов: с 25 июня по 25 августа."

    # базовый гибрид: ключевые слова + похожесть по тегам из БД
    cur = _conn.cursor()
    cur.execute("SELECT answer, tags FROM faq")
    best_answer = None
    best_score = -1e9
    q_set = set(q.split())
    for answer, tags in cur.fetchall():
        base = normalize(tags)
        t_set = set(base.split())
        inter = len(q_set & t_set)
        sim = difflib.SequenceMatcher(None, q, base).ratio()
        score = inter * 2.0 + sim
        if score > best_score:
            best_score = score
            best_answer = answer
    return best_answer if best_score >= 0.9 else None

def kb_all() -> List[Dict[str, str]]:
    cur = _conn.cursor()
    cur.execute("SELECT title, tags, content, lang FROM kb")
    rows = cur.fetchall()
    return [{"title": t, "tags": g, "content": c, "lang": l} for t, g, c, l in rows]

def kb_search(query: str, topk: int = 8) -> List[Dict[str, str]]:
    q = normalize(query)
    q_set = set(q.split())
    items = kb_all()
    scored = []
    for it in items:
        text = normalize(it["title"] + " " + it["tags"] + " " + it["content"][:1500])
        t_set = set(text.split())
        inter = len(q_set & t_set)
        sim = difflib.SequenceMatcher(None, q, text[:1000]).ratio()
        score = inter * 1.5 + sim
        scored.append((score, it))
    scored.sort(key=lambda x: x[0], reverse=True)
    return [it for _, it in scored[:topk]]

def build_full_context() -> str:
    blocks = []
    for it in kb_all():
        blocks.append(f"### {it['title']}\n{it['content']}")
    return "\n\n".join(blocks)

def build_topk_context(user_msg: str) -> str:
    picks = kb_search(user_msg, topk=8)
    return "\n\n".join([f"### {it['title']}\n{it['content']}" for it in picks])

# =========================
# OpenAI
# =========================
def make_openai_client() -> Optional["OpenAI"]:
    if not OPENAI_API_KEY or OpenAI is None:
        return None
    try:
        return OpenAI(api_key=OPENAI_API_KEY)
    except Exception:
        return None

def build_system_prompt(lang_hint: Optional[str]) -> str:
    base = [
        f"Ты — дружелюбный ассистент приёмной комиссии {COLLEGE['name']} (Алматы, Казахстан).",
        "Отвечай свободно и понятно, опираясь только на предоставленный контекст знаний (ниже).",
        "Если в контексте нет точных данных по вопросу — так и скажи, предложи консультацию (/book) и укажи контакты.",
        "Не выдумывай даты или цифры, которых нет в контексте; если сообщаешь дату/год — указывай год полностью.",
        f"Контакты: адрес {COLLEGE['address']}, телефоны {', '.join(COLLEGE['phones'])}, e-mail {COLLEGE['email']}, сайт {COLLEGE['website']}.",
        "Если пользователя интересует запись — предложи /book.",
        "",
        "Форматирование: только HTML-теги, поддерживаемые Telegram (<b>, <i>, <u>, <code>, <pre>, <a href>, <br/>).",
        "Запрещён Markdown.",
        "Списки оформляй строками, начинай с символа '• '.",
    ]
    if lang_hint == "kk":
        base.extend([
            "",
            "Тіл саясаты: пайдаланушы қазақша жазса — жауапты қазақ тілінде бер.",
        ])
    return "\n".join(base)

def openai_answer(user_id: int, user_msg: str) -> str:
    client = make_openai_client()
    if not client:
        return "Расширенные ответы ИИ недоступны (нет OPENAI_API_KEY). Могу ответить по FAQ или записать на консультацию (/book)."

    history = last_dialog_for_user(user_id, limit=6)

    if OPENAI_CONTEXT_MODE == "all":
        ctx = build_full_context()
    elif OPENAI_CONTEXT_MODE == "topk":
        ctx = build_topk_context(user_msg)
    else:
        ctx = ""

    lang_hint = "kk" if is_kazakh_text(user_msg) else "ru"
    system_msg = build_system_prompt(lang_hint)

    messages = [{"role": "system", "content": system_msg}]
    if ctx:
        messages.append({"role": "system", "content": f"— Контекст знаний —\n{ctx}"})
    for u, b in history:
        if u:
            messages.append({"role": "user", "content": u})
        if b:
            messages.append({"role": "assistant", "content": b})
    messages.append({"role": "user", "content": user_msg})

    try:
        resp = client.chat.completions.create(
            model=OPENAI_MODEL,
            messages=messages,
            temperature=0.4,
            max_tokens=700,
        )
        return (resp.choices[0].message.content or "").strip()
    except Exception:
        return "Не удалось получить ответ от ИИ. Попробуйте ещё раз или воспользуйтесь /book."

# =========================
# Слоты для брони
# =========================
def time_slots_for_date(dt: datetime) -> List[str]:
    slots = []
    cur = datetime.combine(dt.date(), DAY_START, tzinfo=TZ)
    end_dt = datetime.combine(dt.date(), DAY_END, tzinfo=TZ)
    while cur <= end_dt:
        t = cur.time()
        if not (LUNCH_START <= t < LUNCH_END):
            slots.append(t.strftime("%H:%M"))
        cur += timedelta(minutes=SLOT_STEP_MIN)
    return [s for s in slots if s <= DAY_END.strftime("%H:%M")]

def available_slots(date_str: str) -> List[str]:
    dt = datetime.strptime(date_str, "%Y-%m-%d").replace(tzinfo=TZ)
    all_slots = time_slots_for_date(dt)
    cur = _conn.cursor()
    cur.execute("SELECT time FROM bookings WHERE date=? AND status='confirmed'", (date_str,))
    taken = {r[0] for r in cur.fetchall()}
    return [s for s in all_slots if s not in taken]

def upcoming_dates() -> List[str]:
    today = datetime.now(TZ).date()
    days = []
    for d in range(WORK_DAYS_AHEAD):
        day = today + timedelta(days=d)
        if day.weekday() < 6:  # Пн–Сб
            days.append(day.isoformat())
    return days

def create_booking(user_id: int, full_name: str, phone: str, date_str: str, time_str: str, topic: str) -> Tuple[bool, str]:
    cur = _conn.cursor()
    try:
        cur.execute("""
            INSERT INTO bookings(user_id, full_name, phone, date, time, topic, created_at)
            VALUES(?,?,?,?,?,?,?)
        """, (user_id, full_name, phone, date_str, time_str, topic, datetime.now(TZ).isoformat()))
        _conn.commit()
        return True, "Ваша запись подтверждена ✅"
    except sqlite3.IntegrityError:
        return False, "Этот слот уже занят. Выберите другое время."

def list_bookings_for_user(user_id: int) -> List[Dict[str, Any]]:
    cur = _conn.cursor()
    cur.execute("SELECT date, time, topic, status FROM bookings WHERE user_id=? ORDER BY date, time", (user_id,))
    rows = cur.fetchall()
    return [{"date": d, "time": t, "topic": topic, "status": s} for d, t, topic, s in rows]

def cancel_booking(user_id: int, date_str: str, time_str: str) -> bool:
    cur = _conn.cursor()
    cur.execute("DELETE FROM bookings WHERE user_id=? AND date=? AND time=?", (user_id, date_str, time_str))
    _conn.commit()
    return cur.rowcount > 0

# формат даты для пользователя: дд–мм–гг
def fmt_user_date(date_str: str) -> str:
    try:
        d = datetime.strptime(date_str, "%Y-%m-%d").date()
        return d.strftime("%d–%m–%y")
    except Exception:
        return date_str

# =========================
# UI и FSM
# =========================
class BookingFSM(StatesGroup):
    choosing_date = State()
    choosing_time = State()
    entering_name = State()
    entering_phone = State()
    entering_topic = State()
    confirm = State()

class OnboardingFSM(StatesGroup):
    enter_name = State()
    enter_phone = State()

def main_menu_kb() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="📚 Программы"), KeyboardButton(text="⭐ Преимущества")],
            [KeyboardButton(text="💰 Стоимость"), KeyboardButton(text="🎓 Гранты и скидки")],
            [KeyboardButton(text="🏨 Общежитие"), KeyboardButton(text="📄 Документы")],
            [KeyboardButton(text="📅 Записаться на консультацию"), KeyboardButton(text="📞 Контакты")],
            [KeyboardButton(text="📆 Дни открытых дверей"), KeyboardButton(text="❓ FAQ")],
            [KeyboardButton(text="🗓 Мои записи")],
        ],
        resize_keyboard=True
    )

def dates_inline_kb() -> InlineKeyboardMarkup:
    buttons = [[InlineKeyboardButton(text=datetime.strptime(d, "%Y-%m-%d").strftime("%a %d.%m"),
                                     callback_data=f"pick_date:{d}")]
               for d in upcoming_dates()]
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def times_inline_kb(date_str: str) -> InlineKeyboardMarkup:
    slots = available_slots(date_str)
    if not slots:
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Нет свободных слотов", callback_data="noop")],
            [InlineKeyboardButton(text="⬅️ Назад к датам", callback_data="back_to_dates")]
        ])
    rows = []; row = []
    for s in slots:
        row.append(InlineKeyboardButton(text=s, callback_data=f"pick_time:{date_str}:{s}"))
        if len(row) == 3:
            rows.append(row); row = []
    if row: rows.append(row)
    rows.append([InlineKeyboardButton(text="⬅️ Назад к датам", callback_data="back_to_dates")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def cancel_booking_kb(date_str: str, time_str: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Отменить запись", callback_data=f"cancel:{date_str}:{time_str}")]
    ])

# =========================
# Бот
# =========================
bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp = Dispatcher()
rt = Router()
dp.include_router(rt)

# =========================
# Команды / старт и онбординг
# =========================
@rt.message(CommandStart())
async def cmd_start(m: Message, state: FSMContext):
    upsert_user(m.from_user.id, m.from_user.first_name or "", m.from_user.last_name or "", m.from_user.username or "")
    profile = get_profile(m.from_user.id)

    if not profile or not profile.get("full_name") or not profile.get("phone"):
        await state.clear()
        await state.set_state(OnboardingFSM.enter_name)
        return await m.answer(
            f"Здравствуйте, {html_escape(m.from_user.first_name or 'Гость')}!\n\n"
            f"Я — виртуальный помощник приёмной комиссии <b>Колледжа Каспийского университета</b>.\n\n"
            f"Перед началом диалога укажите, пожалуйста, <b>Ваши ФИО</b> (например: Иванов Иван Иванович):",
            reply_markup=ReplyKeyboardRemove(),
        )

    welcome = (
        "Здравствуйте! Я — виртуальный помощник приёмной комиссии "
        "<b>Колледжа Каспийского университета</b>.\n"
        "• Отвечаю на вопросы о программах и поступлении\n"
        "• Помогаю записаться на консультацию\n"
        "• Даю контакты и список документов\n\n"
        "Чем могу помочь? /help"
    )
    await m.answer(welcome, reply_markup=main_menu_kb())

@rt.message(OnboardingFSM.enter_name)
async def ob_enter_name(m: Message, state: FSMContext):
    full_name = (m.text or "").strip()
    if len(full_name.split()) < 2 or len(full_name) < 5:
        return await m.answer("Пожалуйста, укажите ФИО полностью (например: Иванов Иван Иванович).")
    await state.update_data(full_name=full_name)
    await state.set_state(OnboardingFSM.enter_phone)
    kb = ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📱 Поделиться номером", request_contact=True)]],
        resize_keyboard=True
    )
    await m.answer("Укажите <b>Ваш номер телефона</b> (например: +77001234567) или нажмите кнопку ниже:", reply_markup=kb)

@rt.message(OnboardingFSM.enter_phone)
async def ob_enter_phone(m: Message, state: FSMContext):
    phone = ""
    if getattr(m, "contact", None) and getattr(m.contact, "phone_number", ""):
        phone = m.contact.phone_number
    else:
        phone = re.sub(r"[^\d+]", "", m.text or "")
    if not re.match(r"^\+?\d{10,15}$", phone):
        return await m.answer("Похоже на некорректный номер. Пример: +77001234567")

    data = await state.get_data()
    save_profile(m.from_user.id, data["full_name"], phone)
    await state.clear()

    welcome = (
        "Спасибо! Данные сохранены ✅\n\n"
        "Я — виртуальный помощник приёмной комиссии <b>Колледжа Каспийского университета</b>.\n"
        "• Отвечаю на вопросы о программах и поступлении\n"
        "• Помогаю записаться на консультацию\n"
        "• Даю контакты и список документов\n\n"
        "Чем могу помочь?"
    )
    await m.answer(welcome, reply_markup=main_menu_kb())

@rt.message(Command("help"))
async def cmd_help(m: Message):
    await m.answer(
        "<b>Команды</b>\n"
        "/start — перезапуск и ввод данных\n"
        "/help — помощь\n"
        "/faq — частые вопросы\n"
        "/book — запись на консультацию\n"
        "/mybookings — мои записи\n"
        "/contacts — контакты\n"
        "/programs — программы\n"
        "/docs — список документов\n"
        "/subjects — профильные предметы\n\n"
        "Админ:\n"
        "/list_today — список записей на сегодня\n"
        "/export_today — CSV-выгрузка на сегодня\n"
        "/list 2025-10-30 — список на дату\n"
        "/export 2025-10-30 — CSV на дату"
    )

# =========================
# Публичные разделы
# =========================
@rt.message(Command("contacts"))
async def cmd_contacts(m: Message):
    await m.answer(CONTACTS_TEMPLATE)

@rt.message(Command("programs"))
async def cmd_programs(m: Message):
    await m.answer(
        "<b>Программы и сроки</b>\n"
        "<u>На базе 9 классов:</u>\n"
        "• Менеджмент — 2 года 10 месяцев\n"
        "• Маркетинг — 2 года 10 месяцев\n"
        "• Правоведение — 2 года 10 месяцев\n"
        "• Гостиничный бизнес — 2 года 10 месяцев\n"
        "• Туризм — 2 года 10 месяцев\n"
        "• Переводческое дело — 2 года 10 месяцев\n"
        "• Программное обеспечение — 3 года 10 месяцев\n\n"
        "<u>На базе 11 классов:</u>\n"
        "• Маркетинг — 1 год 10 месяцев\n"
        "• Туризм — 1 год 10 месяцев\n\n"
        "Подробнее: https://ccu.edu.kz/specialnosti/"
    )

@rt.message(Command("docs"))
async def cmd_docs(m: Message):
    await m.answer(
        "<b>Перечень документов для поступления</b>\n"
        "• Заявление;\n"
        "• Документы об образовании (подлинник с дипломом);\n"
        "• Медицинская справка (форма 075У) со снимком флюорографии;\n"
        "• Паспорт здоровья ребёнка, прививочная карта;\n"
        "• 4 фотографии (3×4);\n"
        "• Удостоверение личности или свидетельство о рождении (копия)."
    )

@rt.message(Command("subjects"))
async def cmd_subjects(m: Message):
    await m.answer(
        "<b>Профильные предметы при поступлении</b>\n"
        "<pre>Шифр     Направление                  Квалификация                      Предметы\n"
        "06130100 Программное обеспечение     Разработчик ПО                    1) алгебра; 2) информатика\n"
        "04140100 Маркетинг                   Маркетолог                        1) алгебра; 2) химия\n"
        "10150100 Туризм                      Менеджер по туризму               1) география; 2) иностр. язык\n"
        "10130100 Гостиничный бизнес          Оперативный менеджер гостиницы    1) география; 2) иностр. язык\n"
        "02310100 Переводческое дело          Переводчик                        1) иностр. язык; 2) литература\n"
        "04130100 Менеджмент                  Менеджер                          1) алгебра; 2) информатика\n"
        "04210100 Правоведение                Юрист                             1) основы права; 2) литература</pre>"
    )

@rt.message(Command("faq"))
async def cmd_faq(m: Message):
    await m.answer(
        "<b>Частые вопросы</b>\n"
        "— Адрес и контакты\n— Программы и сроки\n— Документы для поступления\n— Стоимость\n— Общежитие\n— Гранты и скидки\n— Дни открытых дверей\n— Сроки приёма\n\n"
        "Задайте вопрос текстом или воспользуйтесь кнопками."
    )

@rt.message(Command("book"))
async def cmd_book(m: Message, state: FSMContext):
    await state.clear()
    await state.set_state(BookingFSM.choosing_date)
    await m.answer("<b>Выберите дату консультации</b> (ближайшие 2 недели):", reply_markup=dates_inline_kb())

@rt.message(Command("mybookings"))
async def cmd_mybookings(m: Message):
    user_db_id = upsert_user(m.from_user.id, m.from_user.first_name or "", m.from_user.last_name or "", m.from_user.username or "")
    items = list_bookings_for_user(user_db_id)
    if not items:
        await m.answer("У Вас пока нет записей. Используйте /book, чтобы выбрать дату и время.")
        return
    lines = [f"• {fmt_user_date(it['date'])} {it['time']} — {html_escape(it['topic'] or 'консультация')} ({it['status']})" for it in items]
    await m.answer("<b>Мои записи</b>\n" + "\n".join(lines))

# =========================
# Кнопки главного меню
# =========================
@rt.message(F.text == "📚 Программы")
async def btn_programs(m: Message):
    await cmd_programs(m)

@rt.message(F.text == "⭐ Преимущества")
async def btn_advantages(m: Message):
    await m.answer(
        "<b>Почему это выгодно для Вас</b>\n"
        "• Поступление без экзаменов;\n"
        "• Гранты, скидки и гибкая система оплаты;\n"
        "• Активная студенческая жизнь: 14 студенческих организаций и крупные мероприятия;\n"
        "• Практика в крупных компаниях;\n"
        "• Современная материально-техническая база;\n"
        "• Преподаватели-практики, иностранные преподаватели;\n"
        "• Дополнительные языки: английский, китайский, турецкий;\n"
        "• Бесплатные курсы подготовки к IELTS;\n"
        "• Факультативы по специальностям: SMM, мобилография;\n"
        "• Физкультура по секциям: танцы, рисование, шахматы, наст. теннис, нац. игры;\n"
        "• Поступление в Caspian University по сокращённой двухгодичной программе (скидка до 500 000 ₸);\n"
        "• Центр поступления за рубеж (Польша, Кипр, Италия и др.);\n"
        "• Оплачиваемая стажировка в люксовых отелях Турции;\n"
        "• Академическая мобильность по Казахстану и за рубежом;\n"
        "• ENACTUS — международный конкурс бизнес-проектов;\n"
        "• Центр студенческого предпринимательства;\n"
        "• Автошкола в стенах Колледжа;\n"
        "• Волонтёрство в ОФ «NewMan»;\n"
        "• Участие в WorldSkills и хакатонах."
    )

@rt.message(F.text == "💰 Стоимость")
async def btn_tuition(m: Message):
    await m.answer(
        "<b>Стоимость обучения</b>\n"
        "• 950 000 ₸ за учебный год.\n\n"
        "Если Вам нужна детализация по программе/форме — рекомендую записаться на консультацию: /book"
    )

@rt.message(F.text == "📄 Документы")
async def btn_docs(m: Message):
    await cmd_docs(m)

@rt.message(F.text == "🎓 Гранты и скидки")
async def btn_grants(m: Message):
    await m.answer(
        "<b>Гранты и скидки</b>\n"
        "• Гранты предоставляются на ОП: Гостиничный бизнес, Маркетинг, Менеджмент, Программное обеспечение, Туризм.\n"
        "• Скидки предоставляются в индивидуальном порядке, согласно Положению о скидках.\n\n"
        "Если Вам нужна более подробная информация, рекомендую записаться на консультацию (/book) "
        "или обратиться по контактам:\n" + CONTACTS_TEMPLATE
    )

@rt.message(F.text == "🏨 Общежитие")
async def btn_dorm(m: Message):
    await m.answer(
        "<b>Общежитие</b>\n"
        "В общежитии созданы необходимые условия: бытовые комнаты, холодильники, газовые плиты, стиральные машины, "
        "санузлы и душевые кабины в каждой комнате.\n\n"
        "<b>Преимущества:</b>\n"
        "• Комфорт и уют (современный ремонт);\n"
        "• Система безопасности;\n"
        "• Мини-кухни, душевые и санузлы, умывальники на каждом этаже.\n\n"
        "<b>Порядок заселения:</b>\n"
        "• Направление и чек об оплате (выдаются при заключении договора и оплате);\n"
        "• Медицинская справка 075-У (с флюорографией).\n\n"
        "Стоимость: <b>36 000 ₸/мес</b>\n"
        "Адрес: г. Алматы, Суюнбая 66–68\n"
        "Карта: https://go.2gis.com/z3c8o"
    )

@rt.message(F.text == "📞 Контакты")
async def btn_contacts(m: Message):
    await cmd_contacts(m)

@rt.message(F.text == "📆 Дни открытых дверей")
async def btn_dod(m: Message):
    await m.answer(
        "<b>Дни открытых дверей</b>\n"
        "График: https://ccu.edu.kz/den-otkrytyx-dverej/\n"
        "Регистрация: https://docs.google.com/forms/d/e/1FAIpQLSfyB6uCrHzA0Dqr8ymlM-KKtAQ2cGNCCE_e7ROVIAeyOYXGig/viewform"
    )

@rt.message(F.text == "❓ FAQ")
async def btn_faq(m: Message):
    await cmd_faq(m)

@rt.message(F.text == "📅 Записаться на консультацию")
async def btn_book(m: Message, state: FSMContext):
    await cmd_book(m, state)

@rt.message(F.text == "🗓 Мои записи")
async def btn_mybook(m: Message):
    await cmd_mybookings(m)

# =========================
# Админ
# =========================
def is_admin(user_id: int) -> bool:
    return user_id in ADMIN_IDS

def all_bookings_for_date(date_str: str) -> List[Dict[str, Any]]:
    cur = _conn.cursor()
    cur.execute("SELECT full_name, phone, time, topic, status FROM bookings WHERE date=? ORDER BY time", (date_str,))
    rows = cur.fetchall()
    return [{"full_name": n, "phone": p, "time": t, "topic": topic, "status": s} for n, p, t, topic, s in rows]

def _parse_date_arg(s: Optional[str]) -> Optional[str]:
    if not s:
        return None
    s = s.strip()
    try:
        d = datetime.strptime(s, "%Y-%m-%d").date()
        return d.isoformat()
    except ValueError:
        return None

def _format_admin_list_text(date_str: str, items: List[Dict[str, Any]]) -> str:
    if not items:
        return f"На {date_str} записей нет."
    lines = [
        f"{it['time']} — {html_escape(it['full_name'])} ({html_escape(it['phone'])}) — {html_escape(it['topic'])} [{it['status']}]"
        for it in items
    ]
    return "<b>Записи на " + date_str + "</b>\n" + "\n".join(lines)

def _admin_cancel_kb(date_str: str, items: List[Dict[str, Any]]) -> InlineKeyboardMarkup:
    rows = []
    row = []
    for it in items:
        t = it["time"]
        row.append(InlineKeyboardButton(text=f"❌ {t}", callback_data=f"admin_cancel:{date_str}:{t}"))
        if len(row) == 3:
            rows.append(row); row = []
    if row:
        rows.append(row)
    return InlineKeyboardMarkup(inline_keyboard=rows)

def cancel_booking_any(date_str: str, time_str: str) -> bool:
    cur = _conn.cursor()
    cur.execute("DELETE FROM bookings WHERE date=? AND time=?", (date_str, time_str))
    _conn.commit()
    return cur.rowcount > 0

def save_csv_for_date(date_str: str, rows) -> str:
    filename = f"bookings_{date_str}.csv"
    path = os.path.abspath(filename)
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["full_name", "phone", "time", "topic", "status"])
        for r in rows:
            w.writerow([r["full_name"], r["phone"], r["time"], r["topic"], r["status"]])
    return path

@rt.message(Command("export_today"))
async def cmd_export_today(m: Message):
    if not is_admin(m.from_user.id):
        return await m.answer("Команда только для администраторов.")
    date_str = datetime.now(TZ).date().isoformat()
    rows = all_bookings_for_date(date_str)
    if not rows:
        return await m.answer("На сегодня записей нет.")
    path = save_csv_for_date(date_str, rows)
    await m.answer_document(document=FSInputFile(path), caption=f"Выгрузка на {date_str}")

@rt.message(Command("list_today"))
async def cmd_list_today(m: Message):
    if not is_admin(m.from_user.id):
        return await m.answer("Команда только для администраторов.")
    date_str = datetime.now(TZ).date().isoformat()
    items = all_bookings_for_date(date_str)
    if not items:
        return await m.answer("На сегодня записей нет.")
    lines = [f"{it['time']} — {html_escape(it['full_name'])} ({it['phone']}) — {html_escape(it['topic'])} [{it['status']}]"
             for it in items]
    await m.answer("<b>Записи на сегодня</b>\n" + "\n".join(lines))

@rt.message(Command("list"))
async def cmd_list(m: Message, command: CommandObject):
    if not is_admin(m.from_user.id):
        return await m.answer("Команда только для администраторов.")

    arg_date = _parse_date_arg((command.args or "").strip())
    date_str = arg_date or datetime.now(TZ).date().isoformat()

    items = all_bookings_for_date(date_str)
    text = _format_admin_list_text(date_str, items)
    kb = _admin_cancel_kb(date_str, items) if items else None

    await m.answer(text, reply_markup=kb)

@rt.message(Command("export"))
async def cmd_export(m: Message, command: CommandObject):
    if not is_admin(m.from_user.id):
        return await m.answer("Команда только для администраторов.")

    arg_date = _parse_date_arg((command.args or "").strip())
    date_str = arg_date or datetime.now(TZ).date().isoformat()

    data = all_bookings_for_date(date_str)
    if not data:
        return await m.answer(f"На {date_str} записей нет.")

    path = save_csv_for_date(date_str, data)
    await m.answer_document(document=FSInputFile(path), caption=f"Выгрузка на {date_str}")

@rt.callback_query(F.data.startswith("admin_cancel:"))
async def cb_admin_cancel(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        await c.answer("Только для администраторов.", show_alert=True)
        return

    try:
        _, d, t = c.data.split(":", 2)
    except ValueError:
        await c.answer("Некорректные данные.", show_alert=True)
        return

    ok = cancel_booking_any(d, t)
    if not ok:
        await c.answer("Бронь не найдена или уже отменена.", show_alert=True)
    else:
        await c.answer(f"Отменено: {d} {t}")

    items = all_bookings_for_date(d)
    text = _format_admin_list_text(d, items)
    kb = _admin_cancel_kb(d, items) if items else None
    try:
        await c.message.edit_text(text, reply_markup=kb)
    except Exception:
        await c.message.answer(text, reply_markup=kb)

# =========================
# Callback — запись
# =========================
@rt.callback_query(F.data.startswith("pick_date:"))
async def cb_pick_date(c: CallbackQuery, state: FSMContext):
    _, date_str = c.data.split(":", 1)
    await state.update_data(date=date_str)
    await state.set_state(BookingFSM.choosing_time)
    await c.message.edit_text(f"<b>Дата:</b> {fmt_user_date(date_str)}\nВыберите время:", reply_markup=times_inline_kb(date_str))
    await c.answer()

@rt.callback_query(F.data == "back_to_dates")
async def cb_back_dates(c: CallbackQuery, state: FSMContext):
    await state.set_state(BookingFSM.choosing_date)
    await c.message.edit_text("<b>Выберите дату консультации</b> (ближайшие 2 недели):", reply_markup=dates_inline_kb())
    await c.answer()

@rt.callback_query(F.data.startswith("pick_time:"))
async def cb_pick_time(c: CallbackQuery, state: FSMContext):
    _, date_str, time_str = c.data.split(":", 2)
    await state.update_data(time=time_str, date=date_str)

    # Если профиль заполнен — сразу к теме
    prof = get_profile(c.from_user.id)
    if prof and prof.get("full_name") and prof.get("phone"):
        await state.update_data(full_name=prof["full_name"], phone=prof["phone"])
        await state.set_state(BookingFSM.entering_topic)
        await c.message.edit_text(
            f"<b>Дата:</b> {fmt_user_date(date_str)}\n<b>Время:</b> {time_str}\n\n"
            "Кратко опишите тему консультации:"
        )
    else:
        await state.set_state(BookingFSM.entering_name)
        await c.message.edit_text(f"<b>Дата:</b> {fmt_user_date(date_str)}\n<b>Время:</b> {time_str}\n\nВведите Ваши ФИО сообщением:")
    await c.answer()

@rt.callback_query(F.data.startswith("cancel:"))
async def cb_cancel(c: CallbackQuery):
    _, d, t = c.data.split(":", 2)
    user_db_id = upsert_user(c.from_user.id, c.from_user.first_name or "", c.from_user.last_name or "", c.from_user.username or "")
    ok = cancel_booking(user_db_id, d, t)
    await c.message.edit_text("Ваша запись отменена." if ok else "Не удалось отменить (возможно, уже отменена).")
    await c.answer()

# =========================
# FSM шаги бронирования
# =========================
@rt.message(BookingFSM.entering_name)
async def fsm_enter_name(m: Message, state: FSMContext):
    full_name = (m.text or "").strip()
    if len(full_name) < 5:
        await m.answer("Пожалуйста, укажите полное ФИО.")
        return
    await state.update_data(full_name=full_name)
    await state.set_state(BookingFSM.entering_phone)
    await m.answer("Укажите Ваш телефон (например: +77001234567):")

@rt.message(BookingFSM.entering_phone)
async def fsm_enter_phone(m: Message, state: FSMContext):
    phone = re.sub(r"[^\d+]", "", m.text or "")
    if not re.match(r"^\+?\d{10,15}$", phone):
        await m.answer("Похоже на некорректный номер. Пример: +77001234567")
        return
    await state.update_data(phone=phone)
    await state.set_state(BookingFSM.entering_topic)
    await m.answer("Кратко опишите тему консультации:")

@rt.message(BookingFSM.entering_topic)
async def fsm_enter_topic(m: Message, state: FSMContext):
    topic = (m.text or "").strip()
    if len(topic) < 3:
        await m.answer("Нужно хотя бы 3 символа. Уточните тему:")
        return
    await state.update_data(topic=topic)
    data = await state.get_data()
    await state.set_state(BookingFSM.confirm)
    await m.answer(
        "<b>Подтвердите запись</b>\n\n"
        f"Дата: {fmt_user_date(data.get('date'))}\n"
        f"Время: {data.get('time')}\n"
        f"ФИО: {html_escape(data.get('full_name'))}\n"
        f"Телефон: {html_escape(data.get('phone'))}\n"
        f"Тема: {html_escape(data.get('topic'))}\n\n"
        "Напишите <b>Да</b> или <b>Нет</b>."
    )

@rt.message(BookingFSM.confirm)
async def fsm_confirm(m: Message, state: FSMContext):
    ans = (m.text or "").strip().lower()
    if ans in ("да", "yes", "иә"):
        data = await state.get_data()
        user_db_id = upsert_user(m.from_user.id, m.from_user.first_name or "", m.from_user.last_name or "", m.from_user.username or "")
        ok, msg = create_booking(user_db_id, data["full_name"], data["phone"], data["date"], data["time"], data["topic"])
        await m.answer(msg)
        if ok:
            await m.answer("Если планы изменятся — нажмите кнопку, чтобы отменить запись:", reply_markup=cancel_booking_kb(data["date"], data["time"]))
            await state.clear()
        else:
            await state.set_state(BookingFSM.choosing_time)
            await m.answer("Выберите другое время:", reply_markup=times_inline_kb(data["date"]))
    elif ans in ("нет", "no", "жоқ"):
        await state.clear()
        await m.answer("Запись отменена. При необходимости начните заново: /book")
    else:
        await m.answer("Пожалуйста, ответьте «Да» или «Нет» 🙂")

# =========================
# Общий обработчик текста
# =========================
@rt.message(F.text)
async def any_text(m: Message):
    user_db_id = upsert_user(m.from_user.id, m.from_user.first_name or "", m.from_user.last_name or "", m.from_user.username or "")
    q = (m.text or "").strip()

    # 1) FAQ быстрый ответ
    ans = search_faq_answer(q)
    if ans:
        ans = formalize_vy(strip_markdown_to_plain(ans))
        ans = sanitize_html_for_telegram(ans)
        await m.answer(ans); add_log(user_db_id, q, ans); return

    # 2) OpenAI с контекстом
    reply = openai_answer(user_db_id, q)
    reply = formalize_vy(strip_markdown_to_plain(reply))
    reply = sanitize_html_for_telegram(reply)
    if is_kazakh_text(q) and "Расширенные ответы ИИ" in reply:
        reply = "Сұрағыңыз бойынша көмектесемін. Толық ақпарат үшін /book арқылы жазылыңыз немесе байланысқа шығыңыз."
    await m.answer(reply); add_log(user_db_id, q, reply)

# =========================
# Запуск
# =========================
def main():
    init_db()
    print(f"Admissions bot running (Asia/Almaty), OPENAI_CONTEXT_MODE={OPENAI_CONTEXT_MODE}")
    from asyncio import run
    run(Dispatcher.start_polling(dp, bot))

if __name__ == "__main__":
    main()





