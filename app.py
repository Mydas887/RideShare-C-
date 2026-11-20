"""
🚗 RideShare MVP
=================

A simple ride-sharing app for people from the same university, college or workplace.

The most important feature is ROUTE MATCHING:
    A passenger's pickup point is compared against the driver's real road route
    (from OSRM). If the pickup is close to that route, at a compatible time, in the
    same organization, with free seats, the ride is shown as a match with a score.

Run it with:
    pip install -r requirements.txt
    streamlit run app.py

Everything lives in this one file and is split into clearly labelled sections:
    1. Imports
    2. Configuration
    3. Database initialization
    4. Database helper functions
    5. Authentication
    6. Geocoding
    7. Routing
    8. Route matching
    9. Ride / request / message actions (business logic)
   10. Demo data
   11. UI helper functions
   12. Pages
   13. Main application
"""

# =============================================================================
# 1. IMPORTS
# =============================================================================
import hashlib
import json
import math
import re
import secrets
import sqlite3
import time
from datetime import date, datetime, timedelta

import folium
import pandas as pd
import requests
import streamlit as st
from geopy.distance import geodesic
from geopy.exc import GeopyError
from geopy.geocoders import Nominatim
from streamlit_folium import st_folium


# =============================================================================
# 2. CONFIGURATION
# Change these values to tune the app. Everything below reads from here.
# =============================================================================
DB_NAME = "rideshare.db"

# --- Route proximity (how far the pickup may be from the driver's route) ---
MAX_ROUTE_DISTANCE_KM = 5          # Beyond this, the ride is NOT a match
EXCELLENT_ROUTE_DISTANCE_KM = 1    # 0–1 km  -> Excellent
VERY_GOOD_ROUTE_DISTANCE_KM = 2    # 1–2 km  -> Very Good
GOOD_ROUTE_DISTANCE_KM = 3         # 2–3 km  -> Good, 3–5 km -> Weak

# --- Time compatibility (driver departure vs passenger requested time) ---
MAX_TIME_DIFFERENCE_MINUTES = 60   # Beyond this, the ride is NOT a match
EXCELLENT_TIME_DIFFERENCE_MINUTES = 10
VERY_GOOD_TIME_DIFFERENCE_MINUTES = 20
GOOD_TIME_DIFFERENCE_MINUTES = 30  # 30–60 min -> Weak

# --- Match score weights (must add up to 1.0) ---
WEIGHT_ROUTE = 0.45
WEIGHT_TIME = 0.25
WEIGHT_DESTINATION_ORG = 0.20
WEIGHT_SEATS = 0.10

# --- External services (free, no API keys) ---
NOMINATIM_USER_AGENT = "RideShareMVP/1.0"
NOMINATIM_MIN_SECONDS_BETWEEN_REQUESTS = 1.0   # Nominatim policy: max 1 request/second
GEOCODE_COUNTRY_CODES = None  # e.g. "pk" to only search Pakistan. None = whole world.
OSRM_BASE_URL = "https://router.project-osrm.org/route/v1/driving"
REQUEST_TIMEOUT_SECONDS = 15

# --- Demo data ---
DEMO_EMAIL_SUFFIX = "@demo.rideshare"   # every demo user's email ends with this
DEMO_PASSWORD = "demo123"
DEMO_ADMIN_PASSWORD = "admin123"

# --- Fixed choices ---
USER_ROLES = ["passenger", "driver", "both"]          # "admin" is not self-selectable
ORGANIZATION_TYPES = ["University", "College", "Workplace", "Other"]
REPORT_REASONS = ["Inappropriate behavior", "Unsafe driving", "No-show", "Harassment", "Other"]
REPORT_STATUSES = ["open", "reviewed", "resolved"]

PAGES = [
    "Home",
    "Register / Login",
    "Profile",
    "Offer a Ride",
    "Find a Ride",
    "My Rides",
    "Ride Requests",
    "Messages",
    "Notifications",
    "Admin Dashboard",
]


# =============================================================================
# 3. DATABASE INITIALIZATION
# Creates rideshare.db and all tables automatically the first time the app runs.
# "IF NOT EXISTS" means running it again is harmless.
# =============================================================================
SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS organizations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL UNIQUE,
    organization_type TEXT NOT NULL DEFAULT 'Other',
    email_domain TEXT,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    email TEXT NOT NULL UNIQUE,
    password TEXT NOT NULL,                -- stored as a salted hash, never plain text
    organization_id INTEGER REFERENCES organizations(id),
    role TEXT NOT NULL DEFAULT 'passenger',
    is_verified INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS vehicles (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL REFERENCES users(id),
    make TEXT NOT NULL,
    model TEXT NOT NULL,
    color TEXT,
    license_plate TEXT,
    seats INTEGER NOT NULL DEFAULT 4,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS rides (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    driver_id INTEGER NOT NULL REFERENCES users(id),
    organization_id INTEGER NOT NULL REFERENCES organizations(id),
    origin_address TEXT NOT NULL,
    origin_lat REAL NOT NULL,
    origin_lon REAL NOT NULL,
    destination_address TEXT NOT NULL,
    destination_lat REAL NOT NULL,
    destination_lon REAL NOT NULL,
    departure_date TEXT NOT NULL,          -- "YYYY-MM-DD"
    departure_time TEXT NOT NULL,          -- "HH:MM" (24h)
    available_seats INTEGER NOT NULL,
    total_seats INTEGER NOT NULL,
    route_distance_km REAL,
    route_duration_min REAL,
    route_geometry TEXT,                   -- JSON list of [lat, lon] points
    notes TEXT,
    status TEXT NOT NULL DEFAULT 'active', -- active / full / cancelled / completed
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS ride_requests (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ride_id INTEGER NOT NULL REFERENCES rides(id),
    passenger_id INTEGER NOT NULL REFERENCES users(id),
    pickup_address TEXT NOT NULL,
    pickup_lat REAL NOT NULL,
    pickup_lon REAL NOT NULL,
    requested_date TEXT NOT NULL,
    requested_time TEXT NOT NULL,
    seats_requested INTEGER NOT NULL DEFAULT 1,
    match_score INTEGER,
    match_reason TEXT,
    status TEXT NOT NULL DEFAULT 'pending', -- pending / accepted / rejected / cancelled
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS ride_passengers (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ride_id INTEGER NOT NULL REFERENCES rides(id),
    passenger_id INTEGER NOT NULL REFERENCES users(id),
    request_id INTEGER REFERENCES ride_requests(id),
    seats INTEGER NOT NULL DEFAULT 1,
    pickup_address TEXT,
    pickup_lat REAL,
    pickup_lon REAL,
    status TEXT NOT NULL DEFAULT 'accepted', -- accepted / cancelled / completed
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS messages (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ride_id INTEGER NOT NULL REFERENCES rides(id),
    sender_id INTEGER NOT NULL REFERENCES users(id),
    receiver_id INTEGER NOT NULL REFERENCES users(id),
    message TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS notifications (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL REFERENCES users(id),
    title TEXT NOT NULL,
    message TEXT NOT NULL,
    is_read INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS ratings (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ride_id INTEGER NOT NULL REFERENCES rides(id),
    reviewer_id INTEGER NOT NULL REFERENCES users(id),
    reviewed_user_id INTEGER NOT NULL REFERENCES users(id),
    rating INTEGER NOT NULL CHECK (rating BETWEEN 1 AND 5),
    comment TEXT,
    created_at TEXT NOT NULL,
    UNIQUE (ride_id, reviewer_id, reviewed_user_id)
);

CREATE TABLE IF NOT EXISTS reports (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    reporter_id INTEGER NOT NULL REFERENCES users(id),
    reported_user_id INTEGER NOT NULL REFERENCES users(id),
    ride_id INTEGER REFERENCES rides(id),
    reason TEXT NOT NULL,
    description TEXT,
    status TEXT NOT NULL DEFAULT 'open',   -- open / reviewed / resolved
    created_at TEXT NOT NULL
);

-- Extra table (needed for the "Blocking" feature)
CREATE TABLE IF NOT EXISTS blocked_users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    blocker_id INTEGER NOT NULL REFERENCES users(id),
    blocked_id INTEGER NOT NULL REFERENCES users(id),
    created_at TEXT NOT NULL,
    UNIQUE (blocker_id, blocked_id)
);
"""


def init_db():
    """Create the database file and every table if they don't exist yet."""
    conn = sqlite3.connect(DB_NAME)
    try:
        conn.executescript(SCHEMA_SQL)
        conn.commit()
    finally:
        conn.close()


# =============================================================================
# 4. DATABASE HELPER FUNCTIONS
# Every query uses "?" placeholders (parameterized queries). User input is NEVER
# pasted directly into SQL, which protects against SQL injection.
# =============================================================================
def now_str():
    """Current timestamp as text, used for created_at columns."""
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def get_connection():
    """Open a connection. Rows behave like dictionaries (row["name"])."""
    conn = sqlite3.connect(DB_NAME, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def fetch_all(sql, params=()):
    """Run a SELECT and return a list of dicts."""
    conn = get_connection()
    try:
        return [dict(row) for row in conn.execute(sql, params).fetchall()]
    finally:
        conn.close()


def fetch_one(sql, params=()):
    """Run a SELECT and return one dict (or None)."""
    conn = get_connection()
    try:
        row = conn.execute(sql, params).fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def execute(sql, params=()):
    """Run an INSERT/UPDATE/DELETE, commit, and return the new row id."""
    conn = get_connection()
    try:
        cursor = conn.execute(sql, params)
        conn.commit()
        return cursor.lastrowid
    finally:
        conn.close()


def placeholders(items):
    """Build '?,?,?' for an IN (...) clause with the right number of items."""
    return ",".join("?" for _ in items)


# ---- Organizations ----------------------------------------------------------
def get_organizations():
    return fetch_all("SELECT * FROM organizations ORDER BY name")


def get_organization(org_id):
    return fetch_one("SELECT * FROM organizations WHERE id = ?", (org_id,))


def get_or_create_organization(name, org_type="Other", email_domain=None):
    """Return the id of an organization, creating it if needed."""
    name = name.strip()
    existing = fetch_one("SELECT id FROM organizations WHERE LOWER(name) = LOWER(?)", (name,))
    if existing:
        return existing["id"]
    return execute(
        "INSERT INTO organizations (name, organization_type, email_domain, created_at) VALUES (?, ?, ?, ?)",
        (name, org_type, (email_domain or "").strip().lower() or None, now_str()),
    )


# ---- Users ------------------------------------------------------------------
def get_user(user_id):
    return fetch_one(
        """SELECT u.*, o.name AS organization_name, o.organization_type
           FROM users u LEFT JOIN organizations o ON o.id = u.organization_id
           WHERE u.id = ?""",
        (user_id,),
    )


def get_user_by_email(email):
    return fetch_one("SELECT * FROM users WHERE LOWER(email) = LOWER(?)", (email.strip(),))


def get_org_members(org_id, exclude_user_id=None):
    return fetch_all(
        "SELECT id, name, email FROM users WHERE organization_id = ? AND id != ? ORDER BY name",
        (org_id, exclude_user_id or -1),
    )


def get_user_rating(user_id):
    """Return (average rating, number of ratings). Average is None if no ratings."""
    row = fetch_one(
        "SELECT AVG(rating) AS avg_rating, COUNT(*) AS n FROM ratings WHERE reviewed_user_id = ?",
        (user_id,),
    )
    if not row or row["n"] == 0:
        return None, 0
    return round(row["avg_rating"], 1), row["n"]


# ---- Vehicles ---------------------------------------------------------------
def get_vehicles(user_id):
    return fetch_all("SELECT * FROM vehicles WHERE user_id = ? ORDER BY id", (user_id,))


def describe_vehicle(user_id):
    vehicles = get_vehicles(user_id)
    if not vehicles:
        return "Not provided"
    v = vehicles[0]
    text = f"{v['make']} {v['model']}"
    if v["color"]:
        text += f" ({v['color']})"
    return text


# ---- Notifications ----------------------------------------------------------
def create_notification(user_id, title, message):
    execute(
        "INSERT INTO notifications (user_id, title, message, is_read, created_at) VALUES (?, ?, ?, 0, ?)",
        (user_id, title, message, now_str()),
    )


def count_unread_notifications(user_id):
    row = fetch_one("SELECT COUNT(*) AS n FROM notifications WHERE user_id = ? AND is_read = 0", (user_id,))
    return row["n"] if row else 0


# ---- Blocking ---------------------------------------------------------------
def get_blocked_user_ids(user_id):
    """Users I blocked + users who blocked me. Both are hidden from matching."""
    rows = fetch_all(
        """SELECT blocked_id AS uid FROM blocked_users WHERE blocker_id = ?
           UNION
           SELECT blocker_id AS uid FROM blocked_users WHERE blocked_id = ?""",
        (user_id, user_id),
    )
    return {r["uid"] for r in rows}


# ---- Rides ------------------------------------------------------------------
def get_ride(ride_id):
    """One ride with driver and organization info attached."""
    return fetch_one(
        """SELECT r.*, u.name AS driver_name, o.name AS organization_name, o.organization_type
           FROM rides r
           JOIN users u ON u.id = r.driver_id
           JOIN organizations o ON o.id = r.organization_id
           WHERE r.id = ?""",
        (ride_id,),
    )


def get_ride_participant_ids(ride_id):
    """Driver + accepted passengers of a ride."""
    ride = fetch_one("SELECT driver_id FROM rides WHERE id = ?", (ride_id,))
    if not ride:
        return set()
    passengers = fetch_all(
        "SELECT passenger_id FROM ride_passengers WHERE ride_id = ? AND status IN ('accepted', 'completed')",
        (ride_id,),
    )
    return {ride["driver_id"]} | {p["passenger_id"] for p in passengers}


def is_ride_participant(ride_id, user_id):
    return user_id in get_ride_participant_ids(ride_id)


# =============================================================================
# 5. AUTHENTICATION
# Passwords are stored as salted PBKDF2 hashes (Python standard library only).
# hash_password() and verify_password() are the only two places that touch
# passwords, so switching to another method (e.g. bcrypt) later is easy.
# =============================================================================
EMAIL_PATTERN = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


def hash_password(password):
    salt = secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 100_000).hex()
    return f"pbkdf2${salt}${digest}"


def verify_password(password, stored):
    try:
        _, salt, digest = stored.split("$")
    except (ValueError, AttributeError):
        return False
    check = hashlib.pbkdf2_hmac("sha256", password.encode(), salt.encode(), 100_000).hex()
    return secrets.compare_digest(check, digest)


def register_user(name, email, password, organization_id, role, is_verified):
    """Validate and create a user. Returns (success, message)."""
    name, email = name.strip(), email.strip().lower()
    if len(name) < 2:
        return False, "Please enter your full name."
    if not EMAIL_PATTERN.match(email):
        return False, "Please enter a valid email address."
    if len(password) < 6:
        return False, "Password must be at least 6 characters."
    if role not in USER_ROLES:
        return False, "Please choose a valid role."
    if not organization_id:
        return False, "Please choose or create an organization."
    if get_user_by_email(email):
        return False, "An account with this email already exists. Please log in instead."
    execute(
        """INSERT INTO users (name, email, password, organization_id, role, is_verified, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?)""",
        (name, email, hash_password(password), organization_id, role, 1 if is_verified else 0, now_str()),
    )
    return True, "Account created! You can now log in."


def login_user(email, password):
    """Check credentials and fill st.session_state. Returns True on success."""
    user = get_user_by_email(email)
    if not user or not verify_password(password, user["password"]):
        return False
    st.session_state["user_id"] = user["id"]
    st.session_state["user_name"] = user["name"]
    st.session_state["organization_id"] = user["organization_id"]
    st.session_state["role"] = user["role"]
    return True


def logout_user():
    for key in ["user_id", "user_name", "organization_id", "role",
                "selected_ride", "search_results", "search_params", "ride_preview"]:
        st.session_state.pop(key, None)


def is_logged_in():
    return st.session_state.get("user_id") is not None


def current_user_id():
    return st.session_state.get("user_id")


def can_drive():
    return st.session_state.get("role") in ("driver", "both", "admin")


# =============================================================================
# 6. GEOCODING (address text -> latitude/longitude) using OpenStreetMap Nominatim
# We respect Nominatim's usage policy: a clear User-Agent, max 1 request/second,
# and results are cached so the same address is never looked up twice.
# =============================================================================
COORDINATE_PATTERN = re.compile(r"^\s*(-?\d{1,2}(?:\.\d+)?)\s*,\s*(-?\d{1,3}(?:\.\d+)?)\s*$")


def parse_coordinates(text):
    """Allow typing coordinates directly, e.g. '33.6683, 72.9978'. Handy for testing."""
    match = COORDINATE_PATTERN.match(text or "")
    if not match:
        return None
    lat, lon = float(match.group(1)), float(match.group(2))
    if -90 <= lat <= 90 and -180 <= lon <= 180:
        return lat, lon
    return None


@st.cache_resource
def _nominatim_rate_limiter():
    """Shared across reruns: remembers when we last called Nominatim."""
    return {"last_call": 0.0}


@st.cache_data(ttl=24 * 3600, show_spinner=False)
def _geocode_with_nominatim(address):
    """The actual network call. Cached for 24 hours per address."""
    limiter = _nominatim_rate_limiter()
    wait = NOMINATIM_MIN_SECONDS_BETWEEN_REQUESTS - (time.time() - limiter["last_call"])
    if wait > 0:
        time.sleep(wait)
    limiter["last_call"] = time.time()

    geolocator = Nominatim(user_agent=NOMINATIM_USER_AGENT, timeout=REQUEST_TIMEOUT_SECONDS)
    location = geolocator.geocode(address, country_codes=GEOCODE_COUNTRY_CODES)
    if location is None:
        return None
    return {"lat": location.latitude, "lon": location.longitude, "display_name": location.address}


def geocode_address(address):
    """
    Convert an address into coordinates.
    Returns (result, error_message). result = {"lat", "lon", "display_name"} or None.
    """
    address = (address or "").strip()
    if len(address) < 3:
        return None, "Please enter a location (at least 3 characters)."

    coords = parse_coordinates(address)
    if coords:
        return {"lat": coords[0], "lon": coords[1], "display_name": f"{coords[0]:.5f}, {coords[1]:.5f}"}, None

    try:
        result = _geocode_with_nominatim(address)
    except GeopyError:
        return None, "The location service is not responding right now. Please try again in a moment."
    except Exception:
        return None, "We could not reach the location service. Check your internet connection and try again."

    if result is None:
        return None, f"We could not find '{address}'. Please try a more specific address (e.g. add the city)."
    return result, None


# =============================================================================
# 7. ROUTING (driver's real road route) using the free public OSRM server
# =============================================================================
@st.cache_data(ttl=3600, show_spinner=False)
def _fetch_osrm_route(origin_lat, origin_lon, dest_lat, dest_lon):
    """Network call to OSRM. Note: OSRM expects lon,lat order (not lat,lon)."""
    url = f"{OSRM_BASE_URL}/{origin_lon},{origin_lat};{dest_lon},{dest_lat}"
    response = requests.get(
        url,
        params={"overview": "full", "geometries": "geojson"},
        headers={"User-Agent": NOMINATIM_USER_AGENT},
        timeout=REQUEST_TIMEOUT_SECONDS,
    )
    response.raise_for_status()
    return response.json()


def get_route(origin, destination):
    """
    Get the driving route between two points.
    origin/destination = (lat, lon)
    Returns (route, error_message). route = {"distance_km", "duration_min", "geometry"}
    where geometry is a list of [lat, lon] points along the road.
    """
    try:
        data = _fetch_osrm_route(origin[0], origin[1], destination[0], destination[1])
    except requests.exceptions.Timeout:
        return None, "The routing service took too long to respond. Please try again."
    except requests.exceptions.RequestException:
        return None, "We could not reach the routing service. Check your internet connection and try again."
    except ValueError:
        return None, "The routing service returned an unexpected answer. Please try again."

    if data.get("code") != "Ok" or not data.get("routes"):
        return None, "No driving route was found between these locations. Please check both addresses."

    best = data["routes"][0]
    # GeoJSON gives [lon, lat]; we flip to [lat, lon] because Folium and geopy use lat first.
    geometry = [[lat, lon] for lon, lat in best["geometry"]["coordinates"]]
    if len(geometry) < 2:
        return None, "No usable route was found between these locations."

    return {
        "distance_km": round(best["distance"] / 1000, 1),    # metres -> km
        "duration_min": round(best["duration"] / 60),        # seconds -> minutes
        "geometry": geometry,
    }, None


def straight_line_route(origin, destination, points=30):
    """
    Fallback used ONLY for demo data when OSRM can't be reached:
    a straight line split into points. Real rides always use OSRM.
    """
    geometry = [
        [origin[0] + (destination[0] - origin[0]) * i / points,
         origin[1] + (destination[1] - origin[1]) * i / points]
        for i in range(points + 1)
    ]
    km = geodesic(origin, destination).km * 1.3  # roads are longer than straight lines
    return {"distance_km": round(km, 1), "duration_min": round(km / 35 * 60), "geometry": geometry}


# =============================================================================
# 8. ROUTE MATCHING  ⭐ the core of the MVP ⭐
#
# Steps for every candidate ride:
#   1. Load the driver's stored OSRM route geometry (list of points).
#   2. Find the minimum distance from the passenger pickup to that route.
#      We measure to every route SEGMENT (the line between two consecutive
#      points), not only to the points, so long straight roads are handled well.
#      No API calls are needed for this: it's pure math.
#   3. Reject if farther than MAX_ROUTE_DISTANCE_KM.
#   4. Compare departure time with the requested time; reject if too far apart.
#   5. Check seats.
#   6. Combine everything into a 0–100 score and a human-readable explanation.
# =============================================================================
def calculate_point_to_route_distance(point, route_geometry):
    """
    Minimum distance (km) between a point and a route.
    point = (lat, lon); route_geometry = [[lat, lon], ...]
    Returns {"distance_km": float, "closest_point": (lat, lon)} or None.

    How it works:
      For small areas (a city), the Earth is almost flat, so we convert lat/lon
      into kilometres on a flat x/y plane centred on the pickup point. Then for
      each segment we find the closest point on that segment (simple geometry).
      Finally we measure the exact distance to that closest point with geopy.
    """
    if not route_geometry:
        return None

    p_lat, p_lon = point
    km_per_deg_lon = 111.320 * math.cos(math.radians(p_lat))
    km_per_deg_lat = 110.574

    def to_xy(lat, lon):
        # Pickup point is at (0, 0) on our flat map.
        return (lon - p_lon) * km_per_deg_lon, (lat - p_lat) * km_per_deg_lat

    if len(route_geometry) == 1:
        closest = tuple(route_geometry[0])
        return {"distance_km": geodesic(point, closest).km, "closest_point": closest}

    best_sq_distance = None
    closest = None
    for (lat_a, lon_a), (lat_b, lon_b) in zip(route_geometry[:-1], route_geometry[1:]):
        ax, ay = to_xy(lat_a, lon_a)
        bx, by = to_xy(lat_b, lon_b)
        dx, dy = bx - ax, by - ay
        segment_sq_length = dx * dx + dy * dy
        # t = how far along the segment the closest point is (0 = start, 1 = end)
        if segment_sq_length == 0:
            t = 0.0
        else:
            t = max(0.0, min(1.0, -(ax * dx + ay * dy) / segment_sq_length))
        cx, cy = ax + t * dx, ay + t * dy
        sq_distance = cx * cx + cy * cy
        if best_sq_distance is None or sq_distance < best_sq_distance:
            best_sq_distance = sq_distance
            closest = (lat_a + t * (lat_b - lat_a), lon_a + t * (lon_b - lon_a))

    return {"distance_km": geodesic(point, closest).km, "closest_point": closest}


def is_point_near_route_bounds(point, route_geometry, max_km):
    """
    Quick pre-check (optimization): if the pickup is far outside the route's
    bounding box, skip the detailed calculation.
    """
    lats = [p[0] for p in route_geometry]
    lons = [p[1] for p in route_geometry]
    lat_margin = max_km / 110.574
    lon_margin = max_km / max(1e-6, 111.320 * math.cos(math.radians(point[0])))
    return (min(lats) - lat_margin <= point[0] <= max(lats) + lat_margin
            and min(lons) - lon_margin <= point[1] <= max(lons) + lon_margin)


def minutes_between(time_a, time_b):
    """Signed difference in minutes: time_a - time_b. Times are 'HH:MM'."""
    a = datetime.strptime(time_a, "%H:%M")
    b = datetime.strptime(time_b, "%H:%M")
    return int((a - b).total_seconds() // 60)


def interpolate_score(value, bands):
    """
    Turn a value into a score using (value, score) checkpoints, drawing a straight
    line between them. Example bands: [(0, 100), (1, 90), (2, 80)] -> 1.5 gives 85.
    """
    if value <= bands[0][0]:
        return bands[0][1]
    for (x1, y1), (x2, y2) in zip(bands[:-1], bands[1:]):
        if value <= x2:
            return y1 + (y2 - y1) * (value - x1) / (x2 - x1)
    return 0


def route_proximity_score(distance_km):
    if distance_km > MAX_ROUTE_DISTANCE_KM:
        return 0
    bands = [(0, 100), (EXCELLENT_ROUTE_DISTANCE_KM, 90), (VERY_GOOD_ROUTE_DISTANCE_KM, 80),
             (GOOD_ROUTE_DISTANCE_KM, 65), (MAX_ROUTE_DISTANCE_KM, 30)]
    return interpolate_score(distance_km, bands)


def route_proximity_label(distance_km):
    if distance_km <= EXCELLENT_ROUTE_DISTANCE_KM:
        return "Excellent"
    if distance_km <= VERY_GOOD_ROUTE_DISTANCE_KM:
        return "Very Good"
    if distance_km <= GOOD_ROUTE_DISTANCE_KM:
        return "Good"
    if distance_km <= MAX_ROUTE_DISTANCE_KM:
        return "Weak"
    return "Not a match"


def time_compatibility_score(diff_minutes):
    diff = abs(diff_minutes)
    if diff > MAX_TIME_DIFFERENCE_MINUTES:
        return 0
    bands = [(0, 100), (EXCELLENT_TIME_DIFFERENCE_MINUTES, 90), (VERY_GOOD_TIME_DIFFERENCE_MINUTES, 80),
             (GOOD_TIME_DIFFERENCE_MINUTES, 65), (MAX_TIME_DIFFERENCE_MINUTES, 30)]
    return interpolate_score(diff, bands)


def time_compatibility_label(diff_minutes):
    diff = abs(diff_minutes)
    if diff <= EXCELLENT_TIME_DIFFERENCE_MINUTES:
        return "Excellent"
    if diff <= VERY_GOOD_TIME_DIFFERENCE_MINUTES:
        return "Very Good"
    if diff <= GOOD_TIME_DIFFERENCE_MINUTES:
        return "Good"
    if diff <= MAX_TIME_DIFFERENCE_MINUTES:
        return "Weak"
    return "Not suitable"


def seat_score(available, requested):
    if available < requested:
        return 0
    if available > requested:
        return 100   # spare seats left after you join
    return 80        # exactly enough seats


def calculate_match_score(route_distance_km, time_diff_minutes, same_organization,
                          available_seats, seats_requested):
    """
    Weighted 0–100 score. Returns a dict with every component plus "total".
    Example: route 95, time 90, org 100, seats 100 ->
             95*0.45 + 90*0.25 + 100*0.20 + 100*0.10 = 95.25 -> 95% Match
    """
    route = route_proximity_score(route_distance_km)
    timing = time_compatibility_score(time_diff_minutes)
    org = 100 if same_organization else 0
    seats = seat_score(available_seats, seats_requested)
    total = (route * WEIGHT_ROUTE + timing * WEIGHT_TIME
             + org * WEIGHT_DESTINATION_ORG + seats * WEIGHT_SEATS)
    return {
        "route_score": round(route, 1),
        "time_score": round(timing, 1),
        "org_score": org,
        "seat_score": seats,
        "total": int(math.floor(total + 0.5)),   # normal rounding: 92.5 -> 93
    }


def organization_word(org_type):
    return {"University": "university", "College": "college", "Workplace": "workplace"}.get(org_type, "organization")


def generate_match_reason(route_distance_km, time_diff_minutes, org_type, available_seats):
    """Human-readable reasons, one per line, e.g. '✓ Pickup is 0.7 km from driver's route'."""
    reasons = []

    label = route_proximity_label(route_distance_km)
    icon = "✓" if label != "Weak" else "⚠"
    reasons.append(f"{icon} {label} route match — pickup is {route_distance_km:.1f} km from the driver's route")

    diff = time_diff_minutes
    icon = "✓" if abs(diff) <= GOOD_TIME_DIFFERENCE_MINUTES else "⚠"
    if diff == 0:
        reasons.append("✓ Departs exactly at your requested time")
    else:
        direction = "later" if diff > 0 else "earlier"
        reasons.append(f"{icon} Departure time is {abs(diff)} minutes {direction} than your requested time")

    reasons.append(f"✓ Same {organization_word(org_type)}")
    reasons.append(f"✓ {available_seats} seat{'s' if available_seats != 1 else ''} available")
    return "\n".join(reasons)


def find_matching_rides(passenger_id, organization_id, pickup, requested_date, requested_time, seats_requested):
    """
    Search active rides and score them against the passenger's pickup.
    pickup = {"lat", "lon", "display_name"}
    Returns (matches sorted best-first, summary of why other rides were skipped).
    """
    blocked = get_blocked_user_ids(passenger_id)
    candidate_rides = fetch_all(
        """SELECT r.*, u.name AS driver_name, o.name AS organization_name, o.organization_type
           FROM rides r
           JOIN users u ON u.id = r.driver_id
           JOIN organizations o ON o.id = r.organization_id
           WHERE r.organization_id = ?          -- same organization only
             AND r.departure_date = ?
             AND r.status = 'active'            -- full/cancelled/completed rides are excluded
             AND r.driver_id != ?               -- not your own rides""",
        (organization_id, requested_date, passenger_id),
    )

    pickup_point = (pickup["lat"], pickup["lon"])
    skipped = {"too_far": 0, "wrong_time": 0, "not_enough_seats": 0}
    matches = []

    for ride in candidate_rides:
        if ride["driver_id"] in blocked:
            continue

        if ride["available_seats"] < seats_requested:
            skipped["not_enough_seats"] += 1
            continue

        # --- Time compatibility ---
        time_diff = minutes_between(ride["departure_time"], requested_time)
        if abs(time_diff) > MAX_TIME_DIFFERENCE_MINUTES:
            skipped["wrong_time"] += 1
            continue

        # --- Route proximity (the important part) ---
        try:
            geometry = json.loads(ride["route_geometry"] or "[]")
        except (TypeError, ValueError):
            geometry = []
        if not geometry:
            continue
        if not is_point_near_route_bounds(pickup_point, geometry, MAX_ROUTE_DISTANCE_KM):
            skipped["too_far"] += 1
            continue
        proximity = calculate_point_to_route_distance(pickup_point, geometry)
        distance_km = proximity["distance_km"]
        if distance_km > MAX_ROUTE_DISTANCE_KM:
            skipped["too_far"] += 1
            continue

        # --- Score + explanation ---
        score = calculate_match_score(distance_km, time_diff, True, ride["available_seats"], seats_requested)
        reason = generate_match_reason(distance_km, time_diff, ride["organization_type"], ride["available_seats"])
        rating, rating_count = get_user_rating(ride["driver_id"])

        matches.append({
            "ride_id": ride["id"],
            "driver_id": ride["driver_id"],
            "driver_name": ride["driver_name"],
            "driver_rating": rating,
            "driver_rating_count": rating_count,
            "organization_name": ride["organization_name"],
            "organization_type": ride["organization_type"],
            "origin_address": ride["origin_address"],
            "destination_address": ride["destination_address"],
            "departure_date": ride["departure_date"],
            "departure_time": ride["departure_time"],
            "available_seats": ride["available_seats"],
            "distance_from_route_km": round(distance_km, 2),
            "closest_point": list(proximity["closest_point"]),
            "time_diff_minutes": time_diff,
            "score": score,
            "match_score": score["total"],
            "match_reason": reason,
        })

    matches.sort(key=lambda m: m["match_score"], reverse=True)
    return matches, skipped


# =============================================================================
# 9. RIDE / REQUEST / MESSAGE ACTIONS (business logic)
# Each function checks permissions itself, so the UI can't bypass the rules.
# Each returns (success: bool, message: str).
# =============================================================================
def create_ride(driver_id, organization_id, preview):
    """Save a ride after the driver confirmed the route preview."""
    ride_id = execute(
        """INSERT INTO rides (driver_id, organization_id,
                              origin_address, origin_lat, origin_lon,
                              destination_address, destination_lat, destination_lon,
                              departure_date, departure_time, available_seats, total_seats,
                              route_distance_km, route_duration_min, route_geometry,
                              notes, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'active', ?)""",
        (driver_id, organization_id,
         preview["origin"]["display_name"], preview["origin"]["lat"], preview["origin"]["lon"],
         preview["destination"]["display_name"], preview["destination"]["lat"], preview["destination"]["lon"],
         preview["date"], preview["time"], preview["seats"], preview["seats"],
         preview["route"]["distance_km"], preview["route"]["duration_min"],
         json.dumps(preview["route"]["geometry"]), preview.get("notes", ""), now_str()),
    )
    return ride_id


def create_ride_request(passenger_id, match, search_params):
    """Passenger asks for a seat. Prevents duplicates and invalid requests."""
    ride = get_ride(match["ride_id"])
    passenger = get_user(passenger_id)
    if not ride or not passenger:
        return False, "This ride no longer exists."
    if ride["organization_id"] != passenger["organization_id"]:
        return False, "You can only request rides from your own organization."
    if ride["driver_id"] == passenger_id:
        return False, "You cannot request a seat on your own ride."
    if ride["status"] != "active":
        return False, f"This ride is {ride['status']} and is not accepting requests."
    if ride["available_seats"] < search_params["seats"]:
        return False, "Sorry, this ride doesn't have enough free seats any more."
    if ride["driver_id"] in get_blocked_user_ids(passenger_id):
        return False, "You cannot request this ride."

    existing = fetch_one(
        "SELECT status FROM ride_requests WHERE ride_id = ? AND passenger_id = ? AND status IN ('pending', 'accepted')",
        (ride["id"], passenger_id),
    )
    if existing:
        return False, f"You already have a {existing['status']} request for this ride."

    execute(
        """INSERT INTO ride_requests (ride_id, passenger_id, pickup_address, pickup_lat, pickup_lon,
                                      requested_date, requested_time, seats_requested,
                                      match_score, match_reason, status, created_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'pending', ?)""",
        (ride["id"], passenger_id, search_params["pickup"]["display_name"],
         search_params["pickup"]["lat"], search_params["pickup"]["lon"],
         search_params["date"], search_params["time"], search_params["seats"],
         match["match_score"], match["match_reason"], now_str()),
    )
    create_notification(
        ride["driver_id"], "New ride request",
        f"{passenger['name']} requested {search_params['seats']} seat(s) on your ride on "
        f"{ride['departure_date']} at {format_time(ride['departure_time'])} ({match['match_score']}% match).",
    )
    return True, "Ride request sent successfully."


def accept_request(request_id, driver_id):
    """
    Driver accepts a request. Done in ONE transaction so seats can't go negative:
      1. request -> accepted   2. add ride_passengers row   3. reduce seats
      4. mark ride full at 0   5. notify passenger
    """
    conn = get_connection()
    try:
        req = conn.execute(
            """SELECT rr.*, r.driver_id, r.available_seats, r.status AS ride_status,
                      r.departure_date, r.departure_time
               FROM ride_requests rr JOIN rides r ON r.id = rr.ride_id
               WHERE rr.id = ?""",
            (request_id,),
        ).fetchone()
        if not req:
            return False, "Request not found."
        if req["driver_id"] != driver_id:
            return False, "Only the driver of this ride can accept requests."
        if req["status"] != "pending":
            return False, f"This request is already {req['status']}."
        if req["ride_status"] != "active":
            return False, f"This ride is {req['ride_status']}; no more passengers can be accepted."
        if req["available_seats"] < req["seats_requested"]:
            return False, "Not enough seats left to accept this request."

        new_seats = req["available_seats"] - req["seats_requested"]
        conn.execute("UPDATE ride_requests SET status = 'accepted' WHERE id = ?", (request_id,))
        conn.execute(
            """INSERT INTO ride_passengers (ride_id, passenger_id, request_id, seats, pickup_address,
                                            pickup_lat, pickup_lon, status, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, 'accepted', ?)""",
            (req["ride_id"], req["passenger_id"], request_id, req["seats_requested"], req["pickup_address"],
             req["pickup_lat"], req["pickup_lon"], now_str()),
        )
        conn.execute(
            "UPDATE rides SET available_seats = ?, status = ? WHERE id = ?",
            (new_seats, "full" if new_seats == 0 else "active", req["ride_id"]),
        )
        conn.execute(
            "INSERT INTO notifications (user_id, title, message, is_read, created_at) VALUES (?, ?, ?, 0, ?)",
            (req["passenger_id"], "Request accepted 🎉",
             f"Your seat on the ride on {req['departure_date']} at {format_time(req['departure_time'])} "
             f"was accepted. You can now message the driver.", now_str()),
        )
        conn.commit()
        return True, "Passenger accepted." + (" The ride is now full." if new_seats == 0 else "")
    except sqlite3.Error:
        conn.rollback()
        return False, "Something went wrong while saving. Please try again."
    finally:
        conn.close()


def reject_request(request_id, driver_id):
    req = fetch_one(
        """SELECT rr.*, r.driver_id, r.departure_date, r.departure_time
           FROM ride_requests rr JOIN rides r ON r.id = rr.ride_id WHERE rr.id = ?""",
        (request_id,),
    )
    if not req:
        return False, "Request not found."
    if req["driver_id"] != driver_id:
        return False, "Only the driver of this ride can reject requests."
    if req["status"] != "pending":
        return False, f"This request is already {req['status']}."
    execute("UPDATE ride_requests SET status = 'rejected' WHERE id = ?", (request_id,))
    create_notification(
        req["passenger_id"], "Request rejected",
        f"Your request for the ride on {req['departure_date']} at {format_time(req['departure_time'])} "
        "was not accepted. Try searching for another ride.",
    )
    return True, "Request rejected."


def cancel_ride(ride_id, driver_id):
    """Driver cancels a ride: notify accepted passengers, close pending requests."""
    ride = get_ride(ride_id)
    if not ride or ride["driver_id"] != driver_id:
        return False, "Only the driver can cancel this ride."
    if ride["status"] in ("cancelled", "completed"):
        return False, f"This ride is already {ride['status']}."

    passengers = fetch_all(
        "SELECT passenger_id FROM ride_passengers WHERE ride_id = ? AND status = 'accepted'", (ride_id,))
    pending = fetch_all(
        "SELECT passenger_id FROM ride_requests WHERE ride_id = ? AND status = 'pending'", (ride_id,))

    execute("UPDATE rides SET status = 'cancelled' WHERE id = ?", (ride_id,))
    execute("UPDATE ride_passengers SET status = 'cancelled' WHERE ride_id = ? AND status = 'accepted'", (ride_id,))
    execute("UPDATE ride_requests SET status = 'cancelled' WHERE ride_id = ? AND status IN ('pending', 'accepted')",
            (ride_id,))

    text = (f"The ride from {short_address(ride['origin_address'])} on {ride['departure_date']} at "
            f"{format_time(ride['departure_time'])} was cancelled by the driver.")
    for user_id in {p["passenger_id"] for p in passengers + pending}:
        create_notification(user_id, "Ride cancelled", text)
    return True, "Ride cancelled. Passengers have been notified."


def complete_ride(ride_id, driver_id):
    ride = get_ride(ride_id)
    if not ride or ride["driver_id"] != driver_id:
        return False, "Only the driver can complete this ride."
    if ride["status"] not in ("active", "full"):
        return False, f"This ride is already {ride['status']}."
    execute("UPDATE rides SET status = 'completed' WHERE id = ?", (ride_id,))
    execute("UPDATE ride_passengers SET status = 'completed' WHERE ride_id = ? AND status = 'accepted'", (ride_id,))
    execute("UPDATE ride_requests SET status = 'cancelled' WHERE ride_id = ? AND status = 'pending'", (ride_id,))
    for pid in get_ride_participant_ids(ride_id) - {driver_id}:
        create_notification(pid, "Ride completed", "Your ride was marked as completed. You can now rate your driver.")
    return True, "Ride marked as completed. Everyone can now leave ratings."


def cancel_my_request(request_id, passenger_id):
    req = fetch_one("SELECT * FROM ride_requests WHERE id = ?", (request_id,))
    if not req or req["passenger_id"] != passenger_id:
        return False, "Request not found."
    if req["status"] != "pending":
        return False, f"This request is already {req['status']}."
    execute("UPDATE ride_requests SET status = 'cancelled' WHERE id = ?", (request_id,))
    return True, "Request cancelled."


def leave_ride(ride_id, passenger_id):
    """Passenger cancels participation: give the seats back and notify the driver."""
    seat_row = fetch_one(
        "SELECT * FROM ride_passengers WHERE ride_id = ? AND passenger_id = ? AND status = 'accepted'",
        (ride_id, passenger_id),
    )
    ride = get_ride(ride_id)
    if not seat_row or not ride:
        return False, "You are not on this ride."
    if ride["status"] not in ("active", "full"):
        return False, f"This ride is {ride['status']}."

    new_seats = min(ride["total_seats"], ride["available_seats"] + seat_row["seats"])
    execute("UPDATE ride_passengers SET status = 'cancelled' WHERE id = ?", (seat_row["id"],))
    execute("UPDATE ride_requests SET status = 'cancelled' WHERE ride_id = ? AND passenger_id = ? AND status = 'accepted'",
            (ride_id, passenger_id))
    execute("UPDATE rides SET available_seats = ?, status = 'active' WHERE id = ?", (new_seats, ride_id))
    passenger = get_user(passenger_id)
    create_notification(ride["driver_id"], "Passenger left your ride",
                        f"{passenger['name']} cancelled their seat on your ride on {ride['departure_date']}.")
    return True, "You have left the ride."


def send_message(ride_id, sender_id, receiver_id, text):
    text = (text or "").strip()
    if not text:
        return False, "Please type a message."
    if len(text) > 1000:
        return False, "Messages must be under 1000 characters."
    participants = get_ride_participant_ids(ride_id)
    if sender_id not in participants or receiver_id not in participants or sender_id == receiver_id:
        return False, "Only people on the same accepted ride can message each other."
    execute("INSERT INTO messages (ride_id, sender_id, receiver_id, message, created_at) VALUES (?, ?, ?, ?, ?)",
            (ride_id, sender_id, receiver_id, text, now_str()))
    sender = get_user(sender_id)
    create_notification(receiver_id, "New message", f"{sender['name']}: {text[:80]}")
    return True, "Message sent."


def submit_rating(ride_id, reviewer_id, reviewed_user_id, rating, comment):
    ride = get_ride(ride_id)
    if not ride or ride["status"] != "completed":
        return False, "You can only rate after the ride is completed."
    if reviewer_id == reviewed_user_id:
        return False, "You cannot rate yourself."
    participants = get_ride_participant_ids(ride_id)
    if reviewer_id not in participants or reviewed_user_id not in participants:
        return False, "You can only rate people who were on this ride."
    if not 1 <= int(rating) <= 5:
        return False, "Rating must be between 1 and 5."
    try:
        execute("""INSERT INTO ratings (ride_id, reviewer_id, reviewed_user_id, rating, comment, created_at)
                   VALUES (?, ?, ?, ?, ?, ?)""",
                (ride_id, reviewer_id, reviewed_user_id, int(rating), (comment or "").strip(), now_str()))
    except sqlite3.IntegrityError:
        return False, "You have already rated this person for this ride."
    return True, "Thanks for your rating!"


def submit_report(reporter_id, reported_user_id, ride_id, reason, description):
    if reporter_id == reported_user_id:
        return False, "You cannot report yourself."
    if reason not in REPORT_REASONS:
        return False, "Please choose a reason."
    execute("""INSERT INTO reports (reporter_id, reported_user_id, ride_id, reason, description, status, created_at)
               VALUES (?, ?, ?, ?, ?, 'open', ?)""",
            (reporter_id, reported_user_id, ride_id, reason, (description or "").strip(), now_str()))
    return True, "Report submitted. An admin will review it."


def block_user(blocker_id, blocked_id):
    if blocker_id == blocked_id:
        return False, "You cannot block yourself."
    try:
        execute("INSERT INTO blocked_users (blocker_id, blocked_id, created_at) VALUES (?, ?, ?)",
                (blocker_id, blocked_id, now_str()))
    except sqlite3.IntegrityError:
        return False, "This user is already blocked."
    return True, "User blocked. You won't see each other in ride matches."


def unblock_user(blocker_id, blocked_id):
    execute("DELETE FROM blocked_users WHERE blocker_id = ? AND blocked_id = ?", (blocker_id, blocked_id))
    return True, "User unblocked."


# =============================================================================
# 10. DEMO DATA
# Real coordinates around Islamabad. Routes are calculated with OSRM (not
# hardcoded), so matching is genuinely tested. Only 5 OSRM calls are made and
# NO Nominatim calls (we already know the coordinates).
# =============================================================================
DEMO_PLACES = {
    "F-10 Markaz, Islamabad": (33.6955, 73.0118),
    "F-7 Markaz, Islamabad": (33.7206, 73.0567),
    "I-8 Markaz, Islamabad": (33.6680, 73.0757),
    "NUST H-12, Islamabad": (33.6425, 72.9911),
    "FAST University H-11, Islamabad": (33.6563, 72.9967),
}

# Points you can paste into "Pickup Location" to try each scenario.
DEMO_TEST_PICKUPS = [
    ("G-11 Markaz (near Ahmed's route)", "33.6683, 72.9978", "Should match Ahmed with a high score"),
    ("G-10 Markaz", "33.6764, 73.0128", "Usually close to the F-10 → NUST route"),
    ("G-13 (a bit west of the routes)", "33.6495, 72.9650", "Further from route: lower score"),
    ("Saddar, Rawalpindi (far away)", "33.5973, 73.0479", "More than 5 km away: no NUST matches"),
]


def demo_data_exists():
    row = fetch_one("SELECT COUNT(*) AS n FROM users WHERE email LIKE ?", (f"%{DEMO_EMAIL_SUFFIX}",))
    return row["n"] > 0


def delete_demo_data():
    """Remove only demo users and everything connected to them. Your own data is untouched."""
    demo_users = [r["id"] for r in fetch_all("SELECT id FROM users WHERE email LIKE ?", (f"%{DEMO_EMAIL_SUFFIX}",))]
    if not demo_users:
        return
    u = placeholders(demo_users)
    demo_rides = [r["id"] for r in fetch_all(f"SELECT id FROM rides WHERE driver_id IN ({u})", demo_users)]
    r = placeholders(demo_rides) if demo_rides else "NULL"
    conn = get_connection()
    try:
        conn.execute(f"DELETE FROM messages WHERE ride_id IN ({r}) OR sender_id IN ({u}) OR receiver_id IN ({u})",
                     demo_rides + demo_users + demo_users)
        conn.execute(f"DELETE FROM ratings WHERE ride_id IN ({r}) OR reviewer_id IN ({u}) OR reviewed_user_id IN ({u})",
                     demo_rides + demo_users + demo_users)
        conn.execute(f"DELETE FROM reports WHERE ride_id IN ({r}) OR reporter_id IN ({u}) OR reported_user_id IN ({u})",
                     demo_rides + demo_users + demo_users)
        conn.execute(f"DELETE FROM ride_passengers WHERE ride_id IN ({r}) OR passenger_id IN ({u})",
                     demo_rides + demo_users)
        conn.execute(f"DELETE FROM ride_requests WHERE ride_id IN ({r}) OR passenger_id IN ({u})",
                     demo_rides + demo_users)
        conn.execute(f"DELETE FROM rides WHERE id IN ({r})", demo_rides)
        conn.execute(f"DELETE FROM blocked_users WHERE blocker_id IN ({u}) OR blocked_id IN ({u})",
                     demo_users + demo_users)
        conn.execute(f"DELETE FROM notifications WHERE user_id IN ({u})", demo_users)
        conn.execute(f"DELETE FROM vehicles WHERE user_id IN ({u})", demo_users)
        conn.execute(f"DELETE FROM users WHERE id IN ({u})", demo_users)
        conn.commit()
    finally:
        conn.close()


def load_demo_data():
    """
    Create demo organizations, users, vehicles and rides.
    Returns a list of warnings (e.g. if OSRM was unreachable).
    """
    warnings = []
    orgs = {
        "NUST": get_or_create_organization("NUST", "University", "nust.edu.pk"),
        "FAST University": get_or_create_organization("FAST University", "University", "nu.edu.pk"),
        "COMSATS": get_or_create_organization("COMSATS", "University", "comsats.edu.pk"),
        "ABC Company": get_or_create_organization("ABC Company", "Workplace", "abc.com"),
    }

    def add_user(name, org, role, password=DEMO_PASSWORD):
        email = f"{name.lower()}{DEMO_EMAIL_SUFFIX}"
        return execute(
            """INSERT INTO users (name, email, password, organization_id, role, is_verified, created_at)
               VALUES (?, ?, ?, ?, ?, 1, ?)""",
            (name, email, hash_password(password), orgs[org], role, now_str()),
        )

    ahmed = add_user("Ahmed", "NUST", "driver")
    bilal = add_user("Bilal", "NUST", "both")
    hina = add_user("Hina", "NUST", "driver")
    sara = add_user("Sara", "NUST", "passenger")
    add_user("Zain", "NUST", "passenger")
    ali = add_user("Ali", "FAST University", "driver")
    add_user("Admin", "NUST", "admin", password=DEMO_ADMIN_PASSWORD)

    for user_id, make, model, color, plate, seats in [
        (ahmed, "Toyota", "Corolla", "White", "ICT-1234", 4),
        (bilal, "Honda", "City", "Silver", "ICT-5678", 4),
        (hina, "Suzuki", "Cultus", "Red", "ICT-9012", 4),
        (ali, "Toyota", "Yaris", "Black", "ICT-3456", 4),
    ]:
        execute("""INSERT INTO vehicles (user_id, make, model, color, license_plate, seats, created_at)
                   VALUES (?, ?, ?, ?, ?, ?, ?)""", (user_id, make, model, color, plate, seats, now_str()))

    tomorrow = (date.today() + timedelta(days=1)).isoformat()
    yesterday = (date.today() - timedelta(days=1)).isoformat()

    def add_ride(driver_id, org, origin_name, dest_name, ride_date, ride_time, seats, available, status):
        origin, dest = DEMO_PLACES[origin_name], DEMO_PLACES[dest_name]
        route, error = get_route(origin, dest)
        if error:
            route = straight_line_route(origin, dest)
            warnings.append(f"OSRM unavailable for {origin_name} → {dest_name}; used a straight-line route.")
        return execute(
            """INSERT INTO rides (driver_id, organization_id, origin_address, origin_lat, origin_lon,
                                  destination_address, destination_lat, destination_lon,
                                  departure_date, departure_time, available_seats, total_seats,
                                  route_distance_km, route_duration_min, route_geometry, notes, status, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (driver_id, orgs[org], origin_name, origin[0], origin[1], dest_name, dest[0], dest[1],
             ride_date, ride_time, available, seats, route["distance_km"], route["duration_min"],
             json.dumps(route["geometry"]), "Demo ride", status, now_str()),
        )

    # Scenario 1/2/4: Ahmed's main ride (F-10 → NUST, 8:00 AM)
    add_ride(ahmed, "NUST", "F-10 Markaz, Islamabad", "NUST H-12, Islamabad", tomorrow, "08:00", 3, 3, "active")
    # A second NUST ride, later departure, from F-7
    add_ride(bilal, "NUST", "F-7 Markaz, Islamabad", "NUST H-12, Islamabad", tomorrow, "08:30", 3, 2, "active")
    # Scenario 5: a full ride (0 seats) -> must NOT appear
    add_ride(hina, "NUST", "I-8 Markaz, Islamabad", "NUST H-12, Islamabad", tomorrow, "08:05", 3, 0, "full")
    # Scenario 6: same route, different organization -> must NOT appear for NUST users
    add_ride(ali, "FAST University", "F-10 Markaz, Islamabad", "FAST University H-11, Islamabad",
             tomorrow, "08:00", 4, 4, "active")
    # A completed ride from yesterday with Sara on board -> lets you test ratings
    past = add_ride(bilal, "NUST", "F-7 Markaz, Islamabad", "NUST H-12, Islamabad", yesterday, "08:30", 3, 2, "completed")
    execute("""INSERT INTO ride_passengers (ride_id, passenger_id, seats, pickup_address, pickup_lat, pickup_lon,
                                            status, created_at)
               VALUES (?, ?, 1, 'G-11 Markaz, Islamabad', 33.6683, 72.9978, 'completed', ?)""",
            (past, sara, now_str()))

    create_notification(sara, "Welcome to the RideShare demo",
                        "Try Find a Ride with pickup '33.6683, 72.9978' (G-11) for tomorrow at 8:00 AM.")
    return warnings


# =============================================================================
# 11. UI HELPER FUNCTIONS
# =============================================================================
CUSTOM_CSS = """
<style>
.match-badge {
    display: inline-block; padding: 4px 12px; border-radius: 999px;
    font-weight: 700; font-size: 1.1rem; color: white;
}
.match-high   { background: #16a34a; }
.match-medium { background: #ca8a04; }
.match-low    { background: #dc2626; }
.small-muted  { color: #6b7280; font-size: 0.85rem; }
.reason-line  { margin: 2px 0; }
</style>
"""


def format_time(hhmm):
    """'08:05' -> '8:05 AM'"""
    try:
        return datetime.strptime(hhmm, "%H:%M").strftime("%I:%M %p").lstrip("0")
    except (ValueError, TypeError):
        return hhmm or ""


def short_address(address, parts=2):
    """Shorten long Nominatim addresses for cards: 'A, B, C, D' -> 'A, B'."""
    if not address:
        return ""
    return ", ".join(p.strip() for p in address.split(",")[:parts])


def rating_text(avg, count):
    return f"⭐ {avg} ({count})" if avg is not None else "No ratings yet"


def match_badge(score):
    css = "match-high" if score >= 80 else "match-medium" if score >= 60 else "match-low"
    return f'<span class="match-badge {css}">{score}% Match</span>'


def set_flash(message, kind="success"):
    """Store a message to display after st.rerun()."""
    st.session_state["flash"] = (kind, message)


def show_flash():
    flash = st.session_state.pop("flash", None)
    if flash:
        kind, message = flash
        getattr(st, kind)(message)


def show_result(success, message):
    """Show success/error and rerun so the page refreshes with new data."""
    set_flash(message, "success" if success else "error")
    st.rerun()


def go_to(page):
    """Callback for buttons that switch the sidebar page."""
    st.session_state["nav"] = page


def require_login():
    if not is_logged_in():
        st.info("Please log in first (sidebar → Register / Login).")
        return False
    return True


def create_route_map(origin, destination, route_geometry, pickup=None, closest_point=None):
    """
    Build a Folium map.
      origin / destination / pickup = (lat, lon)
      route_geometry = [[lat, lon], ...]
    Green = origin, red = destination, blue = passenger pickup.
    """
    fmap = folium.Map(location=origin, zoom_start=12, tiles="OpenStreetMap")

    if route_geometry:
        folium.PolyLine(route_geometry, color="#2563eb", weight=5, opacity=0.8, tooltip="Driver's route").add_to(fmap)

    folium.Marker(origin, tooltip="Origin", popup="Driver starts here",
                  icon=folium.Icon(color="green", icon="play")).add_to(fmap)
    folium.Marker(destination, tooltip="Destination", popup="Destination",
                  icon=folium.Icon(color="red", icon="flag")).add_to(fmap)

    bounds = list(route_geometry or []) + [list(origin), list(destination)]
    if pickup:
        folium.Marker(pickup, tooltip="Passenger pickup", popup="Your pickup",
                      icon=folium.Icon(color="blue", icon="user")).add_to(fmap)
        bounds.append(list(pickup))
        if closest_point:
            # Dashed line from the pickup to the nearest point on the route
            folium.PolyLine([pickup, closest_point], color="#f97316", weight=3, dash_array="6",
                            tooltip="Distance to route").add_to(fmap)

    # Zoom the map so everything is visible: [[south, west], [north, east]]
    lats = [p[0] for p in bounds]
    lons = [p[1] for p in bounds]
    fmap.fit_bounds([[min(lats), min(lons)], [max(lats), max(lons)]], padding=(20, 20))
    return fmap


def show_map(fmap, key):
    # returned_objects=[] stops the map from re-running the app on every click/zoom.
    st_folium(fmap, height=420, use_container_width=True, returned_objects=[], key=key)


def show_ride_map(ride, pickup=None, closest_point=None, key="map"):
    geometry = json.loads(ride["route_geometry"] or "[]")
    fmap = create_route_map((ride["origin_lat"], ride["origin_lon"]),
                            (ride["destination_lat"], ride["destination_lon"]),
                            geometry, pickup, closest_point)
    show_map(fmap, key)


def show_reasons(reason_text):
    for line in (reason_text or "").split("\n"):
        if line.strip():
            st.markdown(f'<div class="reason-line">{line}</div>', unsafe_allow_html=True)


# =============================================================================
# 12. PAGES
# =============================================================================

# ---- Home -------------------------------------------------------------------
def page_home():
    if not is_logged_in():
        st.markdown("### Share rides with people from your university, college or workplace.")
        st.write("RideShare matches you with drivers whose **actual road route** passes close to your pickup point "
                 "— not just drivers going to the same destination.")
        c1, c2, c3 = st.columns(3)
        c1.info("**1. Drivers** publish their route")
        c2.info("**2. Passengers** enter a pickup point")
        c3.info("**3. We match** pickups that lie along the route")
        st.button("Register / Login →", on_click=go_to, args=("Register / Login",), type="primary")
        st.divider()
        section_demo_data()
        return

    user = get_user(current_user_id())
    st.subheader(f"Welcome, {user['name']} 👋")
    c1, c2 = st.columns(2)
    with c1:
        st.markdown(f"**Organization:**  \n{user['organization_name'] or '—'}")
    with c2:
        status = "✓ Verified" if user["is_verified"] else "✗ Not verified"
        st.markdown(f"**Verification:**  \n{status}  \n<span class='small-muted'>(MVP Verification — simulated, "
                    "not real institutional verification)</span>", unsafe_allow_html=True)

    st.markdown("#### What would you like to do?")
    b1, b2 = st.columns(2)
    b1.button("🚗 Offer a Ride", on_click=go_to, args=("Offer a Ride",), type="primary")
    b2.button("🔍 Find a Ride", on_click=go_to, args=("Find a Ride",), type="primary")

    uid = current_user_id()
    active_rides = fetch_one("SELECT COUNT(*) AS n FROM rides WHERE driver_id = ? AND status IN ('active','full')",
                             (uid,))["n"]
    pending_for_me = fetch_one("""SELECT COUNT(*) AS n FROM ride_requests rr JOIN rides r ON r.id = rr.ride_id
                                  WHERE r.driver_id = ? AND rr.status = 'pending'""", (uid,))["n"]
    my_pending = fetch_one("SELECT COUNT(*) AS n FROM ride_requests WHERE passenger_id = ? AND status = 'pending'",
                           (uid,))["n"]
    accepted = fetch_one("""SELECT COUNT(*) AS n FROM ride_passengers rp JOIN rides r ON r.id = rp.ride_id
                            WHERE rp.passenger_id = ? AND rp.status = 'accepted'
                              AND r.status IN ('active','full')""", (uid,))["n"]
    unread = count_unread_notifications(uid)

    st.markdown("#### Your activity")
    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Active rides (driver)", active_rides)
    m2.metric("Pending requests", pending_for_me + my_pending,
              help=f"{pending_for_me} waiting for you to answer, {my_pending} you sent")
    m3.metric("Accepted rides", accepted)
    m4.metric("Unread notifications", unread)

    latest = fetch_all("SELECT * FROM notifications WHERE user_id = ? AND is_read = 0 ORDER BY id DESC LIMIT 3", (uid,))
    if latest:
        st.markdown("#### Latest notifications")
        for n in latest:
            st.info(f"**{n['title']}** — {n['message']}")

    st.divider()
    section_demo_data()


def section_demo_data():
    with st.expander("🧪 Demo Data — test route matching instantly", expanded=not demo_data_exists()):
        st.write("Creates organizations (NUST, FAST University, COMSATS, ABC Company), demo users, and rides "
                 "around Islamabad for **tomorrow**. Routes are calculated live with OSRM.")
        user_count = fetch_one("SELECT COUNT(*) AS n FROM users WHERE email NOT LIKE ?",
                               (f"%{DEMO_EMAIL_SUFFIX}",))["n"]
        if user_count:
            st.caption(f"Your database already has {user_count} non-demo user(s). They will NOT be changed.")

        if demo_data_exists():
            st.success("Demo data is loaded.")
            confirm = st.checkbox("Yes, delete the existing demo data and create it again "
                                  "(refreshes ride dates to tomorrow).")
            if st.button("Reset Demo Data", disabled=not confirm):
                with st.spinner("Recreating demo data and calculating routes..."):
                    delete_demo_data()
                    warnings = load_demo_data()
                for w in warnings:
                    st.warning(w)
                set_flash("Demo data reset successfully.")
                st.rerun()
        else:
            if st.button("Load Demo Data", type="primary"):
                with st.spinner("Creating demo data and calculating routes with OSRM..."):
                    warnings = load_demo_data()
                for w in warnings:
                    st.warning(w)
                set_flash("Demo data loaded! Log in as sara@demo.rideshare / demo123 and open Find a Ride.")
                st.rerun()

        st.markdown("**Demo accounts** (password `demo123`, admin password `admin123`)")
        st.dataframe(pd.DataFrame([
            ["sara@demo.rideshare", "Passenger (NUST)", "Search for rides"],
            ["ahmed@demo.rideshare", "Driver (NUST)", "F-10 → NUST at 8:00 AM, 3 seats"],
            ["bilal@demo.rideshare", "Driver (NUST)", "F-7 → NUST at 8:30 AM, 2 seats"],
            ["hina@demo.rideshare", "Driver (NUST)", "I-8 → NUST at 8:05 AM, FULL"],
            ["ali@demo.rideshare", "Driver (FAST)", "F-10 → FAST at 8:00 AM (other org)"],
            ["zain@demo.rideshare", "Passenger (NUST)", "Second passenger for testing"],
            ["admin@demo.rideshare", "Admin", "Admin Dashboard"],
        ], columns=["Email", "Role", "Notes"]), hide_index=True)

        st.markdown("**Test pickup points** (paste into *Pickup Location*; coordinates skip geocoding)")
        st.dataframe(pd.DataFrame(DEMO_TEST_PICKUPS, columns=["Place", "Paste this", "What to expect"]),
                     hide_index=True)


# ---- Register / Login -------------------------------------------------------
def page_auth():
    if is_logged_in():
        st.success(f"You are logged in as {st.session_state['user_name']}.")
        if st.button("Log out"):
            logout_user()
            st.rerun()
        return

    login_tab, register_tab = st.tabs(["Login", "Register"])

    with login_tab:
        with st.form("login_form"):
            email = st.text_input("Email")
            password = st.text_input("Password", type="password")
            submitted = st.form_submit_button("Log in", type="primary")
        if submitted:
            if login_user(email, password):
                st.session_state["nav_next"] = "Home"
                set_flash(f"Welcome back, {st.session_state['user_name']}!")
                st.rerun()
            else:
                st.error("Invalid email or password.")

    with register_tab:
        name = st.text_input("Full Name", key="reg_name")
        email = st.text_input("Email", key="reg_email")
        password = st.text_input("Password (min. 6 characters)", type="password", key="reg_password")

        orgs = get_organizations()
        create_label = "➕ Create a new organization"
        options = [o["name"] for o in orgs] + [create_label]
        org_choice = st.selectbox("Organization", options, key="reg_org")

        new_org_name, new_org_type, new_org_domain = "", "University", ""
        if org_choice == create_label:
            c1, c2, c3 = st.columns(3)
            new_org_name = c1.text_input("Organization name", placeholder="University of Example")
            new_org_type = c2.selectbox("Type", ORGANIZATION_TYPES)
            new_org_domain = c3.text_input("Email domain (optional)", placeholder="example.edu")

        role = st.selectbox("Role", USER_ROLES, format_func=lambda r: {
            "passenger": "Passenger (I need rides)", "driver": "Driver (I offer rides)",
            "both": "Both"}[r], key="reg_role")

        st.markdown("**MVP Verification**")
        verified = st.checkbox("I confirm I belong to this organization.", value=True, key="reg_verified")
        st.caption("⚠️ This is a simulated check for the MVP. It is NOT real institutional verification.")

        if st.button("Create account", type="primary"):
            if org_choice == create_label:
                if len(new_org_name.strip()) < 2:
                    st.error("Please enter the new organization's name.")
                    return
                org_id = get_or_create_organization(new_org_name, new_org_type, new_org_domain)
            else:
                org_id = next(o["id"] for o in orgs if o["name"] == org_choice)
                org = get_organization(org_id)
                if org["email_domain"] and not email.strip().lower().endswith(org["email_domain"]):
                    st.warning(f"Note: {org['name']} usually uses @{org['email_domain']} emails. "
                               "(Not enforced in the MVP.)")
            ok, msg = register_user(name, email, password, org_id, role, verified)
            if ok:
                st.success(msg + " Switch to the Login tab.")
            else:
                st.error(msg)


# ---- Profile ----------------------------------------------------------------
def page_profile():
    if not require_login():
        return
    uid = current_user_id()
    user = get_user(uid)
    avg, count = get_user_rating(uid)
    st.subheader(f"{user['name']}")
    st.caption(f"{rating_text(avg, count)} · {user['email']} · "
               f"{'✓ Verified (MVP Verification)' if user['is_verified'] else 'Not verified'}")

    # --- Edit profile ---
    with st.form("profile_form"):
        st.markdown("#### Edit profile")
        name = st.text_input("Name", value=user["name"])
        email = st.text_input("Email", value=user["email"])
        orgs = get_organizations()
        org_ids = [o["id"] for o in orgs]
        org_id = st.selectbox("Organization", org_ids,
                              index=org_ids.index(user["organization_id"]) if user["organization_id"] in org_ids else 0,
                              format_func=lambda i: next(o["name"] for o in orgs if o["id"] == i))
        role_options = USER_ROLES + (["admin"] if user["role"] == "admin" else [])
        role = st.selectbox("Role", role_options, index=role_options.index(user["role"]))
        saved = st.form_submit_button("Save changes", type="primary")
    if saved:
        email = email.strip().lower()
        other = get_user_by_email(email)
        if len(name.strip()) < 2 or not EMAIL_PATTERN.match(email):
            st.error("Please enter a valid name and email.")
        elif other and other["id"] != uid:
            st.error("That email is already used by another account.")
        else:
            execute("UPDATE users SET name = ?, email = ?, organization_id = ?, role = ? WHERE id = ?",
                    (name.strip(), email, org_id, role, uid))
            st.session_state.update(user_name=name.strip(), organization_id=org_id, role=role)
            st.session_state.pop("search_results", None)
            show_result(True, "Profile updated.")

    # --- Vehicles (drivers only) ---
    if user["role"] in ("driver", "both", "admin"):
        st.markdown("#### 🚙 Vehicle")
        for v in get_vehicles(uid):
            c1, c2 = st.columns([5, 1])
            c1.write(f"**{v['make']} {v['model']}** · {v['color'] or ''} · {v['license_plate'] or ''} · {v['seats']} seats")
            if c2.button("Remove", key=f"del_vehicle_{v['id']}"):
                execute("DELETE FROM vehicles WHERE id = ? AND user_id = ?", (v["id"], uid))
                show_result(True, "Vehicle removed.")
        with st.expander("Add a vehicle"):
            with st.form("vehicle_form", clear_on_submit=True):
                c1, c2 = st.columns(2)
                make = c1.text_input("Make", placeholder="Toyota")
                model = c2.text_input("Model", placeholder="Corolla")
                color = c1.text_input("Color", placeholder="White")
                plate = c2.text_input("License Plate")
                seats = st.number_input("Number of Seats (including driver)", 2, 9, 4)
                add = st.form_submit_button("Add vehicle")
            if add:
                if not make.strip() or not model.strip():
                    st.error("Please enter the make and model.")
                else:
                    execute("""INSERT INTO vehicles (user_id, make, model, color, license_plate, seats, created_at)
                               VALUES (?, ?, ?, ?, ?, ?, ?)""",
                            (uid, make.strip(), model.strip(), color.strip(), plate.strip(), int(seats), now_str()))
                    show_result(True, "Vehicle added.")

    # --- Safety: report & block ---
    st.markdown("#### 🛡️ Safety")
    members = get_org_members(user["organization_id"], uid)
    if not members:
        st.caption("No other members in your organization yet.")
        return
    member_ids = [m["id"] for m in members]
    member_name = {m["id"]: m["name"] for m in members}

    with st.expander("Report a user"):
        with st.form("report_form", clear_on_submit=True):
            reported = st.selectbox("User", member_ids, format_func=lambda i: member_name[i])
            reason = st.selectbox("Reason", REPORT_REASONS)
            description = st.text_area("What happened?")
            send = st.form_submit_button("Submit report")
        if send:
            show_result(*submit_report(uid, reported, None, reason, description))

    with st.expander("Block a user"):
        to_block = st.selectbox("User to block", member_ids, format_func=lambda i: member_name[i], key="block_select")
        if st.button("Block user"):
            show_result(*block_user(uid, to_block))
        blocked = fetch_all("""SELECT b.blocked_id, u.name FROM blocked_users b JOIN users u ON u.id = b.blocked_id
                               WHERE b.blocker_id = ?""", (uid,))
        for b in blocked:
            c1, c2 = st.columns([5, 1])
            c1.write(f"🚫 {b['name']}")
            if c2.button("Unblock", key=f"unblock_{b['blocked_id']}"):
                show_result(*unblock_user(uid, b["blocked_id"]))


# ---- Offer a Ride -----------------------------------------------------------
def page_offer_ride():
    if not require_login():
        return
    if not can_drive():
        st.warning("Your role is **passenger**. Change it to *driver* or *both* on the Profile page to offer rides.")
        return

    uid = current_user_id()
    vehicles = get_vehicles(uid)
    max_seats = max(1, (vehicles[0]["seats"] - 1)) if vehicles else 8
    if not vehicles:
        st.info("Tip: add your vehicle on the Profile page so passengers know what to look for.")

    with st.form("offer_form"):
        st.markdown("#### Route")
        origin_text = st.text_input("Starting Location", placeholder="F-10 Islamabad")
        dest_text = st.text_input("Destination", placeholder="NUST Islamabad")
        c1, c2, c3 = st.columns(3)
        ride_date = c1.date_input("Date", value=date.today() + timedelta(days=1), min_value=date.today())
        ride_time = c2.time_input("Departure Time", value=datetime.strptime("08:00", "%H:%M").time(), step=300)
        seats = c3.number_input("Available Seats", 1, max_seats, min(3, max_seats))
        notes = st.text_area("Notes (optional)", placeholder="e.g. I can wait 5 minutes at the pickup point")
        preview_clicked = st.form_submit_button("Preview Route", type="primary")

    if preview_clicked:
        st.session_state.pop("ride_preview", None)
        if not origin_text.strip() or not dest_text.strip():
            st.error("Please enter both a starting location and a destination.")
            return
        with st.spinner("Finding locations..."):
            origin, err1 = geocode_address(origin_text)
            destination, err2 = geocode_address(dest_text) if not err1 else (None, None)
        if err1 or err2:
            st.error(("Starting location: " + err1) if err1 else ("Destination: " + err2))
            return
        with st.spinner("Calculating the road route with OSRM..."):
            route, err = get_route((origin["lat"], origin["lon"]), (destination["lat"], destination["lon"]))
        if err:
            st.error(err)
            return
        st.session_state["ride_preview"] = {
            "origin": origin, "destination": destination, "route": route,
            "date": ride_date.isoformat(), "time": ride_time.strftime("%H:%M"),
            "seats": int(seats), "notes": notes.strip(),
        }

    preview = st.session_state.get("ride_preview")
    if preview:
        st.markdown("#### Route Preview")
        st.caption(f"**From:** {preview['origin']['display_name']}  \n**To:** {preview['destination']['display_name']}")
        c1, c2, c3 = st.columns(3)
        c1.metric("Route Distance", f"{preview['route']['distance_km']} km")
        c2.metric("Estimated Driving Time", f"{preview['route']['duration_min']} minutes")
        c3.metric("Departure", f"{preview['date']} · {format_time(preview['time'])}")
        fmap = create_route_map((preview["origin"]["lat"], preview["origin"]["lon"]),
                                (preview["destination"]["lat"], preview["destination"]["lon"]),
                                preview["route"]["geometry"])
        show_map(fmap, key="offer_preview_map")

        st.write("Is this the right route? Passengers near this blue line will be matched with you.")
        b1, b2 = st.columns(2)
        if b1.button("✅ Confirm & Publish Ride", type="primary"):
            create_ride(uid, st.session_state["organization_id"], preview)
            st.session_state.pop("ride_preview", None)
            set_flash("Ride successfully published!")
            st.rerun()
        if b2.button("Discard"):
            st.session_state.pop("ride_preview", None)
            st.rerun()


# ---- Find a Ride ------------------------------------------------------------
def select_ride(ride_id):
    st.session_state["selected_ride"] = ride_id


def page_find_ride():
    if not require_login():
        return
    uid = current_user_id()
    user = get_user(uid)

    with st.form("search_form"):
        st.selectbox("Organization", [user["organization_name"] or "—"], disabled=True,
                     help="You can only match with people from your own organization.")
        pickup_text = st.text_input("Pickup Location", placeholder="G-11 Islamabad  (or coordinates: 33.6683, 72.9978)")
        c1, c2, c3 = st.columns(3)
        search_date = c1.date_input("Date", value=date.today() + timedelta(days=1), min_value=date.today())
        search_time = c2.time_input("Desired Time", value=datetime.strptime("08:00", "%H:%M").time(), step=300)
        seats = c3.number_input("Number of Seats", 1, 6, 1)
        search_clicked = st.form_submit_button("🔍 Search Rides", type="primary")

    if search_clicked:
        st.session_state.pop("selected_ride", None)
        st.session_state.pop("search_results", None)
        with st.spinner("Finding your pickup location..."):
            pickup, err = geocode_address(pickup_text)
        if err:
            st.error(err)
            return
        params = {"pickup": pickup, "date": search_date.isoformat(),
                  "time": search_time.strftime("%H:%M"), "seats": int(seats)}
        with st.spinner("Comparing your pickup with every driver's route..."):
            matches, skipped = find_matching_rides(uid, user["organization_id"], pickup,
                                                   params["date"], params["time"], params["seats"])
        st.session_state["search_results"] = {"matches": matches, "skipped": skipped}
        st.session_state["search_params"] = params

    results = st.session_state.get("search_results")
    params = st.session_state.get("search_params")
    if not results or not params:
        return

    matches = results["matches"]
    st.caption(f"📍 Pickup: {params['pickup']['display_name']}")

    # --- Selected ride details (shown above the list so it's easy to see) ---
    selected_id = st.session_state.get("selected_ride")
    selected = next((m for m in matches if m["ride_id"] == selected_id), None)
    if selected:
        show_ride_details(selected, params)
        st.divider()

    if not matches:
        skipped = results["skipped"]
        hints = []
        if skipped["too_far"]:
            hints.append(f"{skipped['too_far']} ride(s) pass more than {MAX_ROUTE_DISTANCE_KM} km from your pickup")
        if skipped["wrong_time"]:
            hints.append(f"{skipped['wrong_time']} ride(s) leave more than {MAX_TIME_DIFFERENCE_MINUTES} min "
                         "from your time")
        if skipped["not_enough_seats"]:
            hints.append(f"{skipped['not_enough_seats']} ride(s) don't have enough seats")
        st.warning("**No strong matches found.**\n\nTry:\n- A wider pickup area (a main road or nearby landmark)\n"
                   "- A different departure time\n- Another date" +
                   ("\n\nOn this date: " + "; ".join(hints) + "." if hints else ""))
        return

    st.markdown(f"#### {len(matches)} matching ride{'s' if len(matches) != 1 else ''} (best first)")
    for m in matches:
        show_match_card(m, params)


def show_match_card(m, params):
    with st.container(border=True):
        top1, top2 = st.columns([3, 1])
        top1.markdown(match_badge(m["match_score"]), unsafe_allow_html=True)
        top2.button("View Ride", key=f"view_{m['ride_id']}", on_click=select_ride, args=(m["ride_id"],))

        c1, c2, c3 = st.columns(3)
        c1.markdown(f"**Driver:** {m['driver_name']}  \n**Rating:** "
                    f"{rating_text(m['driver_rating'], m['driver_rating_count'])}")
        c2.markdown(f"**From:** {short_address(m['origin_address'])}  \n**To:** {short_address(m['destination_address'])}")
        c3.markdown(f"**Departure:** {format_time(m['departure_time'])}  \n**Seats:** {m['available_seats']} available")

        st.markdown(f"**Pickup:** {short_address(params['pickup']['display_name'])} · "
                    f"**Distance from route:** {m['distance_from_route_km']:.1f} km")

        route_label = route_proximity_label(m["distance_from_route_km"])
        time_label = time_compatibility_label(m["time_diff_minutes"])
        tags = [f"✓ Same {organization_word(m['organization_type'])}"]
        tags.append(f"{'✓' if route_label != 'Weak' else '⚠'} Route is "
                    f"{'very close' if route_label in ('Excellent', 'Very Good') else route_label.lower() + ' match'}")
        tags.append(f"{'✓' if time_label != 'Weak' else '⚠'} Time {'compatible' if time_label != 'Weak' else 'is a stretch'}")
        st.markdown(" &nbsp;&nbsp; ".join(tags))


def show_ride_details(m, params):
    ride = get_ride(m["ride_id"])
    if not ride:
        st.error("This ride no longer exists.")
        return
    uid = current_user_id()

    with st.container(border=True):
        h1, h2 = st.columns([3, 1])
        h1.markdown(f"### Ride details &nbsp; {match_badge(m['match_score'])}", unsafe_allow_html=True)
        h2.button("✕ Close", key="close_details", on_click=select_ride, args=(None,))

        c1, c2 = st.columns(2)
        avg, count = get_user_rating(ride["driver_id"])
        c1.markdown(f"""
**Driver:** {ride['driver_name']}
**Driver rating:** {rating_text(avg, count)}
**Organization:** {ride['organization_name']}
**Vehicle:** {describe_vehicle(ride['driver_id'])}
**Origin:** {ride['origin_address']}
**Destination:** {ride['destination_address']}
""")
        c2.markdown(f"""
**Departure:** {ride['departure_date']} at {format_time(ride['departure_time'])}
**Available seats:** {ride['available_seats']} of {ride['total_seats']}
**Route distance:** {ride['route_distance_km']} km
**Estimated duration:** {ride['route_duration_min']:.0f} minutes
**Match score:** {m['match_score']}%
**Notes:** {ride['notes'] or '—'}
""")
        st.markdown("**Why this is a match:**")
        show_reasons(m["match_reason"])
        with st.expander("Score breakdown"):
            s = m["score"]
            st.write(f"Route proximity: {s['route_score']} × {WEIGHT_ROUTE} · Time: {s['time_score']} × {WEIGHT_TIME} · "
                     f"Organization: {s['org_score']} × {WEIGHT_DESTINATION_ORG} · Seats: {s['seat_score']} × {WEIGHT_SEATS}"
                     f" = **{m['match_score']}**")

        show_ride_map(ride, pickup=(params["pickup"]["lat"], params["pickup"]["lon"]),
                      closest_point=m["closest_point"], key=f"details_map_{ride['id']}")
        st.caption("🟢 Driver start · 🔴 Destination · 🔵 Your pickup · orange dashes = distance to route")

        existing = fetch_one("""SELECT status FROM ride_requests WHERE ride_id = ? AND passenger_id = ?
                                AND status IN ('pending','accepted')""", (ride["id"], uid))
        if existing:
            st.info(f"You already have a **{existing['status']}** request for this ride.")
        elif st.button(f"🙋 Request Seat ({params['seats']})", type="primary", key=f"request_{ride['id']}"):
            show_result(*create_ride_request(uid, m, params))


# ---- My Rides ---------------------------------------------------------------
def page_my_rides():
    if not require_login():
        return
    uid = current_user_id()
    offered_tab, joined_tab = st.tabs(["🚗 Offered Rides", "🙋 Joined Rides"])

    with offered_tab:
        rides = fetch_all("SELECT * FROM rides WHERE driver_id = ? ORDER BY departure_date DESC, departure_time DESC",
                          (uid,))
        if not rides:
            st.info("You haven't offered any rides yet.")
        groups = [("Upcoming rides", ("active", "full")), ("Completed rides", ("completed",)),
                  ("Cancelled rides", ("cancelled",))]
        for title, statuses in groups:
            group = [r for r in rides if r["status"] in statuses]
            if group:
                st.markdown(f"#### {title} ({len(group)})")
                for ride in group:
                    show_offered_ride(ride, uid)

    with joined_tab:
        show_joined_rides(uid)


def show_offered_ride(ride, uid):
    label = (f"{ride['departure_date']} · {format_time(ride['departure_time'])} · "
             f"{short_address(ride['origin_address'])} → {short_address(ride['destination_address'])} · "
             f"{ride['status'].upper()}")
    with st.expander(label):
        st.write(f"Seats: {ride['available_seats']} free of {ride['total_seats']} · "
                 f"Route: {ride['route_distance_km']} km, ~{ride['route_duration_min']:.0f} min")
        passengers = fetch_all("""SELECT rp.*, u.name FROM ride_passengers rp JOIN users u ON u.id = rp.passenger_id
                                  WHERE rp.ride_id = ? AND rp.status IN ('accepted','completed')""", (ride["id"],))
        if passengers:
            st.markdown("**Passengers:**")
            for p in passengers:
                st.write(f"• {p['name']} — pickup: {short_address(p['pickup_address'], 3)} ({p['seats']} seat(s))")
        else:
            st.caption("No passengers yet.")

        if ride["status"] in ("active", "full"):
            c1, c2 = st.columns(2)
            if c1.button("✅ Mark as completed", key=f"complete_{ride['id']}"):
                show_result(*complete_ride(ride["id"], uid))
            confirm = c2.checkbox("Confirm cancel", key=f"confirm_cancel_{ride['id']}")
            if c2.button("❌ Cancel ride", key=f"cancel_{ride['id']}", disabled=not confirm):
                show_result(*cancel_ride(ride["id"], uid))

        if ride["status"] == "completed":
            for p in passengers:
                rating_form(ride["id"], uid, p["passenger_id"], p["name"])


def show_joined_rides(uid):
    requests_rows = fetch_all(
        """SELECT rr.*, r.departure_date, r.departure_time, r.origin_address, r.destination_address,
                  r.status AS ride_status, r.driver_id, u.name AS driver_name
           FROM ride_requests rr JOIN rides r ON r.id = rr.ride_id JOIN users u ON u.id = r.driver_id
           WHERE rr.passenger_id = ? ORDER BY rr.id DESC""", (uid,))
    seats = fetch_all(
        """SELECT rp.*, r.departure_date, r.departure_time, r.origin_address, r.destination_address,
                  r.status AS ride_status, r.driver_id, u.name AS driver_name
           FROM ride_passengers rp JOIN rides r ON r.id = rp.ride_id JOIN users u ON u.id = r.driver_id
           WHERE rp.passenger_id = ? ORDER BY r.departure_date DESC""", (uid,))

    def ride_label(row):
        return (f"{row['departure_date']} · {format_time(row['departure_time'])} · with {row['driver_name']} · "
                f"{short_address(row['origin_address'])} → {short_address(row['destination_address'])}")

    pending = [r for r in requests_rows if r["status"] == "pending"]
    accepted = [s for s in seats if s["status"] == "accepted" and s["ride_status"] in ("active", "full")]
    completed = [s for s in seats if s["ride_status"] == "completed" and s["status"] in ("accepted", "completed")]
    cancelled = [r for r in requests_rows if r["status"] in ("rejected", "cancelled")]

    if not (pending or accepted or completed or cancelled):
        st.info("You haven't joined any rides yet. Go to **Find a Ride** to search.")

    if pending:
        st.markdown(f"#### Pending requests ({len(pending)})")
        for r in pending:
            c1, c2 = st.columns([5, 1])
            c1.write(f"⏳ {ride_label(r)} · {r['match_score']}% match")
            if c2.button("Cancel", key=f"cancel_req_{r['id']}"):
                show_result(*cancel_my_request(r["id"], uid))

    if accepted:
        st.markdown(f"#### Accepted rides ({len(accepted)})")
        for s in accepted:
            with st.expander(f"✅ {ride_label(s)}"):
                st.write(f"Pickup: {s['pickup_address']}")
                st.caption("Use the Messages page to coordinate with your driver.")
                confirm = st.checkbox("Confirm leaving this ride", key=f"confirm_leave_{s['id']}")
                if st.button("Cancel my seat", key=f"leave_{s['id']}", disabled=not confirm):
                    show_result(*leave_ride(s["ride_id"], uid))

    if completed:
        st.markdown(f"#### Completed rides ({len(completed)})")
        for s in completed:
            with st.expander(f"🏁 {ride_label(s)}"):
                rating_form(s["ride_id"], uid, s["driver_id"], s["driver_name"])

    if cancelled:
        st.markdown(f"#### Cancelled / rejected ({len(cancelled)})")
        for r in cancelled:
            st.write(f"✗ {ride_label(r)} · {r['status']}")


def rating_form(ride_id, reviewer_id, reviewed_id, reviewed_name):
    """Small rating form, hidden if already rated."""
    if reviewer_id == reviewed_id:
        return
    already = fetch_one("SELECT rating FROM ratings WHERE ride_id = ? AND reviewer_id = ? AND reviewed_user_id = ?",
                        (ride_id, reviewer_id, reviewed_id))
    if already:
        st.write(f"You rated {reviewed_name}: {'⭐' * already['rating']}")
        return
    with st.form(f"rate_{ride_id}_{reviewed_id}"):
        st.markdown(f"**Rate {reviewed_name}**")
        stars = st.select_slider("Stars", options=[1, 2, 3, 4, 5], value=5, format_func=lambda x: "⭐" * x)
        comment = st.text_input("Comment (optional)")
        if st.form_submit_button("Submit rating"):
            show_result(*submit_rating(ride_id, reviewer_id, reviewed_id, stars, comment))


# ---- Ride Requests (driver view) ---------------------------------------------
def page_ride_requests():
    if not require_login():
        return
    uid = current_user_id()
    rows = fetch_all(
        """SELECT rr.*, u.name AS passenger_name, r.departure_date, r.departure_time, r.available_seats,
                  r.origin_address, r.destination_address, r.status AS ride_status
           FROM ride_requests rr
           JOIN rides r ON r.id = rr.ride_id
           JOIN users u ON u.id = rr.passenger_id
           WHERE r.driver_id = ?
           ORDER BY rr.match_score DESC, rr.id""", (uid,))
    pending = [r for r in rows if r["status"] == "pending"]

    st.markdown(f"#### Pending Requests ({len(pending)})")
    if not pending:
        st.info("No pending requests right now. Passengers who match your route will appear here.")
    for r in pending:
        with st.container(border=True):
            c1, c2 = st.columns([3, 1])
            c1.markdown(f"""
**Passenger:** {r['passenger_name']} &nbsp; {match_badge(r['match_score'] or 0)}
**Ride:** {r['departure_date']} · {format_time(r['departure_time'])} · {short_address(r['origin_address'])} → {short_address(r['destination_address'])}
**Pickup:** {short_address(r['pickup_address'], 3)}
**Requested Time:** {format_time(r['requested_time'])} · **Seats:** {r['seats_requested']} (you have {r['available_seats']} free)
""", unsafe_allow_html=True)
            c1.markdown("**Reason:**")
            with c1:
                show_reasons((r["match_reason"] or "").replace("the driver's route", "your route"))
            no_seats = r["available_seats"] < r["seats_requested"] or r["ride_status"] != "active"
            if c2.button("Accept", key=f"accept_{r['id']}", type="primary", disabled=no_seats):
                show_result(*accept_request(r["id"], uid))
            if c2.button("Reject", key=f"reject_{r['id']}"):
                show_result(*reject_request(r["id"], uid))
            if no_seats:
                c2.caption("Not enough seats")
            with c1.expander("Show pickup on map"):
                ride = get_ride(r["ride_id"])
                show_ride_map(ride, pickup=(r["pickup_lat"], r["pickup_lon"]), key=f"req_map_{r['id']}")

    history = [r for r in rows if r["status"] != "pending"]
    if history:
        with st.expander(f"Request history ({len(history)})"):
            st.dataframe(pd.DataFrame([{
                "Passenger": r["passenger_name"], "Ride date": r["departure_date"],
                "Time": format_time(r["departure_time"]), "Match %": r["match_score"], "Status": r["status"],
            } for r in history]), hide_index=True)


# ---- Messages -----------------------------------------------------------------
def page_messages():
    if not require_login():
        return
    uid = current_user_id()
    # Rides where I'm the driver with accepted passengers, or an accepted passenger.
    rides = fetch_all(
        """SELECT DISTINCT r.* FROM rides r
           LEFT JOIN ride_passengers rp ON rp.ride_id = r.id AND rp.status IN ('accepted','completed')
           WHERE r.status != 'cancelled'
             AND ((r.driver_id = ? AND rp.id IS NOT NULL) OR rp.passenger_id = ?)
           ORDER BY r.departure_date DESC""", (uid, uid))
    if not rides:
        st.info("Messages are available once a driver accepts a passenger on a ride.")
        return

    ride_ids = [r["id"] for r in rides]
    ride_map = {r["id"]: r for r in rides}
    ride_id = st.selectbox("Ride", ride_ids, format_func=lambda i: (
        f"{ride_map[i]['departure_date']} · {format_time(ride_map[i]['departure_time'])} · "
        f"{short_address(ride_map[i]['origin_address'])} → {short_address(ride_map[i]['destination_address'])}"))

    if not is_ride_participant(ride_id, uid):   # security check
        st.error("You are not part of this ride.")
        return

    others = [get_user(p) for p in get_ride_participant_ids(ride_id) if p != uid]
    msgs = fetch_all(
        """SELECT m.*, s.name AS sender_name, rcv.name AS receiver_name
           FROM messages m JOIN users s ON s.id = m.sender_id JOIN users rcv ON rcv.id = m.receiver_id
           WHERE m.ride_id = ? AND (m.sender_id = ? OR m.receiver_id = ?)
           ORDER BY m.id""", (ride_id, uid, uid))

    st.markdown("#### Messages")
    if not msgs:
        st.caption("No messages yet. Say hello!")
    for m in msgs:
        with st.chat_message("user" if m["sender_id"] == uid else "assistant",
                             avatar="🙂" if m["sender_id"] == uid else "🚗"):
            st.markdown(f"**{m['sender_name']}** → {m['receiver_name']} "
                        f"<span class='small-muted'>{m['created_at'][5:16]}</span>", unsafe_allow_html=True)
            st.write(m["message"])

    with st.form("message_form", clear_on_submit=True):
        receiver = st.selectbox("To", [o["id"] for o in others],
                                format_func=lambda i: next(o["name"] for o in others if o["id"] == i))
        text = st.text_input("Message", placeholder="I will leave at 8:00 AM.")
        if st.form_submit_button("Send Message", type="primary"):
            show_result(*send_message(ride_id, uid, receiver, text))


# ---- Notifications ----------------------------------------------------------
def page_notifications():
    if not require_login():
        return
    uid = current_user_id()
    unread = fetch_all("SELECT * FROM notifications WHERE user_id = ? AND is_read = 0 ORDER BY id DESC", (uid,))
    st.markdown(f"#### Unread ({len(unread)})")
    if not unread:
        st.info("You're all caught up! 🎉")
    else:
        if st.button("Mark all as read"):
            execute("UPDATE notifications SET is_read = 1 WHERE user_id = ?", (uid,))
            st.rerun()
    for n in unread:
        with st.container(border=True):
            c1, c2 = st.columns([5, 1])
            c1.markdown(f"**{n['title']}**  \n{n['message']}  \n<span class='small-muted'>{n['created_at']}</span>",
                        unsafe_allow_html=True)
            if c2.button("Mark as read", key=f"read_{n['id']}"):
                execute("UPDATE notifications SET is_read = 1 WHERE id = ? AND user_id = ?", (n["id"], uid))
                st.rerun()

    read = fetch_all("SELECT * FROM notifications WHERE user_id = ? AND is_read = 1 ORDER BY id DESC LIMIT 50", (uid,))
    if read:
        with st.expander(f"Read notifications ({len(read)})"):
            for n in read:
                st.write(f"**{n['title']}** — {n['message']}  ({n['created_at']})")


# ---- Admin Dashboard ------------------------------------------------------------
def page_admin():
    if not require_login():
        return
    if st.session_state.get("role") != "admin":
        st.error("Only admins can view this page.")
        return

    def count(sql):
        return fetch_one(sql)["n"]

    m1, m2, m3, m4, m5 = st.columns(5)
    m1.metric("Total Users", count("SELECT COUNT(*) AS n FROM users"))
    m2.metric("Total Organizations", count("SELECT COUNT(*) AS n FROM organizations"))
    m3.metric("Active Rides", count("SELECT COUNT(*) AS n FROM rides WHERE status = 'active'"))
    m4.metric("Pending Requests", count("SELECT COUNT(*) AS n FROM ride_requests WHERE status = 'pending'"))
    m5.metric("Open Reports", count("SELECT COUNT(*) AS n FROM reports WHERE status = 'open'"))

    users_tab, orgs_tab, rides_tab, reports_tab = st.tabs(["Users", "Organizations", "Rides", "Reports"])
    with users_tab:
        # Note: the password column is deliberately NOT selected.
        st.dataframe(pd.DataFrame(fetch_all(
            """SELECT u.id, u.name, u.email, o.name AS organization, u.role, u.is_verified, u.created_at
               FROM users u LEFT JOIN organizations o ON o.id = u.organization_id ORDER BY u.id""")),
            hide_index=True)
    with orgs_tab:
        st.dataframe(pd.DataFrame(fetch_all("SELECT * FROM organizations ORDER BY id")),
                     hide_index=True)
    with rides_tab:
        st.dataframe(pd.DataFrame(fetch_all(
            """SELECT r.id, u.name AS driver, o.name AS organization, r.origin_address, r.destination_address,
                      r.departure_date, r.departure_time, r.available_seats, r.total_seats,
                      r.route_distance_km, r.status
               FROM rides r JOIN users u ON u.id = r.driver_id JOIN organizations o ON o.id = r.organization_id
               ORDER BY r.id DESC""")), hide_index=True)
    with reports_tab:
        reports = fetch_all(
            """SELECT rp.*, a.name AS reporter, b.name AS reported
               FROM reports rp JOIN users a ON a.id = rp.reporter_id JOIN users b ON b.id = rp.reported_user_id
               ORDER BY rp.id DESC""")
        if not reports:
            st.info("No reports yet.")
        for r in reports:
            with st.container(border=True):
                c1, c2 = st.columns([4, 1])
                c1.markdown(f"**#{r['id']} · {r['reason']}** — {r['reporter']} reported **{r['reported']}**  \n"
                            f"{r['description'] or '(no description)'}  \n"
                            f"<span class='small-muted'>{r['created_at']}</span>", unsafe_allow_html=True)
                new_status = c2.selectbox("Status", REPORT_STATUSES, index=REPORT_STATUSES.index(r["status"]),
                                          key=f"report_status_{r['id']}", format_func=str.capitalize)
                if new_status != r["status"]:
                    execute("UPDATE reports SET status = ? WHERE id = ?", (new_status, r["id"]))
                    show_result(True, f"Report #{r['id']} marked as {new_status}.")


# =============================================================================
# 13. MAIN APPLICATION
# =============================================================================
PAGE_FUNCTIONS = {
    "Home": page_home,
    "Register / Login": page_auth,
    "Profile": page_profile,
    "Offer a Ride": page_offer_ride,
    "Find a Ride": page_find_ride,
    "My Rides": page_my_rides,
    "Ride Requests": page_ride_requests,
    "Messages": page_messages,
    "Notifications": page_notifications,
    "Admin Dashboard": page_admin,
}


def sidebar():
    """Navigation menu + login status. Returns the chosen page name."""
    with st.sidebar:
        st.markdown("## 🚗 RideShare")
        if is_logged_in():
            user = get_user(current_user_id())
            if not user:   # e.g. demo data was reset while logged in
                logout_user()
                st.rerun()
            st.markdown(f"**{user['name']}**  \n{user['organization_name'] or ''} · {user['role']}")
            unread = count_unread_notifications(user["id"])
            if unread:
                st.markdown(f"🔔 **{unread}** unread notification{'s' if unread != 1 else ''}")
            pages = [p for p in PAGES if p != "Register / Login"]
            if user["role"] != "admin":
                pages.remove("Admin Dashboard")
        else:
            st.caption("Not logged in")
            pages = ["Home", "Register / Login"]

        # A page switch requested after the menu was drawn is applied here, before drawing it again.
        if "nav_next" in st.session_state:
            st.session_state["nav"] = st.session_state.pop("nav_next")
        if st.session_state.get("nav") not in pages:
            st.session_state["nav"] = "Home"
        choice = st.radio("Navigate", pages, key="nav", label_visibility="collapsed")

        if is_logged_in():
            st.divider()
            if st.button("Log out"):
                logout_user()
                st.session_state["nav_next"] = "Home"
                st.rerun()
    return choice


def main():
    st.set_page_config(page_title="RideShare MVP", page_icon="🚗", layout="wide")
    st.markdown(CUSTOM_CSS, unsafe_allow_html=True)

    try:
        init_db()
        page = sidebar()
        st.title("🚗 RideShare")
        st.caption("Find people from your organization who are going your way.")
        show_flash()
        PAGE_FUNCTIONS[page]()
    except sqlite3.Error:
        st.error("A database error occurred. Please refresh the page and try again.")
    except Exception as error:
        # Streamlit uses special exceptions for st.rerun()/st.stop(); let those through.
        if type(error).__name__ in ("RerunException", "StopException"):
            raise
        st.error("Something went wrong. Please refresh the page and try again.")
        if st.session_state.get("role") == "admin":
            with st.expander("Technical details (admins only)"):
                st.exception(error)


if __name__ == "__main__":
    main()
