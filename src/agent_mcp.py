"""Minimal Lean checker client."""
from __future__ import annotations

import os
import json
import socket
import ssl
import urllib.error
import urllib.request


LEAN_CHECKER_URL = os.environ.get("LEAN_CHECKER_URL", "https://scilibai.ru/grag").rstrip("/")
_forced_schema = os.environ.get("AI4SCIENCE_LEAN_SCHEMA")
LEAN_SCHEMA = _forced_schema if _forced_schema in ("scilib", "lean-checker") else ("scilib" if "/grag" in LEAN_CHECKER_URL else "lean-checker")
LEAN_DISABLED = os.environ.get("AI4SCIENCE_LEAN_DISABLED") == "1"
LEAN_CONNECT_TIMEOUT = 5
LEAN_READ_TIMEOUT = 15

def _lean_format_ok_scilib(data: dict) -> str:
    time_ms = data.get("time_ms") or data.get("processing_time_ms") or 0
    return f"OK: Lean 4 code compiles (Mathlib imported, {time_ms} ms)."

def _lean_format_err_scilib(data: dict) -> str:
    if not data.get("sanity_ok", True):
        reason = data.get("sanity_reason", "unknown")
        return f"ERROR [SANITY_CHECK_FAILED]: {reason}\nNote: Lean checker rejects sorry-only proofs, bare imports, comment-only or natural-language submissions. Provide a real Lean 4 term or tactic block."
    cls = data.get("error_class") or "ERROR"
    msg = (data.get("error_message") or "").strip()
    return f"ERROR [{cls}]: {msg[:1500]}"

def _lean_format_ok_legacy() -> str:
    return "OK: Lean 4 code compiles successfully (Mathlib imported)."

def _lean_format_err_legacy(payload: dict) -> str:
    msgs = payload.get("messages") or []
    if not msgs:
        return f"ERROR (rc={payload.get('returncode')}):\nstdout:\n{(payload.get('stdout') or '').strip()}\nstderr:\n{(payload.get('stderr') or '').strip()}"
    lines = [f"ERROR: Lean reported {len(msgs)} diagnostic(s):"]
    for message in msgs:
        location = f"L{message.get('line')}:C{message.get('column')}" if message.get("line") is not None else "?"
        lines.append(f"  [{message.get('severity') or '?'} @ {location}] {(message.get('message') or '').strip()}")
    return "\n".join(lines)

def _is_remote_unavailable(exc: Exception) -> bool:
    if isinstance(exc, (urllib.error.URLError, TimeoutError, socket.timeout, ssl.SSLError)):
        return True
    return type(exc).__name__ in {"ConnectionError", "ReadTimeout", "ConnectTimeout", "SSLError", "SSLEOFError"}

def lean_check(code: str, timeout: int = 15) -> str:
    """Verify Lean 4 code against Mathlib and return a human-readable result."""
    if LEAN_DISABLED:
        return "ERROR: lean_check is disabled via AI4SCIENCE_LEAN_DISABLED."
    url = f"{LEAN_CHECKER_URL}/check"
    body = {"lean_code": code, "timeout": max(5, min(60, int(timeout)))} if LEAN_SCHEMA == "scilib" else {"code": code, "import_line": "import Mathlib"}
    last_error = None
    for _ in (1, 2):
        try:
            request = urllib.request.Request(
                url,
                data=json.dumps(body).encode("utf-8"),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(request, timeout=max(int(timeout), LEAN_READ_TIMEOUT)) as result:
                status_code = result.status
                response_text = result.read().decode("utf-8")
            break
        except Exception as exc:
            if _is_remote_unavailable(exc):
                last_error = f"{type(exc).__name__}: {str(exc)[:200]}"
                continue
            return f"ERROR: unexpected exception from Lean checker: {type(exc).__name__}: {exc}"
    else:
        return f"OFFLINE: Lean verification endpoint unreachable ({LEAN_CHECKER_URL}). Last error: {last_error}."
    if status_code != 200:
        return f"ERROR: Lean checker HTTP {status_code}: {response_text[:500]}"
    try:
        data = json.loads(response_text)
    except ValueError:
        return f"ERROR: Lean checker returned non-JSON: {response_text[:300]}"
    if LEAN_SCHEMA == "scilib":
        return _lean_format_ok_scilib(data) if data.get("success") else _lean_format_err_scilib(data)
    return _lean_format_ok_legacy() if data.get("ok") else _lean_format_err_legacy(data)
