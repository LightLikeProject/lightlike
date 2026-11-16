#!/usr/bin/env python3
"""Leak check (a hard rule, run by CI): no tracked file contains a local home-directory path, an
e-mail address other than a noreply one, an access token, a private key, a link to an AI
assistant's chat session or a session trailer, and no secrets file is tracked.

Scans the files tracked by git (`git ls-files`); binary files are skipped. Allowed: GitHub and
Anthropic noreply addresses, the project address, the example domains, and `/home/vscode/` (the
dev container's user). A finding is fixed, not allowlisted, unless it is a documented example.

  python3 -I scripts/leak_check.py        # exit 0 = clean, 1 = findings (printed)
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PATTERNS = [
    (re.compile(r"/(?:Users|home)/(?!vscode/)[A-Za-z0-9._-]+/"), "local home-directory path"),
    (re.compile(r"[A-Za-z]:\\Users\\[A-Za-z0-9._-]+"), "local home-directory path"),
    (re.compile(r"~/(?:Desktop|Documents|Downloads)/"), "local home-directory path"),
    (re.compile(r"\bgh[pousr]_[A-Za-z0-9]{30,}"), "GitHub token"),
    (re.compile(r"\bgithub_pat_[A-Za-z0-9_]{20,}"), "GitHub token"),
    (re.compile(r"\bsk-ant-[A-Za-z0-9_-]{20,}"), "Anthropic API key"),
    (re.compile(r"\bsk-[A-Za-z0-9]{32,}"), "API key"),
    (re.compile(r"\bAKIA[0-9A-Z]{16}\b"), "AWS access key"),
    (re.compile(r"\bxox[abprs]-[A-Za-z0-9-]{10,}"), "Slack token"),
    (re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----"), "private key"),
    (re.compile(r"\bclaude\.ai/(?:code/)?(?:session[_/]|chat/|share/)", re.I), "link to an AI chat session"),
    (re.compile(r"^\s*Claude-Session\s*:", re.I), "session trailer"),
]
EMAIL = re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b")
ALLOWED_EMAIL = re.compile(r"(?:@users\.noreply\.github\.com|^noreply@(?:anthropic|github)\.com|"
                           r"^lightlike\.project@gmail\.com|@example\.(?:com|org|net))$", re.I)
SECRET_FILES = re.compile(r"(?:^|/)(?:\.env(?:\..*)?|id_rsa|id_ed25519|.*\.pem|.*\.p12|credentials\.json)$")


def check(files) -> list:
    """`files`: (path, text or None for binary) pairs. Returns the findings."""
    out = []
    for path, text in files:
        if SECRET_FILES.search(path):
            out.append(f"{path}: a secrets file is tracked")
        if text is None:
            continue
        for no, line in enumerate(text.splitlines(), 1):
            for rx, what in PATTERNS:
                if rx.search(line):
                    out.append(f"{path}:{no}: {what}")
            for e in EMAIL.findall(line):
                # a domain starting with a digit is a version pin (pkg@1.2.3), not an address
                if not ALLOWED_EMAIL.search(e) and not e.split("@")[1][0].isdigit():
                    out.append(f"{path}:{no}: e-mail address {e}")
    return out


def tracked(root=ROOT):
    names = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True,
                           check=True).stdout.decode().split("\0")
    for n in filter(None, names):
        p = root / n
        if not p.is_file():
            continue
        data = p.read_bytes()
        yield n, (None if b"\0" in data[:8192] else data.decode("utf-8", errors="replace"))


def main() -> int:
    found = check(tracked())
    for f in found:
        print("FAIL", f)
    print("leak check: OK" if not found else f"leak check: FAILED ({len(found)} findings)")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
