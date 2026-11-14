#!/usr/bin/env python3
"""Shrink the doc-gen4 output for GitHub Pages (published sites must stay under 1 GB).

doc-gen4 renders every module in the import closure; Mathlib alone is about 1 GB. This script
deletes the pages of Mathlib, Lean core and their dependencies and rewrites links to them so they
point at the official Mathlib documentation, which hosts the same modules. That site follows
Mathlib master, so a few links may differ from the pinned Mathlib version.

Usage: python3 scripts/prune_docs.py docbuild/.lake/build/doc
"""
import pathlib
import re
import shutil
import sys

UPSTREAM = "https://leanprover-community.github.io/mathlib4_docs/"
EXTERNAL = ["Mathlib", "Init", "Lean", "Std", "Lake", "Batteries", "Aesop", "ImportGraph",
            "Plausible", "Qq", "ProofWidgets", "LeanSearchClient"]
LINK = re.compile(r'(href|src)="(?:\./|\.\./)*(' + "|".join(EXTERNAL) + r')(/|\.html)')


def main(root: pathlib.Path) -> None:
    rewritten = 0
    for page in root.rglob("*.html"):
        rel = page.relative_to(root).parts
        if rel[0] in EXTERNAL or rel[0].removesuffix(".html") in EXTERNAL:
            continue
        text = page.read_text(encoding="utf-8")
        new, n = LINK.subn(lambda m: f'{m.group(1)}="{UPSTREAM}{m.group(2)}{m.group(3)}', text)
        if n:
            page.write_text(new, encoding="utf-8")
            rewritten += n
    removed = 0
    for name in EXTERNAL:
        for p in (root / name, root / f"{name}.html"):
            if p.is_dir():
                shutil.rmtree(p); removed += 1
            elif p.exists():
                p.unlink(); removed += 1
    print(f"rewrote {rewritten} links to {UPSTREAM}; removed {removed} directories/pages")


if __name__ == "__main__":
    main(pathlib.Path(sys.argv[1]))
