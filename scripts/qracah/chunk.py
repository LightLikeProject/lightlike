"""Split the long `Poly` list literals of the generated certificate files into chunks.

A `def Y : Poly := [t1, ..., tn]` with thousands of terms is slow to elaborate (the cost of one
list literal grows faster than its length), so it is written as
`def Y_c0 : Poly := [...]`, `def Y_c1 : Poly := [...]`, ..., `def Y : Poly := Y_c0 ++ Y_c1 ++ ...`
with at most CHUNK terms per piece. The value of `Y` is unchanged.

Library use (from the generators): `emit_def(name, terms)` where `terms` is the list of term
strings. Command line: `python3 chunk.py FILE...` rewrites the files in place; a literal already
short is left alone, and the rewrite is idempotent.
"""
import re, sys

CHUNK = 100


def emit_def(name, terms, chunk=CHUNK):
    """Lean text of `def name : Poly := ...` for the term strings `terms`."""
    if len(terms) <= chunk:
        return f"def {name} : Poly := [{', '.join(terms)}]\n"
    parts = [terms[i:i + chunk] for i in range(0, len(terms), chunk)]
    out = "".join(f"def {name}_c{i} : Poly := [{', '.join(p)}]\n" for i, p in enumerate(parts))
    out += f"def {name} : Poly := " + " ++ ".join(f"{name}_c{i}" for i in range(len(parts))) + "\n"
    return out


# one term is `(⟨i, ..., 0⟩, c)`; the literal is `[term, term, ...]` on one line
TERM = r"\(⟨[^⟩]*⟩, -?\d+\)"
LINE = re.compile(rf"^def (\w+) : Poly := \[({TERM}(?:, {TERM})*)\]$")


def rewrite(text, chunk=CHUNK):
    out = []
    for line in text.split("\n"):
        m = LINE.match(line)
        if m:
            terms = re.findall(TERM, m.group(2))
            out.append(emit_def(m.group(1), terms, chunk).rstrip("\n"))
        else:
            out.append(line)
    return "\n".join(out)


if __name__ == "__main__":
    for f in sys.argv[1:]:
        s = open(f).read()
        t = rewrite(s)
        open(f, "w").write(t)
        print(f, "changed" if s != t else "unchanged")
