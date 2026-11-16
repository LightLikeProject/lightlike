"""Split the long `Poly` list literals of the generated certificate files into chunks.

A `def Y : Poly := [t1, ..., tn]` with thousands of terms is slow to elaborate (the cost of one
list literal grows faster than its length), so it is written as
`def Y_c0 : Poly := [...]`, `def Y_c1 : Poly := [...]`, ..., `def Y : Poly := Y_c0 ++ Y_c1 ++ ...`
with at most CHUNK terms per piece. The value of `Y` is unchanged.

Every chunk definition gets a docstring (the docstring check requires one for each definition).
A definition named in `caps.json` (`{"RacahCert6": {"Y6_0": 12800000, ...}}`, keyed by the file
stem) gets `set_option maxHeartbeats N in` in front, a per-declaration limit; the file-level
`set_option maxHeartbeats` line is then removed. The values in `caps.json` are twice the smallest
limit of a doubling grid (100000, 200000, ..., 6400000) at which the declaration compiles.

Library use (from the generators): `emit_def(name, terms)` where `terms` is the list of term
strings, and `rewrite(text, caps=...)`. Command line: `python3 chunk.py FILE...` rewrites the files
in place without splitting (the caps of `caps.json` next to this script apply); the rewrite is
idempotent.
"""
import json, os, re, sys

CHUNK = 100


def chunk_doc(name):
    """Docstring of the chunk definition `name` (of the form `Y_c3`)."""
    return f"/-- Chunk `{name}` of a certificate term of the Racah tree identity (generated). -/"


def emit_def(name, terms, chunk=CHUNK):
    """Lean text of `def name : Poly := ...` for the term strings `terms`."""
    if len(terms) <= chunk:
        return f"def {name} : Poly := [{', '.join(terms)}]\n"
    parts = [terms[i:i + chunk] for i in range(0, len(terms), chunk)]
    out = "".join(f"{chunk_doc(f'{name}_c{i}')}\ndef {name}_c{i} : Poly := [{', '.join(p)}]\n"
                  for i, p in enumerate(parts))
    out += f"def {name} : Poly := " + " ++ ".join(f"{name}_c{i}" for i in range(len(parts))) + "\n"
    return out


# one term is `(⟨i, ..., 0⟩, c)`; the literal is `[term, term, ...]` on one line
TERM = r"\(⟨[^⟩]*⟩, -?\d+\)"
LINE = re.compile(rf"^def (\w+) : Poly := \[({TERM}(?:, {TERM})*)\]$")


DEF = re.compile(r"^def (\w+) : Poly := ")


def rewrite(text, chunk=CHUNK, caps=None, split=True):
    """Chunk the long literals (unless `split` is false), document the chunks and apply the
    per-declaration `caps` (`{definition name: heartbeat limit}`). Idempotent. The limits of
    `caps.json` were measured on files whose literals are not split (RacahCert6/8/10, RacahTreeX0),
    so those are rewritten with `split=False`."""
    caps = caps or {}
    out = []
    for line in text.split("\n"):
        m = LINE.match(line) if split else None
        if m:
            terms = re.findall(TERM, m.group(2))
            out.extend(emit_def(m.group(1), terms, chunk).rstrip("\n").split("\n"))
        else:
            out.append(line)
    if caps:  # the limits are per declaration: drop the file-level one
        out = [l for l in out if not re.match(r"set_option maxHeartbeats \d+$", l)]
    res = []
    for line in out:
        m = DEF.match(line)
        if m:
            name = m.group(1)
            has_doc = bool(res) and res[-1].startswith("/--") and res[-1].endswith("-/")
            if not has_doc and re.search(r"_c\d+$", name):
                res.append(chunk_doc(name))
                has_doc = True
            if name in caps:
                k = len(res) - 1 if has_doc else len(res)
                opt = f"set_option maxHeartbeats {caps[name]} in"
                if not (k > 0 and res[k - 1] == opt):
                    res.insert(k, opt)
        res.append(line)
    return "\n".join(res)


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    all_caps = json.load(open(os.path.join(here, "caps.json")))
    for f in sys.argv[1:]:
        s = open(f).read()
        t = rewrite(s, caps=all_caps.get(os.path.basename(f).removesuffix(".lean")), split=False)
        open(f, "w").write(t)
        print(f, "changed" if s != t else "unchanged")
