"""Small helpers for reading Lean source text, shared by `context-pack`, `proof_task_check.py`
and `tasks.py`. No Lean is run here; the helpers only scan text, skipping comments and strings."""
import re

OPEN, CLOSE = "([{⟨⦃⟦", ")]}⟩⦄⟧"

# A line at column 0 that starts a new command ends the previous declaration.
COMMAND = re.compile(
    r"^(/--|/-!|@\[|#|end\b|namespace\b|section\b|open\b|variable\b|universe\b|set_option\b|"
    r"attribute\b|example\b|instance\b|noncomputable\b|private\b|protected\b|theorem\b|lemma\b|"
    r"def\b|abbrev\b|structure\b|inductive\b|class\b|opaque\b|axiom\b|macro\b|syntax\b|"
    r"notation\b|infix\b|infixl\b|infixr\b|prefix\b|postfix\b|local\b|scoped\b|elab\b|"
    r"deriving\b|mutual\b|irreducible_def\b|alias\b|initialize\b)")

DECL_KW = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|irreducible_def)"


def code_mask(src: str) -> list[bool]:
    """For each character, whether it is code (not inside a comment or a string literal)."""
    mask = [True] * len(src)
    i, n = 0, len(src)
    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            mask[i:j] = [False] * (j - i)
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            mask[i:j] = [False] * (j - i)
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            mask[i:j] = [False] * (j - i)
            i = j
        else:
            i += 1
    return mask


def split_header(src: str):
    """Split a declaration's source at its first top-level `:=` (outside brackets, comments and
    strings). Returns (header including `:=`, body), or None if there is none (for example a
    definition by pattern matching)."""
    mask, depth = code_mask(src), 0
    for i, ch in enumerate(src):
        if not mask[i]:
            continue
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif depth == 0 and src.startswith(":=", i):
            return src[: i + 2], src[i + 2:]
        elif depth == 0 and ch == "|" and src[src.rfind("\n", 0, i) + 1:i].strip() == "":
            return None
    return None


def statement_only(src: str) -> str:
    """A theorem's source without its proof: the header, then `sorry` as a placeholder."""
    parts = split_header(src)
    return src if parts is None else parts[0].rstrip() + " by\n  sorry -- proof omitted"


def find_decl(text: str, short: str):
    """The block of the declaration whose last name component is `short`: (start, end) line
    indices, end exclusive. The block includes a preceding docstring and attributes, and ends
    before the next column-0 command. Returns None if absent or ambiguous."""
    lines = text.split("\n")
    pat = re.compile(rf"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                     rf"{DECL_KW}\s+(?:[\w.'«»]+\.)?{re.escape(short)}(?![\w'.])")
    hits = [i for i, l in enumerate(lines) if pat.match(l)]
    if len(hits) != 1:
        return None
    h = hits[0]
    start = h
    while start > 0 and (lines[start - 1].startswith("@[")):
        start -= 1
    if start > 0 and lines[start - 1].rstrip().endswith("-/"):
        k = start - 1
        while k >= 0 and not lines[k].startswith("/-"):
            k -= 1
        if k >= 0 and lines[k].startswith("/--"):
            start = k
            while start > 0 and lines[start - 1].startswith("@["):
                start -= 1
    end = h + 1
    while end < len(lines) and not COMMAND.match(lines[end]):
        end += 1
    while end > h + 1 and lines[end - 1].strip() == "":
        end -= 1
    return start, end
