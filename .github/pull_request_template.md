## Task

<!-- The task ID from the task board, for example T-QU1-P5, or "none". -->
Task:

## Summary

<!-- What changed and why, for a reader who has not seen the task. -->

## AI assistance (optional)

<!-- The tools used, if any. -->

## Checklist

<!-- CI checks the build, `sorry`, imports, docstrings and, for a proof task, that only the proof
     changed (CONTRIBUTING.md#hard-rules). These items are advice; tick what applies. -->

- [ ] New definitions reproduce a known value and differ on a wrong input; main theorems have a non-vacuity example.
- [ ] Only Lean files changed; a renamed declaration keeps a `@[deprecated]` alias.
- [ ] One topic; commit messages follow the format in CONTRIBUTING.md (`type(scope): summary`, a body that says why).
- [ ] I have read the whole diff and vouch for it.
