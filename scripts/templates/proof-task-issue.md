---
name: Proof task
about: A locked Lean statement whose proof is open. Self-contained.
title: "[proof task] {{id}}: {{title}}"
labels: ["proof-task"]
---

**Task** {{id}} · size {{size}} · {{difficulty}} · area {{area}}
**File** `{{file}}` · **declaration** `{{decl}}` · **milestone** {{milestone}} · **depends on** {{deps}}
**Statement** {{lock}}: CI checks that a pull request leaves it as locked in docs/tasks/decomposition.yaml

Comment `/claim` to take this task: the issue shows the label `claimed` and you are the assignee. A
claim lasts 48 hours, or as long as a pull request naming the task is open; a person holds at most 3
claims, and `/unclaim` releases one. While it is claimed, a second `/claim` is not recorded. Claims
are advisory: if two pull requests arrive, the first that passes CI is merged. Share approaches in
this thread; see CONTRIBUTING.md, "Working on the same problem".

### Routes

{{routes}}

### How to submit

1. In `{{file}}`, replace the `sorry` with a proof. Change nothing else in the file.
2. Check it: `lake build {{module}}`.
3. Open a pull request with the line `Task: {{id}}`. A check confirms that only the proof
   changed. Once the proof is on `main`, this issue is closed.

### The task in one block

Everything needed to attempt the task, in one block to copy.

~~~~text
Prove one theorem in Lean 4.

Versions: Lean {{lean}}, Mathlib {{mathlib}}, Physlib {{physlib}}.
The file imports: {{imports}}

Constraints:
- Do not change the statement: its name, binders, hypotheses and conclusion stay exactly as given.
- No sorry, admit, native_decide, new axiom, implemented_by or extern.
- Use only Mathlib, Physlib and the definitions and lemmas below.
- Auxiliary facts go inside the proof (have, let, suffices); add no new top-level declarations.

Definitions the statement depends on:

{{definitions}}

Useful lemmas from the project (statements only):

{{lemmas}}

The statement to prove:

{{statement}}

Return only the proof: the tactic block that replaces `sorry`.
~~~~
