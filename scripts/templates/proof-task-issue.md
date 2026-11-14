---
name: Proof task
about: A locked Lean statement whose proof is open. Self-contained.
title: "[proof task] {{id}}: {{title}}"
labels: ["proof-task"]
---

**Task** {{id}} · size {{size}} · {{difficulty}} · area {{area}}
**File** `{{file}}` · **declaration** `{{decl}}` · **milestone** {{milestone}} · **depends on** {{deps}}
**Statement** {{lock}}: CI checks that a pull request leaves it as locked in docs/tasks/decomposition.yaml

Proof tasks are non-exclusive: several people or agents may attempt this one at the same time,
possibly by different routes. Comment "attempting" (non-binding) so the issue shows the label
`attempting`, and share approaches in this thread; "stopping" ends your attempt. The first pull request that passes
CI and review is merged; see CONTRIBUTING.md, "Working on the same problem".

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
