# The Lean build on GitHub's machines

The workflow [../../.github/workflows/lean-build.yml](../../.github/workflows/lean-build.yml) builds the Lean project from the files as published, on a fresh GitHub machine, and runs `checks/CheckCubo2.lean`.

| Run | Commit | Date (UTC) | Result |
|---|---|---|---|
| [38172080438](https://github.com/tretoef-estrella/dancing-sand-theorem/actions/runs/38172080438) | `f6d95a4` | 11 Oct 2026, 20:24:32–20:48:11 | success, 23 min 34 s |

Steps of that run: Mathlib's compiled files (1 min 41 s); the build of the 420 modules (20 min 50 s); the hand restatements of the main results and their axioms (54 s); the check that no printed axiom list contains `sorryAx` or anything beyond `propext`, `Classical.choice` and `Quot.sound`.

**Why this copy is here.** GitHub deletes the logs and the artifacts of a run after 90 days. [CheckCubo_actions_run38172080438.log](CheckCubo_actions_run38172080438.log) is the artifact of that run (`CheckCubo_actions_log`), downloaded on 11 October 2026 and unchanged: 25 lines, one per restated theorem, each depending only on the three standard axioms. It is identical, line for line, to the author's own log [../final_checks/CheckCubo2.log](../final_checks/CheckCubo2.log) without its watchdog line.

[Logs README](../README.md) · [README](../../README.md)
