# Logs of the Lean proof

The logs of the Lean proof of «The Dancing Sand Theorem», in four folders, and a fifth for the build on GitHub's machines. Each log keeps the name it has in the author's working tree, where the four folders are one (`logs/`); [../lean/PATHS_WORKING_TREE_TO_PUBLISHED.tsv](../lean/PATHS_WORKING_TREE_TO_PUBLISHED.tsv) maps every name.

| Folder | What it holds |
|---|---|
| [brute_force/](brute_force/) | `chkC<N>.log`: the brute-force check of piece `C<N>`, run before the piece was sent to Aristotle, with its negative controls; the script is [../lean/brute_force/](../lean/brute_force/) `chkC<N>.py`. Logs with a longer name are earlier runs, kept: their names say what went wrong. |
| [build/](build/) | `buildC<N>*.log`: the local build of the modules of piece `C<N>`, under the watchdog; the script is [../lean/build/](../lean/build/) `buildC<N>.sh`. |
| [piece_checks/](piece_checks/) | `checkC<N>.log` and `CheckC<N>.log` (the same kind of file; the case of the first letter varies): the Lean file `../lean/proyecto_cubo/checks/CheckC<N>.lean`, which restates the main statements of the piece by hand and prints their axioms. |
| [final_checks/](final_checks/) | the final checks of the certificate: `CheckCubo2.log`, `CertCubo2.log`, `DepsCubo2.log` (version 2, §1.4, §1.5, §3.3); `CheckCubo.log`, `CertCubo.log`, `DepsCubo.log` before the clean rebuild and `CheckCubo_postclean.log`, `DepsCubo_postclean.log` after it (version 1); `CheckCubo_run1.log`, the first run of `CheckCubo.lean`, which failed on a hand restatement and is kept; `CertCubo_width120.log`, an earlier run of `CertCubo.lean`, kept: a line-width option was tried after it, had no effect on the output, and was withdrawn; apart from the watchdog's last line its output is identical to `CertCubo.log`. |
| [actions/](actions/README.md) | the build of the whole project on GitHub's machines, from the files as published (run of 11 October 2026: success, 23 min 34 s), and a copy of its output, kept here because GitHub deletes run logs after 90 days. |

A log counts only if its last line begins with `VIGIA-FIN-OK`; that line reports the exit code, the peak memory and the time. The clean rebuild has its own logs, in [../lean/clean_rebuild/](../lean/clean_rebuild/). The certificate is [../lean/CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v2.pdf](../lean/CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v2.pdf).

[Lean README](../lean/README.md) · [README](../README.md)
