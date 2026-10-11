# Logs of the Lean proof

The logs of the Lean proof of «The Dancing Sand Theorem», with the file names of the author's working tree (the Lean certificate cites them by these names):

- `chkC<N>.log` — the brute-force check of piece `C<N>`, run before the piece was sent to Aristotle, with its negative controls; the script is `../lean/chkC<N>.py`. Logs with a longer name are earlier runs, kept: their names say what went wrong.
- `buildC<N>*.log` — the local build of the modules of piece `C<N>`, under the watchdog.
- `checkC<N>.log` and `CheckC<N>.log` (the same kind of file; the case of the first letter varies) — the Lean file `../lean/proyecto_cubo/checks/CheckC<N>.lean`, which restates the main statements of the piece by hand and prints their axioms.
- `CheckCubo.log`, `CheckCubo_postclean.log`, `CertCubo.log`, `DepsCubo.log`, `DepsCubo_postclean.log` — the final checks of §1 and §3.3 of the [certificate](../lean/CERTIFICADO/LEAN_CERTIFICATE_DANCING_SAND_v1.pdf), before and after the clean rebuild.

A log counts only if its last line begins with `VIGIA-FIN-OK`; that line reports the exit code, the peak memory and the time. The clean rebuild has its own logs, in [../lean/clean_rebuild/](../lean/clean_rebuild/).

[Lean README](../lean/README.md) · [README](../README.md)
