# The Dancing Sand Theorem — the checks of §12.1

This folder is the folder `gate/` named in §12.1 of «The Dancing Sand Theorem — the 2-part of the sandpile group of the hypercube, for every n» (version 8, 6 October 2026), with the watchdog and the logs of one complete run.

The checks are checks, not steps of the proofs: every result of the paper has a written proof. Each check has, where §12.1 says so, a **control**: a deliberately wrong variant that must fail.

## How to run
Python 3 with NumPy (only `gate_direct.py` uses NumPy). From this folder:

    zsh run_all.sh

Each check runs under `vigia.sh`, which caps its memory at 1.2 GB and its time at 600 s, and writes the last line of its log: `VIGIA-FIN-OK`, `VIGIA-MATADO-MEMORIA` or `VIGIA-MATADO-TIEMPO`. A log counts only if its last line begins with `VIGIA-FIN-OK`. `vigia.sh` uses the macOS tool `footprint`; elsewhere run the commands of `run_all.sh` directly. Its comments are in Spanish.

## The checks and the rows of §12.1

| Log in `logs/` | Command | Row of §12.1 |
|---|---|---|
| `gate_direct_11` | `gate/gate_direct.py 11` | Main Theorem and Theorem DW against the direct 2-adic Smith forms, `n = 2, …, 11` |
| `gate_dance_40_6` | `gate/gate_dance.py 40 6` | Theorem D; Theorem 4.4 against the dance |
| `gate_sections5to7_127_3` | `gate/gate_sections5to7.py 127 3` | Propositions 5.2–5.4; Theorem 7.10; Theorem 7.8 (and a re-count of Theorem 6.2) |
| `gate_strict_cut_6_4` | `gate/gate_strict_cut.py 6 4` | Theorem 7.8, strict (Cut), Lemma 7.2(b) where applied; Lemma 7.9 |
| `gate_lemma72_9_20000` | `gate/gate_lemma72.py 9 20000` | Lemma 7.2(b) on random sequences |
| `gate_theoremO_5` | `gate/gate_theoremO.py 5` | Theorem 6.2, `|I| ≤ 5` |
| `gate_section9_200` | `gate/gate_section9.py 200` | Corollaries 1.5–1.7; Lemma 9.7; Propositions 9.3, 9.4, 9.6 |
| `gate_section10_22_5` | `gate/gate_section10.py 22 5` | the weights of §10.2; Lemma 10.1; Lemmas 10.4, 10.5 and `X̄(λ, i) ≅ 2X(λ, i)` |
| `remark2_*` | `gate/remark2/gate_remark2.py KIND WEIGHTS 11` (run inside `gate/remark2/`) | Remark (2) of §10.5 (a measurement, used nowhere) |

`rule_abs.py` is the rule of the Main Theorem, imported by `gate_direct.py` and `gate_section9.py`. `gate/remark2/engines/` holds three earlier engines of the project, copied unchanged, which `gate_remark2.py` imports.

## The run recorded here
The logs were produced on 6 October 2026, on a laptop, from this folder exactly as it is published. They agree line by line with the runs of 5 October 2026 on which §12.1 was written, apart from the times and the memory peaks (`compare_with_5_october.txt`).
