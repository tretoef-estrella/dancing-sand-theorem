# How to verify

**No step of the proof uses a computer.** The proof is in [the paper](paper/THE_DANCING_SAND_THEOREM_v8.pdf) (version 8) and can be checked with pencil and paper; [WHERE_TO_ATTACK.md](WHERE_TO_ATTACK.md) says where to press. The checks in this repository are corroboration. They test the statements of the proof, and its final numbers, on every case small enough to compute, and most of them carry a **control**: a deliberately wrong variant that must fail. A control that cannot fail checks nothing, so each control is printed together with the number of cases in which it failed.

All the runs recorded here were made on a laptop (a MacBook Air with 8 GB of memory), inside a watchdog that kills any run above 1.2 GB of memory or ten minutes of time. A log counts only if its last line begins with `VIGIA-FIN-OK`; that line also reports the peak memory and the time.

## What you need

- **Python 3**. Only `gate_direct.py` needs **NumPy**.
- Optionally the watchdog [checks/vigia.sh](checks/vigia.sh). It uses the macOS tool `footprint`, and its comments are in Spanish; on other systems run the commands below directly.

## Five minutes: the theorem itself

From the folder [checks/](checks/):

```
python3 gate/gate_direct.py 11
```

For `n = 2, …, 11` it computes the 2-adic Smith form of the Laplacian of the cube `Q_n` and of the folded cube `Q_n/⟨𝟙⟩` directly, and compares them with the rule of the Main Theorem and with the fold law. It prints one line per `n`, then `BAD 0`, and its three controls:
- the rule without the pooling fails at `n = 6, 10`;
- the rule without the term `h(D)` fails at `n = 2` and `4, …, 11`;
- the quotient by `x_1x_2` in place of the antipode does not halve the group, for every `n = 3, …, 11`.

About 15 seconds. The rule alone, with no Smith form, is [checks/gate/rule_abs.py](checks/gate/rule_abs.py): `python3 gate/rule_abs.py 2 30` prints `Syl_2 K(Q_n)` for `n = 2, …, 30` at once.

## Everything: the checks of §12.1

```
zsh run_all.sh
```

This runs every check of §12.1 of the paper, each under the watchdog, in about eight minutes. The logs of one complete run, made on 6 October 2026 from this folder exactly as it is published, are in [checks/logs/](checks/logs/). They agree line by line with the runs of 5 October on which §12.1 was written, apart from times and memory peaks ([checks/compare_with_5_october.txt](checks/compare_with_5_october.txt)).

| What is checked (paper) | Command, from `checks/` | What the log ends with | Time |
|---|---|---|---|
| Main Theorem and Theorem DW against the direct Smith forms, `n ≤ 11` | `python3 gate/gate_direct.py 11` | `BAD 0`; three controls fire | 14 s |
| Theorem D, and the closed form of Theorem 4.4 against the dance; `λ ≤ 40`, `i ≤ 6` | `python3 gate/gate_dance.py 40 6` | `mismatches 0`; without `2^{o(Δ)}` the closed form differs in 420/420 cells | 11 s |
| Propositions 5.2–5.4; Theorem 7.10 (Smith form = pooled clocks); Theorem 7.8; `λ < 64` (`λ ≤ 126` for Theorem 7.8) | `python3 gate/gate_sections5to7.py 127 3` | 0 failures; the raw clocks are rejected in all 322 cells where pooling acts | 57 s |
| Theorem 7.8 with strict (Cut); Lemma 7.2(b) where it is applied; Lemma 7.9 | `python3 gate/gate_strict_cut.py 6 4` | 16 380 houses, 0 failures; the controls fire | 43 s |
| Lemma 7.2(b) on random sequences | `python3 gate/gate_lemma72.py 9 20000` | 0 failures; the counterexample `(3,4,3,4)/(1,1,0,0)` to the version-1 statement still breaks it | 7 s |
| Theorem 6.2 (exactly one golden bijection), `|I| ≤ 5` | `python3 gate/gate_theoremO.py 5` | 69 cases, 0 with a count other than 1; the two controls fire | < 1 s |
| Corollaries 1.5–1.7; Lemma 9.7; Propositions 9.3, 9.4, 9.6; `n ≤ 200` | `python3 gate/gate_section9.py 200` | `BAD: none` | 3 s |
| §10.2 (the weights), Lemma 10.1, Lemmas 10.4–10.5 and `X̄(λ, i) ≅ 2X(λ, i)`; `λ ≤ 22`, `i ≤ 5` | `python3 gate/gate_section10.py 22 5` | `BAD [] 0`; the sign-free fold fails in 124/132 | 126 s |
| Remark (2) of §10.5 (a measurement, used nowhere) | `cd gate/remark2 && python3 gate_remark2.py KIND WEIGHTS 11` | as stated in the remark | 30–70 s each |

The table of §12.1 in the paper gives, row by row, the range, the result and the control of each check.

## Independent re-computations (§12.2)

§12.2 of the paper lists what six readers recomputed, each with code of their own and never the author's. Their code and logs are in [record/cold-readings/](record/README.md); reader `k` of §12.2 is the folder `0k-…`. For example:
- reader 1 computed the Smith form of the Laplacian of `Q_n` for `n ≤ 13`;
- reader 3 wrote the rule from §1 alone and compared it for `n ≤ 12`;
- reader 4 checked the repair of Theorem 7.8 on every house with `1 ≤ k ≤ 7`.

Each reader's report names the scripts it ran and their arguments; its logs end with the watchdog's line.

---

[README](README.md) · [The theorems](THEOREMS.md) · [Where to attack](WHERE_TO_ATTACK.md)
