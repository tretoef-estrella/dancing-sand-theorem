# Grading of the second external cold reading — «the fold law for every n» (Grepy Bross, 5 Oct 2026)

Report: `delivered_2026-10-05/REPORT_COLD.md` (md5 6f9785105ac1320abc86a5da7a9b4a80, 269 lines; 60 files stored, md5 identical to the reader's folder, `_MANIFEST_origin.txt`). Reader: «Grepy el lector frío del cubo 2», one Claude, own folder, no agents.

## Verdict
**«HOLDS» ACCEPTED. GRADE: HIGHEST MARK.**
The fold law `Syl₂K̄(n) ≅ 2·Syl₂K(Q_n)` (equivalently `Syl₂K(Q_n) ≅ (Z/2)^{a_n} ⊕ Syl₂K̄(n)⁺`) for every n now has **three readings: the pilot's (flight 9), the auditor's (`reports/VOLADOR_9/AUDIT_FLIGHT_9.md`) and this external cold reading.** The background theorems the chain uses (RT′, D, O, F, the deficit law) were read cold by the first external reader on 4 Oct (Theorem F step by step: `reports/LECTOR_FRIO_1/CALIFICACION_LECTOR_FRIO_1_v1.md`, row L7). **So the whole 2-part of K(Q_n), for every n, is PROVED by pencil and read cold externally, end to end.**

## Why the highest mark
- **Every link F1–F15 is a derivation, not a stamp.** Each row carries the reader's own computation: the group-likeness of exp F making a = (−1)^{(n−H)/2}Σ F^{(r)} (a simplification: no Schur algebra needed), the factorials of the slot formulas, Strassmann for the uniqueness of the 𝒦-representation, the Neumann/chain estimate of Lemma H, the offset bookkeeping of Lemma B (rows at o_D, columns at o_D + 2^k − 1) that no earlier reading wrote out, both continuity arguments at shift 0, the Bernoulli weights with von Staudt–Clausen.
- **Controls that can fire, and fire:** a_n ± 1, no shift, the non-antipodal fold x₁x₂ (fails n = 3..12: the law belongs to the antipode), α = 1, odd units on F with weights (first break at l = 31, as flight 9 found), Ψ ± 4, λ = 0, sign-free fold. One badly designed control (C2d) published as such.
- **Independent engines:** the Laplacians in the VERTEX basis (not the flights' s_S basis), a different Smith algorithm cross-checked against exact big-integer SNF; slot matrices derived from powers of F, not copied.
- **Sealed predictions** before each run; no mathematical prediction failed; errors E1–E9 declared.
- **Read the audits only after writing its verdict**, and disagreed where it should.

## The auditor's own checks (this turn)
- Re-ran four of its gates **with its own scripts** from a scratch copy, under `vigia.sh`: `law_direct.py 2 11` (22 s, 214 MB), `kclass_test.py lemmaB 24 4 6` (18 s), `family 20 6` (31 s), `onemove 400 2` (13 s). **All four logs IDENTICAL** to the reader's (warnings and watchdog lines excluded). Logs `logs/rerun_lector2_*.log`.
- Checked by hand its F12 objection (the arms of circ(fh)): Ψ_i and Ψ_{i+1} do not commute (4D against a series in F); its non-commutative computation `ΨY₀ + Y₀Ψ − 2Ψ + 2Y₀² − 2Y₀ ≡ [Ψ, Y₀] = 4[D, Y₀] ≡ 0 mod 2` is correct. **The reader is right; I marked that step CORRECT without comment.**

## Its disagreements with the auditor — all accepted
1. β²: my audit line presented flight 9's sentence as a strengthening of itself. Accepted (no mathematical consequence).
2. The arms of circ(fh): non-commutative slip in flight 9 §4.2, passed by my audit. Accepted; PRESENTATION, the conclusion holds.
3. Stale Jantzen II.4.13 citation in flight 6 §4.3 not flagged by the audit of flight 6. Accepted.
4. The Bernoulli weights and H-even were «owed» in audits 6–7 and marked CORRECT in audit 9 without saying they were re-derived. Accepted; now discharged by the reader.
5. Ω-even at shift 0: the line «M(Ψ_c)N₊(c) ∈ 2Mat for c ≥ 1, 2Mat closed ⇒ at c = 0» must be written. Accepted.

## Presentation items for the paper (six)
F1 stale citation; F10 (two): the odd constant coupling created by a V-split, and «translation covariant» means one global 𝒦-function per (Δ, m); F11 von Staudt–Clausen to be named; F12 the non-commutative difference of the arms; F14 the closedness line at shift 0.

## Its priority section (to be extended by the auditor's sweep)
Reiner–Tseng give the exact sequence for double covers, not the fold law; Gao et al. Remark 2.13 asks for the «deeper connection» at the first layer; Bai gives a_n and the integrality of L(L + 2)/2; CSX: «no conjecture». Nine web searches, no earlier statement. New data point: the non-antipodal fold does not double.

— Grepy Bross
