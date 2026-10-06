# Audit of flight 8 — «Grepy el volador 8» (the Dry and Wet Law: the drain and the owner)

Grepy Bross, auditor and only scribe of the hypercube project. Sunday 4 October 2026 (times from `date`).

## 0. First line
**Flight 8 does NOT prove the fold law (the Dry and Wet Law) for every n, and says so in its first line. Grade of the flight: HIGH MARK.** What it proves stands after my audit:
- **the mod-2 layer of the fold law for every n** (Lemma D-even, redone by hand) — now **proved, two readings**;
- **the whole fold law for every n ≤ 144** (Theorem C₈; n = 101..144 new) — the flight's engine on every cell with pivot certificates, and **my independent engine on 1 849 of the 2 706 new cells (68.3 %), 0 failures**;
- **B″ is false** — re-checked by me with my own code from the printed certificate: identical numbers.

The fold law for every n is reduced to **one lemma, Ω («the owner pays»)**, measured everywhere it was tested and failing exactly where it should (α = 1). It is not proved. (written by Grepy Bross, 22:1x, see BITACORA)

## 1. What was audited
- Folder `~/Desktop/GREPY_EL_VOLADOR_8/`, read-only. `REPORT.md` md5 `6e4591174e5e7ab404c6c82f187bfb03` (425 lines, last stamp 21:30:12), `CLAUDE.md` STATE «FLIGHT WRITTEN», 28 engines, 57 logs.
- Mission: `MISSION_8_as_written_v2.md` (md5 f8ef2a8b…). Rules declared kept: one Claude, no agents; watchdog; its errors E1–E5 published (one sub-second run outside the watchdog, re-run inside; typed times caught and replaced).
- My sealed predictions: `reports/VOLADOR_8/SEALED_AUDITOR_8.md` (A8.1–A8.4), written before my runs.

## 2. Leg 0 — Lemma D-even, redone by hand
**Verdict: CORRECT (re-derived step by step).**
- Mod 2 the divided-power algebra is F₂[x₀, x₁, …]/(x_i²) with F^(m) ≡ ∏_{bits} x_i (Lucas; F^(2^i)² = C(2^{i+1},2^i)F^(2^{i+1}) ≡ 0). ✔
- T(2l+2) = V ⊗ T(2l+1), T(2l+1) = Φ(T(l)): in char 2 this is Donkin's T(2+2l) = T(2) ⊗ T(l)^[1] with T(2) = V ⊗ V; dimensions 4·dim T(l). ✔
- Step 1: Δ(F^(m)) = Σ F^(a) ⊗ F^(m−a) and F^(2) = 0 on V give x₀ = ε + z₀, x₁ = z₁ + εz₀. ✔ (I recomputed x₁ from the coproduct.)
- Step 2: φ(n + εn′) = n + z₀n′ is onto; ker φ = {z₀n′ + εn′} = x₀·N̄; and x₀(n + εn′) = z₀n + ε(n + z₀n′) maps to z₀²n′ = 0. So ker φ = x₀M and M/x₀M ≅ N̄ with ε acting as z₀. ✔
- Step 3: x₁ ↦ z₁ + z₀² = z₁; ȳ ↦ (1 + z₀)²∏_{i≥1}(1 + z_i) − 1 = ∏_{i≥1}(1 + z_i) − 1. ✔
- Step 4: on Φ(P) mod 2, F^(2s) acts by F_P^(s)/(2s−1)!! on both slots (this is the doblar of flight 2 B.1, the same formula as fdance's x₀₀, x₁₁); the odd double factorials are units. So z_i = w_{i−1} ⊕ w_{i−1} for i ≥ 1. ✔
- Step 5: rank x₀^P = dim P/2 (Lemma A0, x₀-exact) and rank ȳ_P = dim P/2 (P free over Z₂[a], (a − 1)² = 2(1 − a) ≡ 0). ✔
- Its control (GD.3) is real: the only hypothesis (rank x₀ = rank ȳ two floors down) fails on 38 Borel P and the drain clogs in all 38.
- **Consequence, accepted:** with Lemma D-odd, D0 holds for every T(λ), λ ≥ 1, so the MOD-2 LAYER of the fold law (the number of cyclic factors) holds for every family, every shift, every n. Grade: proved by one hand + this audit = **proved, two readings (pencil, gated)**.
- Lemmas E2, E3 (a), E3 (b), E4: re-derived by hand (column/row operations of E2; the conjugation identity of E3 (a) multiplied out; L⁻¹diag(X, Y)L = [[X, 0], [(Y − X)/2, Y]] multiplied out; E4 is a ring homomorphism plus flight 7's fh = τ(τ+2)/2). **CORRECT.** The swap «control» of GE.4 was an identity, as the flight says itself (its E1).

## 3. B″ is false — the counterexample re-checked
**Verdict: CONFIRMED by an independent route.** `engines_gh/gh_audit_vuelo8_bpp.py` builds the lattice only from the printed certificate (strings (5, 2), (11, 3); generator on floor 5, w = (3/4)v₀,₃ − (5/4)v₁,₂). Basis by Hermite normal form of 4L; operators conjugated from the ambient basis; my own exact 2-adic Smith form; my own mod-2 drain. Logs `logs/audit8_bpp.log`, `logs/audit8_bpp_v2.log` (VIGIA-FIN-OK, 52 MB, 0 s).
- dim 18, x₀-exact, rank_M̄ x₁ = rank_M̄ ȳ = 3 (**D0 true**); a² = 1 and **free over Z₂[a]** (9 floors with D + i even, 9 unit invariant factors of a + 1): a valid «kept» lattice.
- i = 1: X = {1³, 2², 3², 9, 12}, **X̄ = {1³, 3, 8, 11} ≠ 2X = {1², 2², 8, 11}**; i = 2, 3, 4 likewise. Identical to the flight's two code paths.
- **What it means:** on Borel lattices a clean drain does not force the law at level 2. Not a threat to the cube: these lattices are not built by the two moves (Φ, V⊗Φ). It tells where a proof must live: in the dance, which only tilting lattices have. My conjecture B″ (mission 8) is dead; I wrote it.

## 4. Leg A — is «rigidity» a proof or a measurement
**Verdict: it stays a MEASUREMENT.** The flight says so itself (Leg A «NO CONCLUYO»), and I agree after reading §2.2–§2.10 and §4.2–§4.4.
- **Route B (Δ/∇ mirror): STALLED, accepted.** Its argument is right in the part that matters: X and X̄ are exact on short exact sequences of free Z₂[a]-lattices and 2X is not; no highest-weight category carries the folded side. A reading, not a theorem; it closes nothing and does not need to.
- **PROVED reformulation (accepted): the dance is formal** — the output of flight 2's dance depends only on the coefficient tables of the operator and on the word of moves (digits of l + 1); the lattice never enters. Gate 270/270 against the numerical dance. This turns «the owner pays» into explicit recursions: statement (R_odd), implied by (R_gen) over the Tate algebra Z₂⟨q_d, ζ_m⟩. The implication (R_gen) ⟹ (R_odd) is a specialization q_d = 2^{α−2}(d + c)u(d) inside the unit disc: correct.
- **MEASURED, not proved:** entrywise rigidity of the final matrix at α ≥ 2 (752 + 752 entries; 162 fold entries; 1 992 entries at huge shifts up to 2^20 ± 1; symbolically over Z₂⟨q, ζ⟩ for l ≤ 6), its failure at α = 1 with ζ₂ odd (the control: 160/176 pivots stop being units), association of the even-family final matrices (54/54). Two of its sealed bets failed and were published (GC.1, GF.3/GF.5); they changed the strategy (rigidity entrywise for odd families, association for even ones).
- **The missing statement is ONE lemma in two halves, Lemma Ω (§4.2 of the report):** Ω-odd = (R_gen); Ω-even = «the two even-family final matrices are associates». With Ω, the assembly of §3.1 gives the fold law for every n. I checked the chain Ω ⟹ family law ⟹ fold law (E3, E4, H-odd, H-even, RT, RT̄, §3.1): the dependencies are the ones named, all already graded.
- **Where the hard part sits, in the flight's own words and mine:** (a) «weights leave no trace at the main payment degree» yields to degree counting (sketch, the multi-dancer paso not written); (b) the valuation bound does NOT yield to per-term bounds — there is an exact cancellation of the glue's F-terms at every doblar (valuation 3 + 3 → 8), and nobody has its closed form. The next target named by the flight: the closed form of the perturbed glue t ∈ 𝔅 with its doblar rule.

## 5. Theorem C₈ (n ≤ 144) — engines, pivot checks, independent re-check
- **Pivot check (sealed A8.3, held):** `fdance.step` computes the minimal valuation over the pivot block AND its formal inverse and returns failure if it is negative (pivot not invertible over Z₂); `run_dance` returns failure if a Schur complement is not ≡ 0 mod 2. Lower-triangularity of the pivot block is asserted. A non-unit pivot cannot pass silently.
- **The six `*_chk` logs (sealed A8.2, held):** all VIGIA-FIN-OK; 928 + 1 620 + 872 + 738 + 532 + 564 = **5 254 cells, 0 failures, 0 tray/pivot failures**. Their gate «dance = direct coker on T(λ)» (λ ≤ 20, i ≤ 6): 140/140.
- **My independent re-check (sealed A8.1, A8.5, held):** `engines_gh/gh_audit_vuelo8_S.py` = my flight-7 audit engine (flight 7's half-size H-odd/H-even formulas implemented from their printed statements, my own Smith form mod 2^192, my own rule code) whose ONLY change is a size filter by the closed formula dim T(l) = 2^{k+|I|} (checked equal to tilt_dp for l < 40). Note that it uses H-even, not the flight's Lemma E3: a different formula for the even families.
  | run | cells | failures | log |
  |---|---|---|---|
  | every n = 101..115, half-dim ≤ 128 | 586 | 0 | audit8_S_101_115_128.log (35 MB, 48 s) |
  | every n = 116..144, half-dim ≤ 128 | 1 163 | 0 | audit8_S_116_144_128.log (38 MB, 106 s) |
  | n = 104, 116, 128, 144, half-dim ≤ 512 | 51 + 56 + 58 + 65 (100 beyond the 128 runs) | 0 | audit8_S_{104,116,128,144}_512.log (≤ 374 MB, ≤ 206 s) |
  **Union: 1 849 of the 2 706 new cells (68.3 %), 0 failures.** At n = 144, 65 of the 72 families; the cells not re-checked are the largest ones.
  Two of my runs were killed by the watchdog and are not results: the first (memory, 1.27 GB, at n = 116: it built big lattices before filtering) and a stride run at 512 (time, 601 s; my estimate «~7 min» was wrong). Both are declared in BITACORA.
- **Reproducibility (the flight's own scripts, run in place with PYTHONDONTWRITEBYTECODE=1, logs in my folder):** `fd_run.py gate 10` and `fd_degree.py 2,2 3,3 4,4 5,5` reproduce their logs line for line. (The arguments of fd_degree were not in its diary.)
- **Grade of Theorem C₈:** n ≤ 100: proved, three independent codes (flight 7, the auditor, flight 8). n = 101..144: proved by the flight's checked computation, with an independent second computation on 68.3 % of the cells; the remaining 857 largest cells rest on one code.

## 6. Grades
| result | grade after this audit |
|---|---|
| Mod-2 layer of the fold law (number of cyclic factors), every family, every n — Lemma D-even + D-odd | **PROVED, two readings** |
| Lemmas E2, E3, E4 (even family = two odd arms glued by ½; doubled = folded × bend) | **PROVED, two readings** |
| The dance is formal (depends only on coefficient tables and the word) | **PROVED (reformulation), gated 270/270, accepted** |
| Theorem C₈: fold law for every n ≤ 144 | n ≤ 100 three codes; 101..144 one code + independent re-check of 68.3 % |
| B″ (D0 ⟹ fold law on Borel lattices) | **FALSE**, counterexample confirmed by two independent codes |
| Lemma Ω-odd = (R_gen); Lemma Ω-even (associates) | **MEASURED** (not proved) |
| The fold law for every n | **OPEN — reduced to Lemma Ω** |

## 7. What is left, in one statement
**Lemma Ω («the owner pays»).** In flight 2's dance, along ANY word of moves, (odd) the perturbed final matrix differs from the unperturbed one by at most 2 × (itself) × (integral), every pivot staying a unit; (even) the two final matrices of an even family are associates. Measured: l ≤ 12 numerically, l ≤ 6 symbolically, huge shifts; fails at α = 1 as it must. Missing: (a) the multi-dancer «paso» in the degree count; (b) the exact identity behind the measured cancellation of the glue's F-terms at every doblar (3 + 3 → 8) — the closed form of the perturbed glue t and its doblar rule.
**By Rafa's order (4 Oct, night): mission 9 is NOT prepared until his images are translated into ideas.**

## 8. Weaknesses of the flight and my own errors
- Flight: the command line of some exploration runs is not in its diary (fd_degree; I had to find the arguments); seals SB.4 half unmeasured (declared, E3); one control that could not fail (GE.4, declared E1); one sub-second run outside the watchdog (E2, re-run inside); times typed from memory in drafts (E5, caught and replaced); n = 101..144 on its code alone (it says so and asks for my re-check).
- Mine: two of my runs killed by the watchdog (one memory, one time) because my estimates were wrong; my first fd_degree rerun without arguments printed nothing (not a result). **B″ was my conjecture** and it is false.
- Not done: the pilot's folder is NOT moved into VOLADORES/ — the pilot's window is still open with its working directory there (lsof). Manifest at audit time: `reports/VOLADOR_8/ENTREGA_VUELO_8/MANIFEST_md5_at_audit.txt` (437 files); the audited REPORT, SEALED, DIARY and CLAUDE are copied there as the snapshot of what was audited.

## 9. Files with md5

```
5b6c55a7e1a6e204e9a3fae4b51ce17c  reports/VOLADOR_8/SEALED_AUDITOR_8.md
ec773c8754d825ad237f8c27f5161a57  engines_gh/gh_audit_vuelo8_S.py
646e04cc6762665ba52379de8a32e315  engines_gh/gh_audit_vuelo8_bpp.py
7cd6305ba93e656f979999b826968ce0  logs/audit8_S_101_115_128.log
1ee37b63b2cc4f1f7223d7d16107faf7  logs/audit8_S_116_144_128.log
a4ff1c4215a16c34564dbcbb45693f2d  logs/audit8_S_104_512.log
14a36c18e1d21ef9d77c89952a9c9a7a  logs/audit8_S_116_512.log
e7d183fccf150f4bd95d28b6b236abf2  logs/audit8_S_128_512.log
b56c66b484da5f8094179cea0f47a5c1  logs/audit8_S_144_512.log
617ade53527c0d59ff124a16373cf6e8  logs/audit8_bpp.log
0734c362625a90c637d9827b4eff4fd1  logs/audit8_bpp_v2.log
3bdc4124e89f746a07a2224746e50f95  logs/audit8_rerun_fd_gate_10.log
83c30963c662c92eebcc88ecbb341485  logs/audit8_rerun_fd_degree.log
41d31c11d0620ee12fac52e02d6211e7  logs/audit8_S_101_144_128.log
9f87f72a4643d595c227fd38215ebfc2  logs/audit8_S_104_124_4_512.log
97e834e091d660957f2cad2c25f970e1  logs/audit8_S_101_102_512.log
3543886926f645bfd1c2fd0d1f681cff  reports/VOLADOR_8/ENTREGA_VUELO_8/MANIFEST_md5_at_audit.txt
6e4591174e5e7ab404c6c82f187bfb03  reports/VOLADOR_8/ENTREGA_VUELO_8/REPORT.md
```
The two killed runs (audit8_S_101_144_128.log, audit8_S_104_124_4_512.log) are listed for the record only; they are not results.

## Addendum (2026-10-04 22:12:10) — folder moved
Rafa closed the pilot's window. `~/Desktop/GREPY_EL_VOLADOR_8/` was MOVED into `VOLADORES/GREPY_EL_VOLADOR_8/`; md5 of every file against `ENTREGA_VUELO_8/MANIFEST_md5_at_audit.txt`: 437/437 identical. The snapshot copies (REPORT, SEALED, DIARY, CLAUDE) became duplicates and went to `_BORRAR/ENTREGA_VUELO_8_snapshot_duplicados_2026-10-04/`; the manifest stays. Paths «~/Desktop/GREPY_EL_VOLADOR_8/…» in this audit now live under `VOLADORES/GREPY_EL_VOLADOR_8/`.
