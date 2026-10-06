# Audit — Flight 4 («Grepy el volador 4»: mission 4 «the rent and the gold» + mission 4b «the rule that rules everything»), Grepy Hypercube, 3 Oct 2026

Copied with md5 into `reports/VOLADOR_4/ENTREGA_VUELO_4/` (manifest there): REPORT.md b30606af5196f82df14dc8d7288e98c2 · MISSION.md 60f3f128… · SEALED.md 505fee47… · DIARY.md cac7b398… · legE_proof.py 03c118a9… · sources_4b/ (8 files).

## 1. Verdict in one line

**CLOSED.** Theorem F (REPORT §11.2.6) proves the floor T(r) ≥ Y(r) in every cell of every family, every α ≥ 1, every shift i ≥ 0. With Theorem O (flight 3) and the tropical bound, this gives d_r = Y(r), i.e. Conjecture W, for every cell. With Theorem D (flight 2, with flight 3's RT′) it gives **the whole Sylow 2-subgroup of the sandpile group of Q_n, for every n, as an explicit closed rule.**

**Grade:** PROVED by pencil. Every link is read by its author and by this auditor. The proof of Theorem F is gated by my own code, and its controls fire. No external cold reading yet.

**Not closed:** the three trophies for general n. They are Gao et al. Conj. 4.14 and 5.4 and the JMM poster's (n+1)-th factor. They are now pure arithmetic on the closed rule; flight 3 evaluated them only for n ≤ 261.

## 2. Pencil reading (my own words; CORRECT / GAP / ERROR)

- **11.2.1, window gates — CORRECT.**
  - Re-derived bit by bit: digit d, incoming carry c, m of type 1 or 0 on [t, next(t)).
  - Carries inside the window: κ_t·[type 1 ∧ (d ∨ c)] + κ_t·[type 0 ∧ d ∧ c].
  - The carry leaves the window iff the window is saturated and the gate fires.
  - Hence R(D) = τ(D) − Σ_t κ_t c_t(D)·[type 1 ∧ t ∉ D, or type 0 ∧ t ∈ D].
- **11.2.2, top-digit recursion — CORRECT.**
  - Removing the top digit c leaves the windows below c unchanged; the top window of H′ is [max I′, c), as in H.
  - The four formulas for R and J follow from 11.2.1 with c_in = J′(D₀).
  - γ_I = γ_{I′} + h_c on arrows that do not move c, and γ_I = γ_{I′} on arrows that do.
- **Theorem U (A.5) — CORRECT.**
  - The cost of a matching is ≥ Σ_A w_r − Σ_B w_c, by (i′).
  - That is ≥ the sum of the r smallest w_r minus the sum of the r largest w_c.
  - By monotonicity, this is Σ_{L_r} (x + φ − φ′∘mir), which is ≥ Y(r) by (iii′).
  - The mirror reverses the o-order, so L_r is paired with F_r.
- **Theorem F, steps 1–8 — CORRECT, every inequality re-derived.**
  - **Step 1 (walk):** antitonic least squares is invariant under adding a non-increasing function that is constant on its blocks. The KKT block conditions are preserved, and Cut_{j−1} puts the steps of d₁ on block boundaries.
  - **Gluing:** a single central block of sum 0, symmetric under the mirror.
  - **Step 2:** max d₁ ≤ α2^c, because κ ≤ h. Hence Λ_j holds.
  - **Step 3:** the three cases of the Cut lemma.
    - T = 1 saturated: τ = −α2^c, so X1 ≥ α > 0 just before b.
    - T = 0 saturated: X2(b′) ≤ −α < 0.
    - In both cases the boundary survives the central block.
  - **Step 4:** v′ = R_j + φ(·∖c).
    - (E) is an identity, using J′(∅) = 0.
    - Same-half arrows gain h in γ.
  - **Step 5:** v′({c}) − v′(I′) = −X1(I′) ≤ h − α, by Λ_{j−1}.
  - **Step 7:** the plumber's interval is non-empty. The four inequalities are:
    - c3 ≤ c4, since c3 − c4 = X1(f) ≤ 0;
    - c3 ≤ v′(p);
    - v′(p*) ≤ c4;
    - v′(p*) ≤ v′(p), since the difference is X1(p) > 0.
  - **Step 8:** all six arrow cases with an end in F checked. An arrow into F from after F, or out of F to before F, is impossible, because e ⊊ a implies that e precedes a.
- **Base cell → real cells — CORRECT.**
  - **i ≥ 1:** v = V − P_rJ and w = V − P_cJ. The pooled clocks are the base pooled clocks shifted by −P_rJ + P_cJ∘mir. The shift is non-increasing and constant on blocks (Cut_n).
  - **i = 0:** the house m_low = 2^k − 1 with row ∅ deleted. The natural column sets F_r never contain the column I.
- **Integer splitting — CORRECT.** No two adjacent blocks have equal non-integer means. The child gaps only grow under a non-increasing shift; the central block is 0; its neighbours have means of strict sign.
- **One external input used by the chain and not new here:** PAVA's characterization of the antitonic fit (Ayer–Brunk–Ewing–Reid–Silverman 1955; standard).

## 3. Independent gates (own code; none of flight 4's code) — MEASURED, 0 failures

`engines_gh/gh_audit_vuelo4.py`, `engines_gh/gh_audit_vuelo4_ctrl.py`. Every run passed the watchdog (VIGIA-FIN-OK), with a peak of at most 32 MB.

- **G1 — cost form against Theorem D.**
  - I took the 2-adic valuations of MY exact Theorem-D matrices M(λ, i) (flight-2 audit engine) and compared them with R_m(a) − R_{m+K}(b) + γ(a∖b). Rulers come from plain integer carries with the full m; at i = 0 I used the house 2^k − 1.
  - Result: the two agree up to ONE constant per cell, in every cell. That is 4104/4104 cells: λ < 64, α = 1..3, 24 shifts including i = 0.
  - Row ∅ is identically zero at i = 0.
  - Controls fire: without γ, 424/620 cells fail; with rows and columns read at the same m, 310/620 fail.
  - Log: `logs/gh_audit_vuelo4_G1.log`, `logs/gh_audit_vuelo4_G1ctrl.log`.
- **G3 — my implementation of the induction of 11.2.6.**
  - Rulers and carry-out sets come from integer carries, not from flight 4's formulas.
  - At every level I checked (W), the final segment F₁, c3 ≤ c4, the non-empty window, (E_j), (M_j), (G_j), Cut_j and Λ_j.
  - I tried three prices of the window (lo, hi, mid).
  - Then I checked Theorem U (i′)(ii′)(iii′) in REAL cells: rulers at m and m + K with the full m; shifts 0..2K+1 plus 7 large shifts (long carry runs, both jump cases).
  - Result: **0 failures**.
    - k ≤ 5: 23 436 builds, 55 080 real cells, α = 1..6.
    - k = 6: 72 576 builds, 154 224 real cells, α = 1..6.
    - k = 7: 146 304 builds, 301 752 real cells, α = 1..6 (§5b).
  - That is every family λ ≤ 254 with |I| ≥ 1.
  - Control: the same potentials with the gold removed break (i′) in 21 796 cells (k ≤ 5).
- **Earlier (flight-3 audit, still valid):** Smith(M) equals the pooled rule, exactly, in 11 592 + 2 268 + 455 cells; Theorem O in 3 712 cells.

## 4. The chain for the whole 2-part, with readers

| link | author | readers | gate |
|---|---|---|---|
| Fusion recursion m_λ(n) | flight 1 | flight 2, auditor | yes |
| Theorem RT′ (tilting families over Z_2, no citations) | flight 3 | auditor | Theorem D 15/15 |
| Theorem D (2-part = small clocks ⊕ Smith(M(λ, i))) | flight 2 | flight 3, auditor | 15/15 whole groups n ≤ 16 |
| Cost form C.4 / A.4 / 11.2.1–2 | flights 3, 4 | auditor | G1 4104/4104 |
| Theorem O (d_r ≤ Y) | flight 3 | auditor | 3712 + 1920 |
| Theorem U, Theorem F (T ≥ Y) | flight 4 | auditor | G3, 0 failures |
| d_r ≥ T (tropical) | standard | — | — |

**The theorem.** For every n ≥ 1:

Syl₂ K(Q_n) ⊕ Z₂ ≅ ⊕_λ [ ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ Smith₂ M(λ, (n−λ)/2) ]^{m_λ(n)}

where:
- the exponents of Smith₂ M are the pooled clocks: integer PAVA of x_D = R_m(D) − R_{m+K}(I∖D);
- R_μ(D) = Σ_{t∈D} (h_t − α2^t) − #carries(μ + o_D);
- for the cube, α = 1;
- this is flight 1's rule D.5.

## 5. State of the art (web sweep today, originals read where available)

- **Chandler–Sin–Xiang (arXiv:1511.00272, original read, local copy).** «Only the 2-Sylow subgroup of the critical group remains to be determined… **We do not have any conjecture about its exact structure.**»
- **Gao–Marx-Kuo–McDonald–Yuen** (arXiv:1912.06919 v3, 17 Apr 2024; Comm. Algebra 2024; original read). They give the n − 1 largest factors exactly. Their words: «determining the complete structure still seems out of reach at this moment». Their method (representation ring, 2-adic valuations through carries) is a forerunner of ours and must be credited.
- **Bai 2003** (Linear Algebra Appl. 369). He settles the odd primes, the number of 2-cyclic factors (2^{n−1} − 1) and the number of Z/2 factors, which are Reiner's two conjectures. The full 2-part is left open. Anzis–Prasad 2016 and Reiner's REU 2016 «Problem 1: describe Syl₂ K(C_n)» also say it is open.
- **Searches** for 2025–2026 papers on the 2-part of K(Q_n) found nothing. arXiv:2609.10625 is about the square grid. arXiv:2512.24317 and 2405.16015 are pure SL₂ representation theory.
- **Not read:** the JMU 2022 undergraduate project (host down today, as for the constructor).
- **To credit in a paper:**
  - the tilting decomposition of V^{⊗n} for SL₂ in characteristic 2 (Doty–Henke math/0205186, Donkin, Erdmann, and later work) — our fusion recursion must be compared with it;
  - Bier 1993 (Theorem Z);
  - Reiner–Tseng (the fold-law exact sequence);
  - Kummer (carries);
  - PAVA.

**Answer to «Reiner's mystery»:**
- Reiner's two FORMAL conjectures were proved by Bai in 2003, not by us.
- The mystery he named — Problem 1 of the 2016 REU, the whole Syl₂ K(Q_n) — is open in every source we found. **This project answers it**, subject to external review.

## 5b. G3 k = 7, α = 4..6
PASS, 0 failures: 146 304 builds, 301 752 real cells (logs/gh_audit_vuelo4_G3_k7b.log, VIGIA-FIN-OK, 31 MB, 292 s). So G3 covers every family λ ≤ 254 with |I| ≥ 1 and α = 1..6. (The control line «0» in the k ≥ 6 logs is by construction: the control loop runs only for k ≤ 5.)

> **NOTE 2026-10-04 20:50 (Grepy Bross, after the first external cold reading, `reports/LECTOR_FRIO_1/CALIFICACION_LECTOR_FRIO_1_v1.md`).** The statement printed in §4 above is **wrong as written by a constant**: Theorem D has `2^k · coker M`, and with α = 1 the big-clock exponents are **e_D = k + 2^k + κ(i−1, 2^k) + ŷ_D** (ŷ = the integer antitonic fit of x_D in o-order), not ŷ_D; the cell i = 0 needs its own convention (e_∅ = ∞, the other clocks = flight 1's naive clocks u(D) pooled the same way = the house m_low = 2^k − 1 with the row ∅ deleted); and the integer splitting (a pool of p values with sum S becomes S mod p values ⌈S/p⌉, then ⌊S/p⌋) is part of the statement. Example: λ = 6, i = 1: x = (1, 1, −1, −1), constant 6, X(6, 1) = {1:4, 5:2, 7:2}. The theorem is unaffected; the line above is kept as written (append-only). Also, «Integer splitting — CORRECT» in §2 is too narrow: what the proof needs is ⌊μ_A⌋ ≥ ⌈μ_B⌉ for adjacent PAVA blocks (true in every cell, by the same induction; reader's P-INT and C4). And the credit for m_λ(n) moves from Doty–Henke to Donkin's characters and Larsen 2024 §2 (Larsen not yet read in the original).
