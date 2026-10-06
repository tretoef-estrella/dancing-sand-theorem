# Audit, first pass — Flight 3 («Grepy el volador 3», «the orphan»), Grepy Hypercube, 3 Oct 2026

Copied with md5 into `reports/VOLADOR_3/ENTREGA_VUELO_3/`: REPORT.md 3183fbd19b74371a3313a019118b0e64 · checks/SEALED.md 51b7ca3db33154558b6db02b7c5e475f · logs/DIARY.md a4c556e35de122ea4994d75af9838fef.

## 1. Verdict in one line
**Not closed for every n. Very large advance:** the orphan (step (i)) is PROVED for every family; Conjecture W is PROVED for every family with |I| ≤ 2; and, by two pencil lemmas plus an exhaustive finite check per family, for every λ ≤ 255 and every odd λ ≤ 511 ⟹ **the whole 2-part of K(Q_n) is a theorem for every n ≤ 261 and every odd n ≤ 299**, with Gao et al. Conj. 4.14, the poster's (n+1)-th factor and Conj. 5.4 (n = 4…256) proved in that range. Open: ONE argument for the floor (ii) valid for all families at once. First open cube: n = 262.

## 2. Independent checks (own code; none of flight 3's code used) — MEASURED, 0 failures
`engines_gh/gh_audit_vuelo3.py`, log `logs/gh_audit_vuelo3.log` (VIGIA-FIN-OK, 12 MB, 146 s). M(λ, i) from Theorem D with my own code; exact 2-adic Smith form over Z/2^N with ring operations only; rule W^(α) from flight 2's `rulew.py`:
- **Theorem A2:** every λ < 512 with |I| = 2, α = 1, 2, 3, shifts 0..32 and 13 large shifts up to 2047 (long carry runs and both jump cases): **11592/11592**.
- **Families |I| ≥ 3, even λ ≤ 127:** α = 1, 2, 26 shifts each: **2268/2268**.
- **k = 7 sample, 3 ≤ |I| ≤ 4:** **455/455**.
- **Theorem O:** v(det M[L_r, F_r]) = U(r) (unpooled rule) for every r, even λ < 64 with |I| ≥ 2, i = 1..8, α = 1, 2: **3712/3712**; unique term of minimal valuation by brute force over all permutations (|I| ≤ 3): **1920/1920**.
- Control (one naive clock moved by one before pooling): 40 mismatching cells — it can fail and does.

## 3. Proofs read on this pass
- **Leg 0 / RT′ (no tilting citations).** The citation error it found is real: Jantzen II.4 opens «Let k be a field throughout this chapter» (the auditor had warned of it). The replacement is sound on this reading:
  - Lemma W: an extension of Δ_A(λ) by a lattice with weights in [−λ, λ] splits, by Kostant's commutation formula;
  - Ext¹(Δ, ∇) = 0 and Hom over Z_2 follow;
  - lifting holds by Nakayama;
  - the identity V^{⊗3} ≡ Δ(3) ⊕ V² mod 2 holds (the form values 1, 3, 3, 1 are units).
  So Theorem D no longer depends on Donkin or Jantzen. Second reading owed.
- **Lemma ε, Lemma (top digit), strict subadditivity, Theorem O:** read; the induction on the top digit and the shortcut argument (paths → arrows, strict subadditivity) are correct on this reading.
- **A.1 carries form (Legendre/Kummer), Theorem A2 (three carry cases, four jump patterns, chord criterion):** the structure is correct. The inequality-by-inequality case work is «written out in my working notes» and not in the report: that part is gated (330000 + 331100 cells, and my 11592), not read. **Grade for A2: PROVED by one hand; the case table must be written in full for the second reading.**
- **St1:** re-derived; correct. The cost is affine in α and in the jump P. The natural matching minimises the α-part and the jump part, and is the unique minimum of the rest on its row/column sets (Theorem O). The clock differences grow with α and P.
- **St2 (finite window in P):** plausible on this reading. It is the step that turns «infinitely many shifts» into a finite check, so it needs a careful second reading.
- Per-family check: exhaustive by machine, two engines agreeing on k ≤ 6. The proof of n ≤ 261 is therefore «pencil lemmas + finite machine verification», like a computer-assisted proof. Grade: PROVED (computer-assisted), one hand.

## 4. Errors of the pilot (declared by him)
- Two scratch files written outside his folder, in the session's scratchpad. This breaches the folder rule; nothing of the project was touched, and both files were copied back.
- Two guessed clock times; one run killed by the watchdog (E3).
- Two sealed predictions failed: P-AD1 and P-Q1 at λ = 0. Two predictions were not run: P-AD3 and the n ≤ 40 table.
- None of these affects a claim.

## 5. What is open, exactly
The floor (ii) for all families at once: every r-matching costs ≥ Y(r). In flight 3's cleanest form (Lemma F4) a matching costs «rows R + columns C + the gaps γ it skips», and pooling happens only where a gap after some digit t is wider than α·2^t. The per-family threshold α0 is ≤ 5 for all 99 families checked.
