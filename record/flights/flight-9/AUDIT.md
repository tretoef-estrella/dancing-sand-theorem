# Audit of flight 9 — «the oil, the cave and the pair of hinges» (Lemma Ω) — Grepy Bross, 5 Oct 2026
Report audited: `~/Desktop/GREPY_EL_VOLADOR_9/REPORT.md` (copy `REPORT_FLIGHT_9_as_delivered.md`, md5 in BITACORA). Seals written before any run: `SEALED_AUDITOR_9.md` (md5 7f818086…).

## Verdict
**HOLDS. No FATAL item, no GAP, no ERROR in the mathematics.** Lemma Ω is proved, odd and even, for the operators the law uses. With flight 8's audited assembly this proves **the Dry and Wet law (the fold law) for every n**:
Syl₂ K(Q_n) ≅ (Z/2)^(a_n) ⊕ [Syl₂ K̄(n), every exponent + 1], a_n = 2^(n−2) − 2^⌊(n−2)/2⌋.
Grade: **PROVED by pencil, two readings** (the pilot's, and mine below, line by line), with gates by the pilot and independent gates by the auditor. **No external cold reading yet: it is owed before any paper or announcement.** Mark: **HIGHEST.**

## The reading, item by item (all CORRECT)
- **Lemma IB (inverse block).** A chain of Schur complements is one Schur complement, and its inverse is a block of A⁻¹: this is the standard block-inverse identity. ρ and κ depend only on the word. CORRECT.
- **Corollary** (each entry of M_w(A)⁻¹ is a constant γ_ij times one coefficient y_M(f)): follows from floor homogeneity. Gated by the pilot 2862/2862, with a control that fires 1564/2862.
- **Lemma PS.** A⁻¹ = Σ(−1)^s(Δ⁻¹N)^sΔ⁻¹, a sum over compositions. Relative to the all-ones path, a composition costs the payments of the skipped floors divided by Π m_i!. Its valuation is ≥ (α−1)Σ(m_i−1), by v(m!) ≤ m−1. CORRECT (floor-dependent integral ζ allowed).
- **Lemma H.** (B∘(1+E))⁻¹ = Σ(−1)^n[𝒜(B∘E)]^n𝒜. By the strict superadditivity of δ, v((𝒜⁻¹)_DD′) ≥ δ(D∖D′), and the n-th term is ≥ δ(D∖D′) + n. Diagonal scalings commute with ∘. CORRECT.
- **Theorem R.** IB + PS + H, then Theorems O and F (flights 3–4), which see only support and valuations. CORRECT.
- **The class 𝒦 (K1, K2).**
  - K1 (re-expansion under shifts, inverse of odd elements): re-derived.
  - K2: Θ is a ring map, since (a+2χ)(b+2ω) = ab + 2(aω+bχ) + 4χω; it is shift-invariant, since χ(X−2e) ≡ χ(X) coefficientwise mod 2; and ker Θ = 2𝒦.
  - Strassmann uniqueness applies, because the coefficients a, 4c₁, 8c₂, … tend to 0.
  - CORRECT.
- **T1, T2.** The position of (D₁, f−a) is y − a·2^h − r_{D∖D₁}, by additivity of r. The image ring is commutative of characteristic 2, and every element without constant term squares to 0, since C(2q,q) is even and E_t² = 0. CORRECT.
  - **Remark of the auditor:** the constant term of β, ε·χ̄, also squares to 0 (ε² = 0). So in fact β² = 0 whole, which is stronger than «only the constant term survives».
- **Theorem C, doblar.** The slot formulas printed match flight 8's `fdance.doblar_elem` exactly: x00 and x11 over (2q−1)!!, x10 over (2q+1)!!, x01 with the even factor 2q+2.
  - The positions match: B = x00 at y′, C = x11 at y′+2^h, P = x10 at y′+2^h, Dd = x01 at y′.
  - Θ(Dd) = 0, Θ(B) = Θ(C), β² = 0 ⟹ S ∈ 2𝒦.
  - (a): the new payment is −B₀P₀⁻¹C₀/2 ≡ 0 mod 8, because Dd has no degree-0 term.
  - (b): S_{∅,1} = 2Γ_{∅,1}(y′) + (terms containing B₀ or C₀, ≡ 0 mod 4), so the new F-coefficient is odd.
  - CORRECT.
- **Theorem C, paso = V-split + doblar.** Checked against `fdance.paso_elem`:
  - the output floor is 2f+σ+v, so the shift v·2^h equals r_{D∪{h}} − r_D;
  - the remaining row C = row10 + row01 and the remaining column B = col01 − col10 each differ by a pivot row or pivot column, so the Schur complement is unchanged.
  - CORRECT.
- **Ω-odd (const) and c = 0.**
  - c ≥ 1: Theorems C and R.
  - c = 0: limit along c = 2^n. Entries of a clean dance are continuous in c (unit pivots for every c ∈ Z₂). An entry of M_Σ(0) that vanishes forces the matching entry of M_A(0) to vanish. Theorems O and F hold at i = 0 (flights 3–4 treat i = 0: row ∅ absent).
  - The real weights: tanh as is; coth after ÷3 and conjugation by 3^{−D}.
  - CORRECT.
- **Claim A.**
  - 𝔞 mod 4 is shift-invariant, since 𝔞(φ(·−e)) = a + 2χ(−2e) and χ(−2e) is even.
  - Perturbing by 2δ changes 𝔞(S) only by multiples of 4, using commutativity and β² ≡ 0 mod 2 (the payment is ≡ 0 mod 4, so its 𝔞 is ≡ 0 mod 4).
  - CORRECT.
- **Lemma U.** glue = L⁻¹diag L with a constant L acting on the dancer index; integrality ⟺ G_h(X) ≡ G_h(Y) mod 2. CORRECT.
- **Even arms are clean.** Ψ_i ≡ Ψ_{i+1} mod 2 (difference 2(1+εSh⁻¹)). Ψ² ∈ 2𝒯 because Θ(Ψ)² = 0. The payments of Ψ(Ψ±2)/2 are 4y(2y±1) and their F-coefficients are odd. CORRECT.
- **Lemma B (the window bound).**
  - Each path of Ψ±2 against Σ's main path has valuation ≥ W[window], with w(d) = 1 + v(d+c) ≥ 1.
  - v(X_D) − v(X_{D″}) = −W[o_{D″}, o_D − 1], so the total is δ + δ + W[o_D, o_{D′}+2^k−1] ≥ 1. The window is non-empty because o_{D∖D′} ≤ 2^k − 1.
  - CORRECT.
- **Partial fractions and Ω-even.**
  - The partial fractions 2/(Ψ(Ψ±2)) = ±(Ψ⁻¹ − (Ψ±2)⁻¹) are linear in A⁻¹, so the same ρ and κ apply.
  - glue(a,b)·glue(c,d) = glue(ac, bd): checked by hand.
  - glue(W₋,W₊) is integral, since W₊ ≡ I ≡ W₋ mod 2, and it lies in GL(Z₂).
  - CORRECT.
- **Assembly (§5.1).** Flight 8 §3.1 (two readings) + H-odd, P-R1, A0 (flight 7, audited) + Ω-odd, Ω-even. CORRECT.

## The auditor's gates (own operators, own Smith forms, own determinant; flight 8's fdance only performs the moves, md5-identical)
| seal | what | result |
|---|---|---|
| SA1 | Theorem C as stated, with genuinely floor-dependent 𝒦 functions on EVERY coefficient (F-coefficient, payment, ζ₂…ζ₈), l ≤ 63, c = 0..3, 4 seeds. The pilot never ran this: its gates used constant weights. | **HELD: 1008/1008 clean** (161 s, 15 MB) |
| SA2 | control: random odd units on F | first version DID NOT FIRE (378/378 clean). **My error:** with ζ = 0 an odd unit on F is conjugated to 1 by a floor unit, so that control cannot fail. Corrected (odd units on F + constant ζ_m): **FIRED, 49/378, first at l = 31**, as the pilot found |
| SA3 | control: α = 1, ζ₂ odd | **FIRED, 183/189** |
| SA4 | Theorem R with floor-dependent 𝒦 weights, own Smith form | **HELD: 378/378** (l ≤ 63): equal entrywise valuations and equal Smith forms |
| SA5 | Ω-even: M(circ(fh))·M(circ(f))⁻¹ integral with unit determinant (i ≥ 1), Smith forms equal (i ≥ 0) | **HELD: 100/100 (l ≤ 20, i ≤ 4) and 144/144 (l ≤ 36, i ≤ 3)** |
| re-run | the pilot's own Ω1 gate, from a copy outside its folder | **identical: 120/120** |
Logs: `logs/audit9_*.log`, all VIGIA-FIN-OK, peak ≤ 20 MB.

## Did the images serve? (the auditor's reading, not the pilot's)
- **YES, two of them, and decisively:**
  - **«Las bisagras van en pareja» + «los bugs son hallazgos».** They made the auditor see that the random weights were the bug and retarget mission 9 to the real weights (Ω-real). Flight 9 then proved that the general statement (flight 8's R_gen) is FALSE. Without that redirect the flight would have chased a false lemma. And the pair is literally the mechanism of Ω-even: the two arms agree mod 2 (Claim A), which is what makes the glued dance clean (Lemma U).
  - **The cave / Shawshank («cuanto más bajas, todo a la mitad»).** It told the pilot what to measure: how the noise varies from level to level. The measured h+2 and 2 led to the class 𝒦 of functions of TWICE the position, the heart of Theorem C.
- **Partly:** the oiled hinge. The oil itself (row and column operations) was not needed; what remained of the image is the U-bar: the hinge is the same at every level (Lemma U).
- **Not used:** the turned lid (4 Oct night). It stays as a measured law to test against this machinery.

## Owed
1. An external cold reading of the proof (flight 9 + the chain of flights 1–8), before any paper or announcement.
2. The paper of the cube (Dancing Sand Theorem + the fold law), with the credits; novelty sweep for Theorem C and the class 𝒦.
3. The turned lid: does this machinery prove the swap symmetry?
4. Not proved here (the pilot says so): the oil route's own statements; the identity of the oil defects of the two hinges.

— Grepy Bross
