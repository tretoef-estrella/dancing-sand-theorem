# Audit, first pass — Flight 2 («Grepy el volador 2», «the two moves»), Grepy Hypercube, 3 Oct 2026

Copied with md5 into `reports/VOLADOR_2/ENTREGA_VUELO_2/`: REPORT.md 57ce9da71ede23b5d29af50014475bde · checks/SEALED.md 34aa254b5b70cbc4350440f33cce8ddd · logs/DIARY.md a216fb866cf113071b3ec2edea921806.

## 1. Verdict in one line
**Not closed. Large advance:** the whole 2-part of K(Q_n) is now, for every n, the Smith form of explicit 2^{|I|}×2^{|I|} integer matrices M(λ, i) with closed-form entries (Theorem D, proved by one hand modulo cited tilting theory). The only open step is (C-b): Smith(M) = the pooled clocks of the rule when |I| ≥ 2. Smallest open cell: n = 6, λ = 6, i = 0.

## 2. Independent check of Theorem D AS PRINTED (own code) — MEASURED 15/15
`engines_gh/gh_audit_vuelo2.py` (my tilting multiplicities by character peeling from Donkin's product formula; my q_k recursion; my exact 2-adic Smith form over Q), logs `logs/gh_audit_vuelo2.log`, `logs/gh_audit_vuelo2b.log` (VIGIA-FIN-OK, < 6 MB, 0 s):
- whole 2-part n = 2..13: 12/12 exact, one Z each (against my gh_gates and the Chaise's cubo_mitad);
- layers Z/2, Z/4, order ≥ 8 at n = 14, 15, 16: 3/3 (against my aire.py);
- deficit law v_2(a_k(Δ)) = k − |Δ| − min Δ: 966/966 cells, λ < 128;
- control: changing the split term by a factor 2 breaks 11 of 12 cells. **My first control (factor −3) could not fire — a unit does not change valuations, and Smith(M) depends only on valuations; replaced. Error of the auditor, published.**

## 3. Proofs read on this pass
- Leg 0 (second reading of flight 1): sound; the gap it found in RT (tilting over Z_2, not only F_2) is real and its repair (Δ_Z-filtration of Δ_Z(m)⊗V by primitive vectors; self-duality) is correct on my reading. ⟹ Theorems Z, B, S, E, λ = 2 now have TWO readings.
- A.1, the functor Φ: sl_2 relation on b0 n checked by hand (EF − FE = Ω − H² − 4FE = 2H+1 = 2m+1); the mod-2 reduction (Ω ≡ (H+1)² mod 4) correct. Identification Φ(T(l)) ≅ T(2l+1) rests on the same cited facts as RT.
- A.2, P-R1: elimination re-derived: Z n = 2Fn − 2^{2α}(j+2f)(j+2f+1)n, and (j+2f)(j+2f+1)/2 = (⌈j/2⌉+f)·odd. CORRECT.
- B.1 even step, C.1 (|I| = 1), C.4 coefficient algebra and deficit law: read, correct on this pass.
- Grade: PROVED by one hand + auditor's positive first pass: Φ, P-R1, B.1, C.0, C.1, C.4, Theorem D, P-X1 (small clocks). Second reading owed (flight 3, Leg 0).
- OPEN: (C-b). Measured everywhere (4352/4352, tropical 882/882, natural minors unique 2632/2632).

## 4. Where (C-b) stands, in the auditor's words
d_r = r-th determinantal divisor of M. Smith partial sums are convex. If (i) every natural minor has a unique minimal-valuation term (no cancellation) then d_r ≤ U(r) (unpooled rule), hence d_r ≤ Y(r) = greatest convex minorant of U = pooled rule. If (ii) every r×r minor has valuation ≥ Y(r) — which follows from the TROPICAL statement «every r-matching in the support costs ≥ Y(r)» because a sum's valuation is at least the minimum of its terms' — then d_r = Y(r). Both (i) and (ii) are assignment problems on the explicit weights v(M_{DD'}) = ρ_D + κ_{D'} + δ(D∖D'), δ(Δ) = k − |Δ| − min Δ, with the 2-adic ruler w(d) = α − 1 + v_2(i+d). The pilot showed (C.6) the statement is false for non-realisable weights, so the ruler must be used.
