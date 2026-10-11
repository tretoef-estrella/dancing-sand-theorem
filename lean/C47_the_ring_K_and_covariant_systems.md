# The ring 𝒦 and the covariant systems (Lemmas 10.13 and 10.14, paper v8 §10.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.5, Lemma 10.13 (the ring `𝒦`, the homomorphism `Θ: 𝒦 → 𝒮`) and Lemma 10.14 (the ring `𝒯_h` of covariant systems, the homomorphism `Θ_h: 𝒯_h → R_𝒮`, and `β² = β_0²` in `R_𝒮`). These are the tools of Theorem 10.15 (cleanliness), which is piece C48.

**One change of presentation, and why.** The paper's `𝒦` is the set of functions `ϑ(y) = a + 2χ(2y)` with `χ ∈ X·ℤ_2[[X]]`; uniqueness of `(a, χ)` uses Strassmann's theorem, and the shifts need rearrangements of 2-adic series. This piece uses the **rational subclass** `𝒦_r`: `χ = p/q` with polynomials `p, q ∈ ℤ_2[X]`, `p(0) = 0`, `q(0)` a unit. It is a subring of `𝒦` that contains the constants and `2^α y` (`α ≥ 2`). It is closed under shifts and under inverses of the elements with a unit constant `a`. Everything is finite polynomial algebra, and uniqueness follows because a polynomial with infinitely many roots is zero. The proof of Theorem 10.15 uses only these properties, so it holds verbatim with `𝒦_r` in place of `𝒦` (piece C48).

Folder `RequestProject/RingK/`, namespace `RingK`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps.Bf` (`x.coef m f`), its product `(x * y).coef m f = Σ_{a ≤ m} C(m, a) x.coef a f · y.coef (m − a) (f − a)` (`Bf.coef_mul`), its ring structure; Mathlib's `Polynomial`, `PowerSeries`, `TrivSqZeroExt`, `PadicInt`, `PadicInt.toZMod`, `Ring.inverse`.

Throughout, `A := ℤ_[2]` and `red := PadicInt.toZMod : ℤ_[2] →+* ZMod 2`.

## Definitions (new)

1. `KRep`: a structure with fields `a : ℤ_[2]`, `p q : Polynomial ℤ_[2]`, `hp : p.coeff 0 = 0`, `hq : IsUnit (q.coeff 0)`.
2. `KRep.eval (r : KRep) (y : ℤ_[2]) : ℤ_[2] := r.a + 2 * r.p.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))`.
3. `Kr : Set (ℤ_[2] → ℤ_[2]) := Set.range KRep.eval` (the class `𝒦_r`).
4. `S := TrivSqZeroExt (ZMod 2) (PowerSeries (ZMod 2))` (the ring `𝒮`: `ε² = 0`, characteristic 2).
5. `thetaRep (r : KRep) : S := TrivSqZeroExt.inl (red r.a) + TrivSqZeroExt.inr ((r.p.map red : PowerSeries (ZMod 2)) * ((r.q.map red : PowerSeries (ZMod 2)))⁻¹)` (the inverse of a power series over the field `ZMod 2`).
6. `theta (ϑ : ℤ_[2] → ℤ_[2]) : S := if h : ϑ ∈ Kr then thetaRep (Classical.choose h) else 0`.
7. `RS := Finset ℕ → ℕ → S` with addition pointwise, unit `one Δ q = if Δ = ∅ ∧ q = 0 then 1 else 0`, and product
  `(β * γ) Δ q = Σ_{Δ₁ ∈ Δ.powerset} Σ_{a ∈ range (q + 1)} (C(q, a) : S) · β Δ₁ a · γ (Δ \ Δ₁) (q − a)`
  (the ring `R_𝒮 = 𝒮[F^{(m)}][E_t]/(E_t²)`: `Δ` is the monomial `E^Δ`, `q` the divided power `F^{(q)}`).
8. `oS (D : Finset ℕ) : ℕ := Σ_{t ∈ D} 2^t` (the offset `o_D`).
9. For `P : Finset ℕ`, the index type `Dn P := {D : Finset ℕ // D ⊆ P}` (a `Fintype`), and for `h : ℕ`, `c : ℤ_[2]` and `Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]` the **covariant system**
  `covSys P h c Γ : Matrix (Dn P) (Dn P) (Bf ℤ_[2])`, `(covSys P h c Γ D D').coef m f = if D'.1 ⊆ D.1 then Γ (D.1 \ D'.1) m ((2 : ℤ_[2]) ^ h * f + oS D.1 + c) else 0`.
10. `thetaSys (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : RS := fun Δ m => theta (Γ Δ m)`.
11. `prodFun h Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]`,
  `prodFun h Γ Γ' Δ m y = Σ_{Δ₁ ∈ Δ.powerset} Σ_{a ∈ range (m + 1)} C(m, a) · Γ Δ₁ a y · Γ' (Δ \ Δ₁) (m − a) (y − a · 2^h − oS Δ₁)`.

## Part K — the class 𝒦_r (Lemma 10.13 (a), (c))

- **(K1)** For every `r : KRep` and `y`, `IsUnit (r.q.eval (2 * y))`, so `Ring.inverse (r.q.eval (2 * y)) * r.q.eval (2 * y) = 1`.
- **(K2) Uniqueness.** If `r.eval = r'.eval` then `r.a = r'.a` and `r.p * r'.q = r'.p * r.q`.
- **(K3) Ring.** The constant functions are in `Kr`; `Kr` is closed under `+`, `−`, `*` and under multiplication by any constant of `ℤ_[2]`. (Formulas: `(a, p, q) + (b, p', q') = (a + b, p q' + p' q, q q')`; `(a, p, q)(b, p', q') = (ab, a p' q + b p q' + 2 p p', q q')`.) The identity function `y ↦ y` is not needed; but `y ↦ 2^α y` with `α ≥ 2` is in `Kr` (`p = 2^{α−2} X`, `q = 1`).
- **(K4) Shifts.** For `ϑ ∈ Kr` and `e : ℤ_[2]`, `(fun y => ϑ (y − e)) ∈ Kr`. (Formula: `a' = a + 2 p(−2e)/q(−2e)`, `p' = q(−2e) · p(X − 2e) − p(−2e) · q(X − 2e)`, `q' = q(−2e) · q(X − 2e)`.)
- **(K5) Inverses.** If `ϑ = r.eval` with `IsUnit r.a`, then `ϑ y` is a unit for every `y`, and `(fun y => Ring.inverse (ϑ y)) ∈ Kr`. (Formula: `a' = a⁻¹`, `p' = −p`, `q' = a · (a q + 2 p)`.)
- **(K6) Values modulo 4.** For `ϑ = r.eval` and every `y`: `∃ z, ϑ y − r.a = 4 * z`. In particular `ϑ y` is a unit iff `r.a` is.

## Part S — the homomorphism Θ (Lemma 10.13 (b))

- **(S0)** If `r.eval = r'.eval` then `thetaRep r = thetaRep r'`; hence `theta (r.eval) = thetaRep r` for every `r`.
- **(S1)** On `Kr`: `theta` is additive and multiplicative, `theta 1 = 1`, `theta (fun _ => a) = inl (red a)`, and `theta (fun y => a * ϑ y) = inl (red a) * theta ϑ`.
- **(S2) Shift invariance.** For `ϑ ∈ Kr` and every `e`, `theta (fun y => ϑ (y − e)) = theta ϑ`.
- **(S3) Kernel.** For `ϑ ∈ Kr`: `theta ϑ = 0 ↔ ∃ ψ ∈ Kr, ϑ = fun y => 2 * ψ y`.
- **(S4)** For `ϑ = r.eval` with `IsUnit r.a`: `theta (fun y => Ring.inverse (ϑ y)) * theta ϑ = 1`.
- **(S5) The constant term.** For `ϑ = r.eval`: `TrivSqZeroExt.fst (theta ϑ) = red r.a`; if `r.a` is even (`∃ z, r.a = 2 z`), then `theta ϑ * theta ϑ = 0`.

## Part R — the ring R_𝒮 (Lemma 10.14 (c))

- **(R1)** `RS` with the operations of Definition 7 is a commutative ring (in which `(2 : RS) = 0`).
- **(R2)** For every `β : RS`, `(β * β) Δ q = if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0`. (Proof: the terms `(Δ₁, a)` and `(Δ \ Δ₁, q − a)` pair up and cancel in characteristic 2; a term is its own partner only if `Δ₁ = Δ \ Δ₁`, that is `Δ = ∅`, and `a = q − a`; then `C(2a, a)` is even unless `a = 0`.)

## Part T — covariant systems (Lemma 10.14 (a), (b))

Fix `P : Finset ℕ`, `h : ℕ`, `c : ℤ_[2]`.

- **(T0)** `oS (D₁ ∪ D₂) = oS D₁ + oS D₂` for disjoint `D₁, D₂`.
- **(T1) Products.** For all `Γ Γ'`: `covSys P h c Γ * covSys P h c Γ' = covSys P h c (prodFun h Γ Γ')` (equality in `Matrix (Dn P) (Dn P) (Bf ℤ_[2])`). Moreover `covSys P h c Γ + covSys P h c Γ' = covSys P h c (Γ + Γ')`, `a • covSys P h c Γ = covSys P h c (a • Γ)`, and `1 = covSys P h c Γ₁` with `Γ₁ Δ m y = if Δ = ∅ ∧ m = 0 then 1 else 0`.
- **(T2) The class is a ring.** If `Γ Δ m ∈ Kr` and `Γ' Δ m ∈ Kr` for all `Δ m`, then `prodFun h Γ Γ' Δ m ∈ Kr` for all `Δ m`; likewise sums, constant multiples and `Γ₁`.
- **(T3) Θ_h is multiplicative.** Under the hypotheses of (T2), `thetaSys (prodFun h Γ Γ') = thetaSys Γ * thetaSys Γ'` in `RS`; and `thetaSys (Γ + Γ') = thetaSys Γ + thetaSys Γ'`, `thetaSys Γ₁ = 1`.

## Proof sketch

- (K1): `q(2y) ≡ q(0) (mod 2)` (the other coefficients are multiplied by powers of `2y`), and an element of `ℤ_[2]` congruent to a unit modulo 2 is a unit (`PadicInt.isUnit_iff`, norm 1). (K2): the polynomial `(a − a') q q' + 2 (p q' − p' q)` vanishes at every `X = 2y`, `y : ℤ_[2]`: infinitely many roots, so it is `0` (`Polynomial.eq_zero_of_infinite_isRoot`); its constant term `(a − a') q(0) q'(0)` gives `a = a'`, then `2 (p q' − p' q) = 0` and `ℤ_[2]` has no 2-torsion. (K3)–(K5): the formulas, with `Ring.inverse` of units; the new `p'(0) = 0` and the new `q'(0)` is a product of units. (K4) uses `p(−2e) ∈ 2ℤ_[2]` (since `p(0) = 0`). (K6): `p(2y) = 2y · (…)` since `p(0) = 0`.
- (S0): from (K2), `red` of `p q' = p' q` gives `p̄ q̄' = p̄' q̄` in `ZMod 2[X]`, so `p̄/q̄ = p̄'/q̄'` in `PowerSeries (ZMod 2)`. (S1): the formulas of (K3) reduced mod 2 (`2 p p'` disappears; `inr x * inr y = 0`). (S2): mod 2, `X − 2e ≡ X`, `p(−2e) ≡ 0`, `q(−2e) ≡ q(0)`, `2p(−2e)/q(−2e) ≡ 0`. (S3): `theta = 0` means `red a = 0` and `p̄ = 0`; then `ψ = (a/2, p/2, q)`. (S4): (S1) and (K5). (S5): `inr x * inr x = 0`.
- (R1): the operations are those of the commutative ring `𝒮 ⊗ (divided powers in F) ⊗ ΛE`; associativity from `C(q, a) C(q − a, b) = C(q, a + b) C(a + b, a)` and the bijection of ordered decompositions of `Δ`; commutativity from `Δ₁ ↔ Δ \ Δ₁`, `a ↔ q − a`. (R2) as stated.
- (T1): coefficientwise. The entry `(D, D')` of the product is `Σ_{D₁} Σ_a C(m, a) · G(D, D₁)_a(f) · G'(D₁, D')_{m−a}(f − a)`; only `D' ⊆ D₁ ⊆ D` contribute; with `Δ₁ := D \ D₁` the position of `(D₁, f − a)` is `2^h (f − a) + o_{D₁} + c = y − a 2^h − o_{Δ₁}` (T0), and `D₁ ↦ D \ D₁` is a bijection onto `(D \ D').powerset`. (T2): (K3), (K4). (T3): apply `theta` term by term; (S2) removes the shifts; (S1).

## Checks before formalization

`chkC47.py` (exact rationals; elements of `ℤ_2` as fractions with odd denominators; power series mod 2 truncated at degree 8): the formulas of (K3), (K4), (K5) give representations in the class with the right values at random points; (K6); (S0) on a second representation of the same function; (S1)–(S4); (R1) commutativity and associativity and (R2) for random `β` with `P = {0, 1, 3}`, `q < 5`; (T1) the product formula entry by entry for `P ⊆ {0, 1, 2}`, `h ≤ 3`, random `c`, floors `0…5`, `m < 4`, and (T2), (T3). 12 622 checks, 0 failures. Controls, all four fire: a representation with `p(0) ≠ 0` loses the mod-4 property; `Θ` without the factor `q̄⁻¹` is not multiplicative; without `E_t² = 0` (overlapping `Δ₁, Δ₂`) the square is not `β_0²`; the position without `− o_{Δ₁}` breaks (T1).
