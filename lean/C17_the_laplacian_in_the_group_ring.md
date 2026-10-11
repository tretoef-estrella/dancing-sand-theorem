# The Laplacian of the cube in the group ring (§2.1)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §2.1 (the Laplacian in the group ring, Lemma 2.1, and the reduction `ℤ_2 ⊕ Syl_2 K(Q_n) ≅ coker(σ on R ⊗ ℤ_2)`). This is the first piece of stage 1c: it starts the certificate from the graph `Q_n` itself. The dictionary with `V^{⊗n}` (Lemma 2.2) and the family decomposition (Theorem 3.6) are later pieces. Nothing of pieces C1–C16 is needed here.

## Setting

Let `n ∈ ℕ` and `G := Fin n → ZMod 2` (the group `(ℤ/2)^n`, written additively), with generators `e_i := Pi.single i 1`.

**The cube and its Laplacian.** The cube `Q_n` is the Cayley graph of `G` with the generators `e_i`: `g` and `g + e_i` are joined, for every `i`. Every vertex has degree `n`. Its Laplacian acts on `ℤ^G = (G → ℤ)` by
  `(L f)(g) := n · f(g) − Σ_{i<n} f(g + e_i)`.
**The sandpile group** is the torsion of the cokernel:
  `K(Q_n) := torsion of the ℤ-module (G → ℤ) ⧸ range L`
(Mathlib's `Submodule.torsion ℤ`). Its **2-part** is `Syl_2 K(Q_n) := {x ∈ K(Q_n) : 2^e • x = 0 for some e}`.

**The group ring.** `R := ℤ[G]`, encoded as `AddMonoidAlgebra ℤ G` (so the product of `x_g` and `x_h` is `x_{g+h}`). Put `x_i := x_{e_i}`, `s_i := 1 − x_i`, and for `S : Finset (Fin n)`, `s_S := ∏_{i∈S} s_i` (`s_∅ = 1`). Put
  `σ := Σ_{i<n} (1 − x_i) = Σ_i s_i ∈ R`.
For `S` define `U(s_S) := Σ_{j ∉ S} s_{S ∪ {j}}` and `D(s_S) := |S| · s_S`.

The identification of `R` with `ℤ^G` sends `f = Σ_g f(g) x_g` to the function `g ↦ f(g)` (`AddMonoidAlgebra ℤ G = G →₀ ℤ`, and `G` is finite).

## Part A — Lemma 2.1

**(A1)** `s_j · s_j = 2 s_j` for every `j`.

**(A2) (Lemma 2.1)** For `j` and `S`: `s_j · s_S = s_{S ∪ {j}}` if `j ∉ S`, and `s_j · s_S = 2 s_S` if `j ∈ S`.

**(A3)** `σ · s_S = Σ_{j ∉ S} s_{S∪{j}} + 2|S| · s_S`, that is, `σ = U + 2D` on the elements `s_S`.

**(A4)** The family `(s_S)_{S ⊆ Fin n}` is a `ℤ`-basis of `R` (stated as: there is a `Basis (Finset (Fin n)) ℤ R` whose `S`-th vector is `s_S`). *Proof sketch:* `x_T = ∏_{i∈T}(1 − s_i) = Σ_{S ⊆ T} (−1)^{|S|} s_S`, so the change of basis from `{x_T}` to `{s_S}` is unitriangular for inclusion; `|Finset (Fin n)| = |G| = 2^n`.

## Part B — the Laplacian is multiplication by σ

**(B1)** For every `f ∈ R` and every `g ∈ G`: `(σ · f)(g) = n · f(g) − Σ_{i<n} f(g + e_i)` (note `g − e_i = g + e_i` in `G`). In other words, under the identification `R = ℤ^G`, multiplication by `σ` is `L`.

**(B2)** Consequently `(G → ℤ) ⧸ range L ≃ₗ[ℤ] R ⧸ range (σ · −)` (as `ℤ`-modules, where `σ · −` is left multiplication).

## Part C — one free summand, and a finite rest

Write `R_+ := span_ℤ {s_S : S ≠ ∅}` (the augmentation ideal).

**(C1)** The coefficient of `s_∅` in `σ · f` is `0` for every `f ∈ R` (in the basis of (A4)); that is, `range (σ · −) ⊆ R_+`.

**(C2)** The restriction of `σ · −` to `R_+` maps `R_+` to `R_+`, and, in the basis `{s_S : S ≠ ∅}` ordered by `|S|`, it is lower triangular with diagonal entries `2|S| ≠ 0`. In particular it is injective, and `range (σ · −) ⊇ σ · R_+` has finite index in `R_+`.

**(C3)** `R ⧸ range (σ · −) ≃ₗ[ℤ] ℤ × (R_+ ⧸ range (σ · −))`, and `T(n) := R_+ ⧸ range(σ · −)` is finite. (The `ℤ` is spanned by the class of `s_∅ = 1`.)

**(C4)** `K(Q_n) ≃ₗ[ℤ] T(n)`. In particular `K(Q_n)` is finite, and `(G → ℤ) ⧸ range L ≃ₗ[ℤ] ℤ × K(Q_n)` (the paper's `coker(σ on R) ≅ ℤ ⊕ K(Q_n)`).

## Part D — the 2-adic reduction

Let `A := ℤ_[2]`. Write `σ_A : (G → A) → (G → A)` for `(σ_A f)(g) := n · f(g) − Σ_{i<n} f(g + e_i)` (the Laplacian with coefficients in `A`).

**(D1)** For every finite abelian group `T` (a finite `ℤ`-module), `T ⊗_ℤ A ≃+ Syl_2 T` as additive groups, where `Syl_2 T := {x : 2^e • x = 0 for some e}`. *Proof sketch:* `T = Syl_2 T ⊕ T_odd`; multiplication by an odd integer is bijective on `T_odd` and invertible on `A` (an odd integer is a unit of `ℤ_2`), so `T_odd ⊗ A = 0`; and if `2^e • Syl_2 T = 0`, then `Syl_2 T ⊗ A = Syl_2 T ⊗ (A ⧸ 2^e A)` and `A ⧸ 2^e A ≅ ℤ ⧸ 2^e` (`PadicInt.toZModPow`).

**(D2) (the last claim of §2.1)** `(G → A) ⧸ range σ_A ≃+ A × Syl_2 K(Q_n)`.
*Proof sketch:* `⊗_ℤ A` is right exact, so `((G → ℤ) ⧸ range L) ⊗ A ≅ (G → A) ⧸ range σ_A`; then (C4) and (D1).
