# Divided-power lattices, the natural module, and the dictionary (§2.2–§2.3, first half)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §2.2 (the hyperalgebra, Kostant's formula (K), the natural module `V`, Lemma 2.2 the dictionary, Corollary 2.3) and §2.3 (the Weyl lattices `Δ_A(λ)` and `∇_A(λ)`). This is the second piece of stage 1c. It reuses piece C17 (`RequestProject/CubeLaplacian/`): `CubeLaplacian.G`, `CubeLaplacian.e`, `CubeLaplacian.lap`, `CubeLaplacian.K`, `CubeLaplacian.Syl2`, `CubeLaplacian.D2`.

## Why an encoding is needed

Mathlib has no Kostant `ℤ`-form of `U(sl_2)`. The paper uses only lattices on which `H` acts diagonally with integer weights, and only the divided powers `E^{(s)}`, `F^{(r)}` and Kostant's formula (K). So a lattice is encoded by its data: a finite basis of weight vectors, and the two families of divided powers, subject to the relations that `Dist_ℤ` imposes (Kostant: `Dist_ℤ` is spanned by the products `F^{(a)} C(H, b) E^{(c)}`, and these relations give the normal order). The operators `C(H, b)` act on a weight vector of weight `w` by the generalized binomial `C(w, b)` (Mathlib's `Ring.choose`), so they need no data of their own.

## Setting

Let `A` be a commutative ring (later `A = ℤ_[2]`). Binomial coefficients `C(a, b)` with `a ∈ ℤ` are `Ring.choose a b`, cast to `A`.

**Divided-power lattice.** A *DP-lattice* over `A` is:
- a finite type `ι` with decidable equality (the basis) and a weight `wt : ι → ℤ`;
- the module `M := ι → A`, with `δ_i := Pi.single i 1`;
- two families `Fd, Ed : ℕ → Module.End A M` (written `F^{(r)}`, `E^{(s)}`),

such that:
- **(W)** for every `i` and `r`, `F^{(r)} δ_i` is a combination of the `δ_j` with `wt j = wt i − 2r`, and `E^{(r)} δ_i` of the `δ_j` with `wt j = wt i + 2r`;
- **(P0)** `F^{(0)} = 1` and `E^{(0)} = 1`;
- **(P1)** `F^{(a)} ∘ F^{(b)} = C(a + b, a) · F^{(a+b)}` and `E^{(a)} ∘ E^{(b)} = C(a + b, a) · E^{(a+b)}`;
- **(K)** for every `i`, `r`, `s`:
  `E^{(s)} F^{(r)} δ_i = Σ_{j=0}^{min(r,s)} C(wt i + s − r, j) · F^{(r−j)} E^{(s−j)} δ_i`.

(This is Kostant's formula `E^{(s)} F^{(r)} = Σ_j F^{(r−j)} C(H − r − s + 2j, j) E^{(s−j)}` evaluated on a vector of weight `w`: the operator `C(H − r − s + 2j, j)` acts on `E^{(s−j)} δ_i`, of weight `w + 2(s − j)`, by `C(w + s − r, j)`.) The operator **`H`** is `H δ_i := wt i · δ_i`, and `F := F^{(1)}`.

A **morphism** of DP-lattices is an `A`-linear map commuting with every `F^{(r)}`, every `E^{(s)}`, and `H`.

**The trivial lattice** `𝟙`: `ι = Unit`, weight `0`, `F^{(r)} = E^{(r)} = 0` for `r ≥ 1`.

**The natural module `V`**: `ι = Fin 2`, `wt 0 = 1`, `wt 1 = −1` (so `b_0 := δ_0`, `b_1 := δ_1`); `F^{(1)} b_0 = b_1`, `F^{(1)} b_1 = 0`, `E^{(1)} b_1 = b_0`, `E^{(1)} b_0 = 0`, and `F^{(r)} = E^{(r)} = 0` for `r ≥ 2`.

**`V ⊗ M`** (the coproduct `Δ(F^{(r)}) = Σ_{a+b=r} F^{(a)} ⊗ F^{(b)}`, the same for `E`, `Δ(H) = H ⊗ 1 + 1 ⊗ H`): basis `Fin 2 × ι`, `wt(e, i) = wt_V(e) + wt(i)`, and, writing `b_e m` for the vector with `m` in the slot `e`,
  `F^{(r)}(b_0 m) = b_0 F^{(r)} m + b_1 F^{(r−1)} m` (`r ≥ 1`), `F^{(r)}(b_1 m) = b_1 F^{(r)} m`,
  `E^{(r)}(b_1 m) = b_1 E^{(r)} m + b_0 E^{(r−1)} m` (`r ≥ 1`), `E^{(r)}(b_0 m) = b_0 E^{(r)} m`.

**`V^{⊗n}`**: `V^{⊗0} := 𝟙`, `V^{⊗(n+1)} := V ⊗ V^{⊗n}`. Its basis is `Fin 2 × (Fin 2 × ⋯ × Unit)`; a basis vector is a pure tensor `b_{e_1} ⊗ ⋯ ⊗ b_{e_n}`, determined by the set of positions with `e_t = 1`.

**Weyl lattices** (§2.3). For `λ ∈ ℕ`: `Δ_A(λ)` has basis `e_r` (`ι = Fin (λ + 1)`), `wt(e_r) = λ − 2r`,
  `F^{(t)} e_r = C(r + t, t) e_{r+t}` (`0` if `r + t > λ`),  `E^{(s)} e_r = C(λ − r + s, s) e_{r−s}` (`0` if `s > r`).
The dual Weyl lattice `∇_A(λ)` has basis `w_r`, `wt(w_r) = λ − 2r`,
  `F^{(t)} w_r = C(λ − r, t) w_{r+t}` (`0` if `r + t > λ`),  `E^{(s)} w_r = C(r, s) w_{r−s}` (`0` if `s > r`).
(So `F w_r = (λ − r) w_{r+1}` and `E w_r = r w_{r−1}`, as in §2.3.)

## Part T — the constructions are DP-lattices

**(T1)** `𝟙` and `V` are DP-lattices.
**(T2)** If `M` is a DP-lattice then `V ⊗ M` is a DP-lattice.
**(T3)** Hence `V^{⊗n}` is a DP-lattice for every `n`.
**(T4)** `Δ_A(λ)` and `∇_A(λ)` are DP-lattices for every `λ`.
**(T5)** `Δ_A(0) = ∇_A(0) = 𝟙`, and `Δ_A(1) = ∇_A(1) = V` (equal data under `Fin 1 ≃ Unit`, `Fin 2 = Fin 2`).

## Part L — Lemma 2.2, the dictionary

**(L1)** For every `n`, the operators on `V^{⊗n}`: `F^{(1)}` sends the pure tensor with letters `b_1` on a set `S` of positions to the sum, over the positions `j ∉ S`, of the pure tensor with letters `b_1` on `S ∪ {j}`; and `H` multiplies it by `n − 2|S|`.

**(L2) (Lemma 2.2)** There is an `A`-linear equivalence `Ψ : (G n → A) ≃ₗ[A] V^{⊗n}` (where `G n` and the Laplacian `lap A n` are those of piece C17) such that
  `Ψ ∘ lap A n = (F^{(1)} + n − H) ∘ Ψ`.
*Proof sketch:* in the group ring `A[G]` (identified with `G → A` by `f ↦ (g ↦ f(g))`), the elements `s_S = ∏_{i∈S}(1 − x_i)` form an `A`-basis and multiplication by `σ = Σ_i (1 − x_i)` is the Laplacian (piece C17, (A3), (A4), (B1), with `ℤ` replaced by `A`); `Ψ` sends `s_S` to the pure tensor with `b_1` on `S` (positions matched by any fixed bijection); then `σ s_S = Σ_{j∉S} s_{S∪{j}} + 2|S| s_S` becomes `(F^{(1)} + n − H)`, because `n − (n − 2|S|) = 2|S|`.

## Part C — Corollary 2.3

**(C1)** Let `(M_j)_{j ∈ J}` be a finite family of DP-lattices and `Θ : V^{⊗n} ≃ₗ[A] Π_j M_j` an `A`-linear equivalence that commutes with `F^{(1)}` and with `H` (componentwise on the right). Then
  `(G n → A) ⧸ range (lap A n) ≃ₗ[A] Π_j (M_j ⧸ range (F^{(1)} + n − H on M_j))`.
**(C2)** With `A = ℤ_[2]` and piece C17 (D2): under the hypothesis of (C1),
  `ℤ_[2] × Syl_2 K(Q_n) ≃+ Π_j (M_j ⧸ range (F^{(1)} + n − H on M_j))`.
