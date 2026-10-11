# C40 — the formal operators: the algebra 𝔅, its action, the twist map, the V-split, the Schur step

Piece C40 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §10.3 «The formal dance», first part: the paragraphs «Formal operators», «The twist map», «The `V`-split», and the elimination step in the proof of Proposition 10.7). Folder `RequestProject/FormalOps/`, namespace `FormalOps`. The folders C1–C39b are certified: do not change them. The moves, cleanliness, the dance of a system, its final matrix, Lemma 10.6 and the count of Proposition 10.7 come in a later piece.

## Setting (reuse, do not redefine)

- C18 `DPLattice` (`M.ι`, `M.wt`, `M.Fd`, `H M`, the axioms `M.isDP.W_F`, `M.isDP.P0_F`, `M.isDP.P1_F`), `DPLattice.bvec`, `DPLattice.tensorV` and its coproduct formulas `tensorV_Fd_b0`, `tensorV_Fd_b1`.
- C20 `Doubling.OddUnits`, `Doubling.dfi` (`dfi s = ⅟(2s − 1)!!`), `Doubling.phi` (basis `Fin 2 × N.ι`, weights `wt(0, i) = 2 wt i + 1`, `wt(1, i) = 2 wt i − 1`) and its formulas `Doubling.B1`, `Doubling.B3`.
- C39 `FoldHalf.E0` (`∀ s ≥ BN, N.Fd s = 0 → ∀ r ≥ 2·BN, (phi N).Fd r = 0`).

Throughout `A` is a commutative ring; where `Doubling.phi` occurs, `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`. Two hypotheses on a DP-lattice `N` recur:
- **(top W)** `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)` (`W : ℤ`);
- **(nil BN)** `∀ s ≥ BN, N.Fd s = 0` (`BN : ℕ`).

Under (top W) the **floor** of the basis vector `i` is `fl i := (W − N.wt i) / 2` (integer division; exact by the parity). `F^{(r)}` lowers the weight by `2r`, so it raises the floor by `r`.

## Definitions (new)

- **`Bf A`**, the formal operators (the paper's `𝔅`): a type whose elements `x` carry coefficients `x.coef : ℕ → ℤ → A`; `x.coef m f` is the coefficient of `F^{(m)}` at the **target floor** `f`. It must be a new type (a structure with one field, or a type synonym with its own instances), so that its multiplication is not the pointwise one. Extensionality: `x = y ↔ ∀ m f, x.coef m f = y.coef m f`.
  - `0`, `+`, `−`, `n •`, `a •` (`a : A`) coefficientwise;
  - `1`: `coef 0 f = 1`, `coef m f = 0` for `m ≥ 1`;
  - **product** `(x * y).coef m f = Σ_{a ∈ range (m + 1)} (Nat.choose m a : A) * x.coef a f * y.coef (m − a) (f − a)`.
- `Bf.fd m` (the formal `F^{(m)}`): `coef m' f = if m' = m then 1 else 0`. `Bf.dg p` for `p : ℤ → A` (the floor function `p(D)`): `coef 0 f = p f`, `coef m f = 0` for `m ≥ 1`.
- **`flD N W p`** for `p : ℤ → A`: the diagonal operator `(flD N W p v) i = p ((W − N.wt i) / 2) * v i` on `N.ι → A`.
- **`act N W B x := Σ_{m ∈ range B} flD N W (x.coef m) * N.Fd m`** (the action of `x` on `N`; on a vector of floor `g` it is `Σ_m x_m(g + m) F^{(m)}`).
- **The twist map** (for `x : Bf A`, using `Doubling.dfi`):
  - `tw00 x`: `coef q f = dfi q * x.coef (2q) (2f)`;
  - `tw11 x`: `coef q f = dfi q * x.coef (2q) (2f + 1)`;
  - `tw10 x`: `coef q f = dfi (q + 1) * x.coef (2q + 1) (2f + 1)`;
  - `tw01 x`: `coef 0 f = 0` and `coef (q + 1) f = ((2q + 2 : ℕ) : A) * dfi (q + 1) * x.coef (2q + 1) (2f)`.
  (The first index is the coordinate slot, the second the source slot: `tw10` maps the `b_0` slot to the `b_1` slot.)
- **The `V`-split**: `vplus x`: `coef m g = x.coef m (g + 1)`; `vprime x`: `coef m g = x.coef (m + 1) (g + 1)`.
- **Block operators**: for `A`-modules `L₁ L₂ K₁ K₂`, `P : L₁ ≃ₗ[A] K₁`, `C : L₂ →ₗ[A] K₁`, `Bb : L₁ →ₗ[A] K₂`, `Dd : L₂ →ₗ[A] K₂`:
  `blockOp P C Bb Dd : L₁ × L₂ →ₗ[A] K₁ × K₂`, `(u, v) ↦ (P u + C v, Bb u + Dd v)`, and
  `schur P C Bb Dd := Dd − Bb ∘ₗ P.symm ∘ₗ C : L₂ →ₗ[A] K₂`.

## Part B — the algebra and its action

**(B1)** `Bf A` is a ring: give an instance `Ring (Bf A)` whose `0`, `1`, `+`, `−`, `*` are the ones above (associativity: `((x*y)*z).coef m f = Σ_{a+b+c=m} m!/(a! b! c!) · x_a(f) y_b(f − a) z_c(f − a − b)` both ways). Also `Algebra A (Bf A)`, or at least `(a • x) * y = a • (x * y) = x * (a • y)`. Simp lemmas: `coef_add`, `coef_mul`, `coef_one`, `coef_fd`, `coef_dg`.

**(B2)** `flD N W` is a ring map from `ℤ → A` (pointwise operations): `flD N W 1 = 1`, `flD N W (p + q) = flD N W p + flD N W q`, `flD N W (p * q) = flD N W p * flD N W q`.

**(B3)** (floor shift) Under (top W), for every `a : ℕ` and `p : ℤ → A`:
  `N.Fd a * flD N W p = flD N W (fun f => p (f − a)) * N.Fd a`.

**(B4)** (the action) Under (top W) and (nil BN), for all `B, B' ≥ BN`:
- `act N W B x = act N W B' x` (independence of the bound);
- `act N W B 1 = 1` (if `B ≥ 1`), `act N W B (x + y) = act N W B x + act N W B y`, `act N W B (a • x) = a • act N W B x`;
- **`act N W B (x * y) = act N W B x * act N W B y`**;
- `act N W B (Bf.fd m) = N.Fd m` for every `m`, and `act N W B (Bf.dg p) = flD N W p` (if `B ≥ 1`).

## Part T — the twist map (paper §10.3, «The twist map»)

Let `N : DPLattice A` satisfy (top W) and (nil BN).

**(T0)** `Doubling.phi N` satisfies (top (2W + 1)): `∀ i, (phi N).wt i ≤ 2W + 1 ∧ Even (2W + 1 − (phi N).wt i)`. (The floor of `b_e n` is `2·fl(n) + e`.)

**(T1)** For every `x : Bf A`, every `n : N.ι → A`, every `B ≥ 2·BN` and every `B' ≥ BN`:
- `act (phi N) (2W + 1) B x (bvec 0 n) = bvec 0 (act N W B' (tw00 x) n) + bvec 1 (act N W B' (tw10 x) n)`;
- `act (phi N) (2W + 1) B x (bvec 1 n) = bvec 0 (act N W B' (tw01 x) n) + bvec 1 (act N W B' (tw11 x) n)`.

*(Proof sketch: on a vector `b_e n` with `n` of floor `f'`, use B3: `F^{(2q)}(b_e n) = dfi q · b_e F^{(q)} n`, `F^{(2q+1)}(b_0 n) = dfi (q + 1) · b_1 F^{(q)} n`, `F^{(2q+1)}(b_1 n) = (2q + 2) dfi (q + 1) · b_0 F^{(q+1)} n`; the target floor in `phi N` is `2g` on the `b_0` slot and `2g + 1` on the `b_1` slot, `g` the floor in `N` of the target; reduce to basis vectors and use (W) of `N`. Terms with an index `≥ BN` vanish on both sides.)*

## Part V — the `V`-split (paper §10.3, «The `V`-split»)

Let `M : DPLattice A` satisfy (top W) and (nil BN) (any commutative ring `A`).

**(V0)** `DPLattice.tensorV M` satisfies (top (W + 1)) and (nil (BN + 1)). (The floor of `b_v ⊗ y` is `v + fl(y)`.)

**(V1)** For every `x : Bf A`, every `y : M.ι → A`, every `B ≥ BN + 1` and every `B' ≥ BN`:
- `act (tensorV M) (W + 1) B x (bvec 0 y) = bvec 0 (act M W B' x y) + bvec 1 (act M W B' (vprime x) y)`;
- `act (tensorV M) (W + 1) B x (bvec 1 y) = bvec 1 (act M W B' (vplus x) y)`.

*(Proof sketch: `F^{(m)}(b_0 y) = b_0 F^{(m)} y + b_1 F^{(m−1)} y` (`m ≥ 1`), `F^{(m)}(b_1 y) = b_1 F^{(m)} y`; the target `b_1 ⊗ F^{(m−1)} y` has floor `g + 1` with `g` the floor in `M` of `F^{(m−1)} y`.)*

## Part S — the Schur step (proof of Proposition 10.7)

For `A`-modules `L₁ L₂ K₁ K₂` and `P C Bb Dd` as above:

Below, `c • ⊤` may be written `LinearMap.range (c • LinearMap.id)` (the same submodule `c K₁`); say which.

**(S1)** For every `c : A`:
  `(K₁ × K₂) ⧸ range (c • blockOp P C Bb Dd) ≃ₗ[A] (K₁ ⧸ (c • ⊤ : Submodule A K₁)) × (K₂ ⧸ range (c • schur P C Bb Dd))`.

**(S2)** `(K₁ × K₂) ⧸ range (blockOp P C Bb Dd) ≃ₗ[A] K₂ ⧸ range (schur P C Bb Dd)`.

**(S3)** If `schur P C Bb Dd = (2 : A) • G'` for some `G' : L₂ →ₗ[A] K₂`, then for every `h : ℕ`:
  `(K₁ × K₂) ⧸ range ((2 : A) ^ h • blockOp P C Bb Dd) ≃ₗ[A] (K₁ ⧸ ((2 : A) ^ h • ⊤ : Submodule A K₁)) × (K₂ ⧸ range ((2 : A) ^ (h + 1) • G'))`.

*(Proof sketch: the unimodular operations `(u, v) ↦ (u − P⁻¹ C v, v)` on the source and `(k₁, k₂) ↦ (k₁, k₂ − Bb P⁻¹ k₁)` on the target turn `blockOp` into `(u, v) ↦ (P u, schur v)`; then `c • P` has range `c • ⊤` since `P` is onto.)*

## Checks done before sending

- Brute force (`chkC40.py`, independent lattice model of `T(λ)`, `Φ` and `V ⊗ −` from `chk_lattice_lib.py`, `F^{(r)} = F^r/r!` over `ℚ`, exact rationals; random integer formal operators with `m < 7` on floors `[−3, 11]`): (B1) associativity, units, distributivity; (B2)–(B4) on `T(m)`, `m ≤ 5`, with the top `W = m`: `act 1 = 1`, additivity, **multiplicativity**, independence of the bound, the floor shift (B3) for `a ≤ 3`; (T0)–(T1) on `Φ(T(m))`, `m ≤ 4`, every block; (V0)–(V1) on `V ⊗ T(m)` and `V ⊗ Φ(T(m))`, `m ≤ 4`, every block; (S1) on 120 random integer block matrices (`P` unimodular of size `≤ 3`, `C`, `Bb`, `Dd` of size `≤ 3`), `c = 2^h`, `h ≤ 3`, equal 2-adic Smith forms. 773 checks, 0 failures. `logs/chkC40.log`.
- Controls (all six must fire, and do): the product without the binomial coefficients; the product with the shift on the wrong side (`y_b(f + a)`); `tw01` read at `2f + 1`; `tw00` without the odd denominators; `vprime` without the floor shift; (S1) without the summand `K₁/cK₁`.

## Instructions

Encodings are your choice provided they are faithful; say in a docstring how each object is encoded. Keep the statements exactly as in this file (more general statements are fine if noted; say if a hypothesis is unused). Every docstring should name the part of `C40_the_formal_operators.md` it corresponds to. No `sorry`, no new axiom, no `native_decide`.
