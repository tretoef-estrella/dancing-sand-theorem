# The dance (Proposition 4.3, §3.3–§4.3)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §3.3 (the dance lattices `T(λ)`, built digit by digit), §3.4 (the operator `σ^{(α)}_i`), and Proposition 4.3 (the dance: the twist and split moves applied digit by digit). As in pieces C11 and C12, everything is over **any commutative ring `A`**, and the moves are used in their **scaled form**. The identification of the final matrix with the closed form of Theorem 4.4 comes in the next piece; here the final matrix is the one the moves produce.

This file reuses, without changing them:
- piece C11 (`RequestProject/Payment/`): `Payment.Sys`, `slotLof`, `slotEmb`, `Payment.G` (halved data), the double `NΦ`, `flΦ`, `FΦ`, the twisted data `pT`, `κT`, and `Payment.theorem_A`;
- piece C12 (`RequestProject/Split/`): the split model `NΨ`, `flΨ`, `FΨ`, the split data `pSp`, `κSp` on the slot type `Lex (S × Fin 2)`, and `Split.theorem_B`.

## Setting

`A` is a commutative ring. Write `n(ds) := length ds` and `m(ds) := number of entries equal to true`.

**Digit lists.** A *digit list* is a list `ds : List Bool`, read from the lowest digit: `ds = [d_0, d_1, …, d_{k−1}]` with `d_t = true` iff `t ∈ I`, where `λ + 1 = 2^k + Σ_{t∈I} 2^t`. (Every `λ ≥ 0` has exactly one such list.)

**The tower `T(ds)`.** A graded family (as in C11), all of whose modules are `A`, defined by recursion on `ds`:
- `T([])`: index type `Unit`, floor `0`, operator `F = 0`;
- `T(false :: rest) := Φ(T(rest))`: index type `Idx(rest) × Fin 2`, floor `flΦ`, operator `FΦ` (C11);
- `T(true :: rest) := Ψ(T(rest))`: index type `Idx(rest) × Fin 4`, floor `flΨ`, operator `FΨ` (C12).
Write `Idx(ds)`, `fl_ds`, `F_ds` for its index type, floor and operator. (The paper's `T(2l + 2)` is `V ⊗ Φ(T(l))`; it is equivalent to `Ψ(T(l))` by the change of basis of C12, (A3), which identifies the payment systems slot by slot. Building the tower with `Ψ` is a choice of basis.)

**Relabelling the split slots.** The split slot type `Lex (Fin r × Fin 2)` is order-isomorphic to `Fin (r * 2)` by `(s, j) ↦ 2s + j` (this is `finProdFinEquiv`, read through `toLex`/`ofLex`; it is monotone for the lexicographic order). For data on `Lex (Fin r × Fin 2)` write `relab` for the data on `Fin (r * 2)` obtained by composing with the inverse of this order isomorphism (in every slot argument).

**The dance data.** For halved data `(p, κ)` on slots `Fin r`, define data on slots `Fin (r * 2^{m(ds)})` by recursion on `ds`:
- `dance [] r p κ := (p, κ)`;
- `dance (false :: rest) r p κ := dance rest r (pT p) (κT p κ)`;
- `dance (true :: rest) r p κ := dance rest (r * 2) (relab (pSp p)) (relab (κSp p κ))`.
(The slot count is `r * 2^{m(ds)}`; the cast between `Fin (r * 2 * 2^{m(rest)})` and `Fin (r * 2^{m(ds)})` is your choice of encoding, e.g. `Fin.cast` with `pow_succ`/`mul_assoc`.)

**The final matrix.** For data `(p, κ)` on slots `Fin R` (on `T([])`, whose only floor is `0`), let `Mfin(p, κ) : Matrix (Fin R) (Fin R) A` have entries
  `Mfin s s' := 2 p_s(0)` if `s = s'`,  `2 κ_{s s'}(0)` if `s' < s`,  `0` if `s < s'`.
(Lower triangular. On `T([])` the payment system `G[0, 0, p, κ]` is this matrix acting on `Sys (fun _ => A) (Fin R) ≅ (Fin R → A)`.)

**The operator `σ`.** For `α ≥ 1` and `i ∈ ℕ`, the halved data of size 1 of `σ^{(α)}_i = F + 2^α(D + i)` are `pσ(f) := 2^{α−1} (i + f)` (in `A`), `κσ := 0`. So `σ^{(α)}_i := G[fl_ds, F_ds, pσ, κσ]` on `Sys (fun _ => A) (Fin 1)`.

## Part R — relabelling slots

**(R1)** For slot types `S`, `S'` with an order isomorphism `e : S ≃o S'`, and halved data `(p', κ')` on `S'`, let `p := p' ∘ e`, `κ s u := κ' (e s) (e u)`. The slotwise relabelling `Sys N S ≃ₗ[A] Sys N S'` (`x ι_{s,i} ↦ x ι_{e s, i}`) intertwines `G[fl, F, p, κ]` and `G[fl, F, p', κ']`; consequently, for every `c ∈ A`, `coker(c · G[fl, F, p, κ]) ≅ coker(c · G[fl, F, p', κ'])`.

*Proof.* `e` preserves the order, so the coupling sum over `{s : s > s'}` is carried to the sum over `{u : u > e s'}`. ∎

## Part D — the dance

**(D1) The scaled dance.** For every digit list `ds`, every `r`, all halved data `(p, κ)` on `Fin r` for `T(ds)`, and every `h ∈ ℕ`, there is an `A`-linear isomorphism
  `Sys(T(ds), Fin r) ⧸ range(2^h · G[fl_ds, F_ds, p, κ])`
  `≅ Clocks(ds, r, h) × Sys(T([]), Fin(r·2^{m(ds)})) ⧸ range(2^{h + n(ds)} · G[0, 0, dance ds r p κ])`,
where `Clocks(ds, r, h)` is defined by recursion: `Clocks([], r, h) := Unit` (or `PUnit`, the zero module);
`Clocks(false :: rest, r, h) := (Sys(T(rest), Fin r) ⧸ 2^h·⊤) × Clocks(rest, r, h + 1)`;
`Clocks(true :: rest, r, h) := (Sys(T(rest), Fin r) ⧸ 2^h·⊤) × (Sys(T(rest), Fin r) ⧸ 2^h·⊤) × Clocks(rest, r · 2, h + 1)`.
(The order of the factors is your choice of encoding.)

*Proof.* Induction on `ds`. For `false :: rest`, `T(ds) = Φ(T(rest))` and Theorem A of C11 with `c = 2^h` gives `coker(2^h G) ≅ (M^S/2^h M^S) × coker(2^h·2·G')` with `G' = G[fl_rest, F_rest, pT p, κT p κ]`, and `2^h · 2 = 2^{h+1}`; apply the induction hypothesis at `h + 1`. For `true :: rest`, Theorem B of C12 with `c = 2^h` gives two copies of `M^S/2^h M^S` times `coker(2^{h+1} G'')` on the slot type `Lex (Fin r × Fin 2)`; relabel by (R1) to `Fin (r * 2)` and apply the induction hypothesis at `h + 1`. ∎

**(D2) The clocks are free quotients with the paper's counts.** For every `ds`, `r`, `h`:
  `Clocks(ds, r, h) ≅ Π_{j < n(ds)} ((Fin (r · 2^{n(ds) + m(ds) − 1 − j}) → A) ⧸ 2^{h+j}·⊤)`  (as `A`-modules).
Equivalently: at move `j` the factor is `A/2^{h+j}` to the power of half the rank of the system at that stage.

*Proof.* `Sys(T(ds'), Fin r')` is free of rank `r' · 2^{n(ds') + m(ds')}` (the tower has `2^{n + m}` indices: `Φ` doubles them and `Ψ` multiplies them by 4; all modules are `A`). At move `j` with digit `d_j` and current slot count `r_j = r · 2^{m(d_0, …, d_{j−1})}`, the factor is one copy (`d_j = false`) or two copies (`d_j = true`) of `Sys(T(d_{j+1}, …), Fin r_j)`, of rank `r_j · 2^{(n − j − 1) + m(d_{j+1}, …)}` each; in both cases the total rank is `r · 2^{n + m − 1 − j}`. Use `(X ⧸ c⊤) × (Y ⧸ c⊤) ≅ (X × Y) ⧸ c⊤` and `(Fin a → A) ≅ Sys` by a choice of bases. ∎

**(D3) The final system is the final matrix.** For data `(p, κ)` on `Fin R` over `T([])` and every `c ∈ A`:
  `Sys(T([]), Fin R) ⧸ range(c · G[0, 0, p, κ]) ≅ (Fin R → A) ⧸ range(c · Matrix.toLin' (Mfin p κ))`.

*Proof.* `Sys(T([]), Fin R) = ⨁_{(s, ()) } A ≅ (Fin R → A)`; on the generator of slot `s'`, `G` gives `2p_{s'}(0) e_{s'} + Σ_{s > s'} 2κ_{s s'}(0) e_s`, the column `s'` of `Mfin` (`F = 0` on `T([])`). ∎

**Proposition 4.3 (the dance).** Let `ds` be the digit list of `λ` (`k := n(ds)`, `|I| = m(ds)`), `α ≥ 1`, `i ∈ ℕ`, and let `(p_k, κ_k) := dance ds 1 pσ κσ` (data on `Fin (1 · 2^{|I|})`) and `M := Mfin(p_k, κ_k)`. Then
  `X^{(α)}(λ, i) := Sys(T(ds), Fin 1) ⧸ range(σ^{(α)}_i)`
  `≅ Π_{a < k} ((Fin (2^{k + |I| − 1 − a}) → A) ⧸ 2^a·⊤)  ×  (Fin (2^{|I|}) → A) ⧸ range(2^k · Matrix.toLin' M)`.
The factor `a = 0` is the zero module (`2^0 = 1`); for `A = ℤ_2` (or `ℤ`) the factors `a ≥ 1` are the paper's small clocks `(ℤ/2^a)^{2^{|I| + k − 1 − a}}`, and the last factor is `coker(2^k M)`.

*Proof.* (D1) with `r = 1`, `h = 0`, then (D2) and (D3). ∎

**(D4) The final matrix is lower triangular, with an even diagonal.** For every `ds`, `r`, `(p, κ)`: `Mfin (dance ds r p κ)` has `Mfin s s' = 0` for `s < s'`, and every diagonal entry and every entry below the diagonal lies in `2A` (it is `2 ×` an element of `A`).

## Checks before formalization

`lean/chkC13.py` (log `logs/chkC13.log`): over `ℤ`, every digit list with `1 ≤ n(ds) ≤ 4` and `n(ds) + m(ds) ≤ 5` (rank of `T(ds)` at most 32), `α ∈ {1, 2}`, `i ∈ {0, 1, 2, 3}`: the invariant factors (sympy) of the matrix of `σ^{(α)}_i` on `T(ds)` equal those of the small clocks of Proposition 4.3 together with `coker(2^k M)`, `M` computed by iterating the formulas of `pT`, `κT`, `pSp`, `κSp` and the relabelling `(s, j) ↦ 2s + j`. Also, for `r = 2` and random halved data, (D1) with `h ∈ {0, 1}` in the explicit form of (D2). Cross-check with the next piece: the invariant factors of `M` equal those of the closed-form matrix `Mc` of C10 (Theorem 4.4). Result: 144 checks of Proposition 4.3, 120 of (D1) with `r = 2`, 144 of (D4), and 144 cross-checks with `Mc` (Theorem 4.4): 0 failures. Controls, each of which must fail somewhere, and does: the digits processed from the top (80); the slots relabelled in the reversed order `(s, j) ↦ 2(r − 1 − s) + j` (46); the clocks at exponent `a + 1` (144); the final factor `2^{k − 1} M` (136). (A first control, the relabelling `(s, j) ↦ s + r j`, could not fail: it respects the order on every pair where `κ''` is non-zero. It was replaced; that log is kept as `logs/chkC13_v1_silent_control.log`.)
