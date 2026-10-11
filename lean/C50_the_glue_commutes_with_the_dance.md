# The glue commutes with the dance (paper v8 §10.7, Lemma 10.19)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.7, Lemma 10.19.

§10.7 proves the fold law on the even families. By C39 (A4_even) and C39b (V6), both sides of an even family are cokernels of glued operators on `T(l) × T(l)`. A glued operator has the form `(m, m') ↦ (X m, Z m + Y m')`, where `2Z = Y − X`. This piece is the first step of §10.7. Gluing commutes with the formal dance (C40b), provided the two arms are congruent modulo `2` at every level of their dances.

The paper proves it by conjugating with the scalar matrix `[[1, 0], [1/2, 1]]`. That matrix is not integral, so here the proof uses block formulas with no division:
- the pivot of a glued system has the glued inverse `glue(Q_X, Q_Y, −Q_Y P_Z Q_X)`;
- the lower-left block `L` of the glued Schur complement satisfies `2L = S_Y − S_X` up to agreement;
- since `ℤ_[2]` has no `2`-torsion, `S_X = 2X'`, `S_Y = 2Y'` and `Y' − X' = 2W` give `L = 2W`.

Folder `RequestProject/GlueDance/`, namespace `GlueDance`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps`: `Bf` (its ring structure and `ℤ_[2]`-action), `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`.
- C40b `FormalDance`: `Agree`, `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`, and the lemmas `Agree.*`, `MAgree.*` of `FormalDance/PartC.lean` (`MAgree.add`, `sub`, `mul`, `smul`, `twP`, `twC`, `twB`, `twD`, `vsplit`, …).
- C13 `Dance`: `slots`, `slots_eq`, `splitIso`, `splitIso_apply`.
- C49b `ContZero`: `MCong`, (K3), (K5).
- C48 `Cleanliness.L1` (a clean move transported along an equivalence of index types); C48b `DanceXi.T1`.
- Mathlib: `finProdFinEquiv`, `finCongr`, `Matrix.submatrix`.

Throughout, `A := ℤ_[2]`.

## Definitions (new)

- `glueM {n : Type*} (X Y Z : Matrix n n (Bf ℤ_[2])) : Matrix (Fin 2 × n) (Fin 2 × n) (Bf ℤ_[2]) :=`
  `fun p p' => if p.1 = 0 ∧ p'.1 = 0 then X p.2 p'.2 else if p.1 = 1 ∧ p'.1 = 0 then Z p.2 p'.2 else if p.1 = 1 ∧ p'.1 = 1 then Y p.2 p'.2 else 0`.
  (Entry `[p, p']` maps the source slot `p'` to the coordinate slot `p`, as in C40b `paySys`: the block `[[X, 0], [Z, Y]]`, the glue index on top. This is the operator `(m, m') ↦ (X m, Z m + Y m')` of C39 `FoldHalf.glueOp`.)
- `gE {r r₂ : ℕ} (h : r₂ = 2 * r) : Fin 2 × Fin r ≃ Fin r₂ := finProdFinEquiv.trans (finCongr h.symm)` (the glue index is the top digit: `(g, s) ↦ s + r g`).
- `glueC {r r₂ : ℕ} (h : r₂ = 2 * r) (X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) : Matrix (Fin r₂) (Fin r₂) (Bf ℤ_[2]) := fun j j' => glueM X Y Z ((gE h).symm j) ((gE h).symm j')`.
- `relab {r : ℕ} (M : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])) : Matrix (Fin (r * 2)) (Fin (r * 2)) (Bf ℤ_[2]) := fun j j' => M (ofLex ((Dance.splitIso r).symm j)) (ofLex ((Dance.splitIso r).symm j'))` (the relabelling inside C40b `DanceRel`).
- `PairRel : (ds : List Bool) → (r : ℕ) → (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) → (Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])) → Prop`, by recursion on `ds` (two dances side by side, with the two arms congruent modulo `2` at every level):
  - `[], _, X, Y, Xk, Yk => MCong 1 Y X ∧ MAgree X Xk ∧ MAgree Y Yk`;
  - `false :: rest, r, X, Y, Xk, Yk => MCong 1 Y X ∧ ∃ X' Y', CleanStep X X' ∧ CleanStep Y Y' ∧ PairRel rest r X' Y' Xk Yk`;
  - `true :: rest, r, X, Y, Xk, Yk => MCong 1 Y X ∧ ∃ X'' Y'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2]), CleanStep (vsplit X) X'' ∧ CleanStep (vsplit Y) Y'' ∧ PairRel rest (r * 2) (relab X'') (relab Y'') Xk Yk`.

## Part B — block algebra

For `n` a `Fintype` with `DecidableEq`, `X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])`:

- **(B1)** `glueM X Y Z * glueM X' Y' Z' = glueM (X * X') (Y * Y') (Z * X' + Y * Z')`; `glueM 1 1 0 = 1`; `glueM X Y Z + glueM X' Y' Z' = glueM (X + X') (Y + Y') (Z + Z')`; `glueM X Y Z - glueM X' Y' Z' = glueM (X - X') (Y - Y') (Z - Z')`; `(a : ℤ_[2]) • glueM X Y Z = glueM (a • X) (a • Y) (a • Z)`.
- **(B2)** `twP (glueM X Y Z) = glueM (twP X) (twP Y) (twP Z)`, and the same for `twC`, `twB`, `twD`.
- **(B3)** `MAgree X X' → MAgree Y Y' → MAgree Z Z' → MAgree (glueM X Y Z) (glueM X' Y' Z')`; conversely `MAgree (glueM X Y Z) (glueM X' Y' Z')` gives the three agreements.
- **(B4)** No `2`-torsion: for `G H : Matrix n n (Bf ℤ_[2])`, `MAgree ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H) → MAgree G H`.

## Part G — one twist move

- **(G2)** For `n` a `Fintype` with `DecidableEq` and `X Y Z X' Y' W : Matrix n n (Bf ℤ_[2])`:
  if `CleanStep X X'`, `CleanStep Y Y'`, `MAgree (Y - X) ((2 : ℤ_[2]) • Z)` and `MAgree (Y' - X') ((2 : ℤ_[2]) • W)`, then `CleanStep (glueM X Y Z) (glueM X' Y' W)`.

## Part S — one V-split, and the relabelling

For `r r₂ : ℕ` and `h : r₂ = 2 * r`:

- **(S1)** For `X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])`: `vsplit (glueC h X Y Z) = fun q q' => glueM (vsplit X) (vsplit Y) (vsplit Z) (τ h q) (τ h q')`, where `τ h : Fin r₂ × Fin 2 ≃ Fin 2 × (Fin r × Fin 2)` is `q ↦ (((gE h).symm q.1).1, (((gE h).symm q.1).2, q.2))` (state `τ` as a definition or inline; it is an equivalence).
- **(S2)** `MAgree (Y - X) ((2 : ℤ_[2]) • Z) → MAgree (vsplit Y - vsplit X) ((2 : ℤ_[2]) • vsplit Z)`.
- **(S3)** For `X'' Y'' W'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])`, with `h2 : r₂ * 2 = 2 * (r * 2)`:
  `relab (fun q q' => glueM X'' Y'' W'' (τ h q) (τ h q')) = glueC h2 (relab X'') (relab Y'') (relab W'')`.
  (An identity of indices: for `j : Fin (r₂ * 2)`, `(splitIso r₂).symm j = (j / 2, j % 2)`, `(gE h).symm (j / 2) = ((j / 2) / r, (j / 2) % r)`, `(gE h2).symm j = (j / (2r), j % (2r))`, and `(splitIso r).symm (j % (2r)) = ((j % (2r)) / 2, j % 2)`; the two sides agree since `j / (2r) = (j / 2) / r` and `(j % (2r)) / 2 = (j / 2) % r`.)
- **(S4)** `Dance.slots ds r₂ = 2 * Dance.slots ds r` for every `ds` (from `Dance.slots_eq`).

## Part D — the dance of a glued system

- **(D1)** `PairRel ds r X Y Xk Yk → DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧ MCong 1 Yk Xk`.
- **(D2) Lemma 10.19.** For every `ds : List Bool`, `r r₂ : ℕ`, `h : r₂ = 2 * r`, `X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])`, `Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])` with `PairRel ds r X Y Xk Yk`, and every `Z` with `MAgree (Y - X) ((2 : ℤ_[2]) • Z)`: there is `Zk` with `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)` and
  `DanceRel ds r₂ (glueC h X Y Z) (glueC (S4 ds h) Xk Yk Zk)`
  (with `S4 ds h : Dance.slots ds r₂ = 2 * Dance.slots ds r`).
- **(D3) The final matrix.** For `h : r₂ = 2 * r`, `Xk Yk Zk : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` with `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)`, and all `g g' : Fin 2`, `s s' : Fin r`:
  `finalM (glueC h Xk Yk Zk) (gE h (g, s)) (gE h (g', s')) = if g = 0 ∧ g' = 0 then finalM Xk s s' else if g = 1 ∧ g' = 0 then finalM Zk s s' else if g = 1 ∧ g' = 1 then finalM Yk s s' else 0`,
  and `2 * finalM Zk s s' = finalM Yk s s' - finalM Xk s s'`.

## Proof sketch

- (B1)–(B3): entry by entry on `Fin 2 × n` (`fin_cases` on the glue indices; `Matrix.mul_apply` with `Fintype.sum_prod_type`); `tw10 0 = 0` and the like for (B2). (B4): coefficientwise, `(2 : ℤ_[2]) ≠ 0` in a domain (as C49b (K5)).
- (G2): let `Q_X`, `Q_Y` be the inverses of `twP X`, `twP Y` given by the two clean moves. Take `Q := glueM Q_X Q_Y (−(Q_Y * twP Z * Q_X))`. By (B1), `twP (glueM X Y Z) * Q = glueM (P_X Q_X) (P_Y Q_Y) (P_Z Q_X − P_Y Q_Y P_Z Q_X)`, which agrees with `glueM 1 1 0 = 1` (`MAgree.mul` with `P_Y Q_Y ≈ 1`). Likewise `Q * twP (glueM X Y Z)` has lower-left block `−Q_Y P_Z Q_X P_X + Q_Y P_Z`, which agrees with `0`. The Schur complement `twD − twB Q twC` is `glueM S_X S_Y L` by (B1)–(B2), with `S_X ≈ 2X'`, `S_Y ≈ 2Y'` and
  `L = D_Z − (B_Z Q_X C_X − B_Y Q_Y P_Z Q_X C_X + B_Y Q_Y C_Z)`.
  From `2Z ≈ Y − X` and (B2), `2B_Z ≈ B_Y − B_X`, `2C_Z ≈ C_Y − C_X`, `2D_Z ≈ D_Y − D_X`, `2P_Z ≈ P_Y − P_X`. So `2L ≈ (D_Y − D_X) − (B_Y − B_X) Q_X C_X + B_Y Q_Y (P_Y − P_X) Q_X C_X − B_Y Q_Y (C_Y − C_X)`. With `Q_Y P_Y ≈ 1` and `P_X Q_X ≈ 1` this telescopes to `S_Y − S_X ≈ 2(Y' − X') ≈ 4W`, so `L ≈ 2W` by (B4). Hence `glueM S_X S_Y L ≈ 2 • glueM X' Y' W` by (B1), (B3).
- (S1), (S3): entry by entry; `vsplit` is entrywise and `vplus 0 = 0`, `vprime 0 = 0`. (S3) is the index identity written in the statement (`Fin.ext`, `finProdFinEquiv`, `Nat.div_div_eq_div_mul`, `Nat.mod_mul_right_div_self`, `omega`). (S2): `vplus`, `vprime` are additive and commute with `•` (coefficientwise), and `MAgree.vsplit`.
- (D2): by induction on `ds`, generalizing `r r₂ h X Y Z`.
  - `[]`: `Zk := Z`; the agreements by (B3).
  - `false :: rest`: `MCong 1 Y' X'` (the next level of `PairRel`) gives `W`; (G2) gives `CleanStep (glueC h X Y Z) (glueC h X' Y' W)` after transport along `gE h` (`Cleanliness.L1`); then the induction hypothesis.
  - `true :: rest`: (S1), (S2), then (G2) on `Fin 2 × (Fin r × Fin 2)` with `W''` from `MCong 1 (relab Y'') (relab X'')` read back through `relab` (or from `MCong 1 Y'' X''` directly; both are the same entries), `Cleanliness.L1` along `τ h`, (S3) with `r₂ * 2 = 2 * (r * 2)`, and the induction hypothesis at `(r * 2, r₂ * 2)`.

  Keep `r₂` general in the induction, so that no cast between `Fin ((2 * r) * 2)` and `Fin (2 * (r * 2))` is needed. The final index types are related by (S4).
- (D1): by induction on `ds`. (D3): `finalM` is the coefficient `(0, 0)`, and `MAgree` at `m = 0`, `f = 0`.

## Checks before formalization

`chkC50.py` (md5 `bfe9b221de4dcdfb8a839cfc8615c328`; exact rationals; random integer `3 × 3` and `4 × 4` matrices as a noncommutative ring standing in for `Bf ℤ_[2]`; inverses exact, with odd determinants, so they are `2`-adic integers).
- **(B1):** the product, sum and identity rules of `glueM` (block matrices).
- **(G2):** pivots `P_X = I + 2A`, `P_Y = P_X + 2p`, and `B, C, D` with `Y = X + 2·(…)` blockwise. Then:
  - `glue(Q_X, Q_Y, −Q_Y P_Z Q_X)` is a two-sided inverse of `glue(P_X, P_Y, P_Z)`;
  - the lower-left block `L` of the glued Schur complement satisfies `2L = S_Y − S_X` exactly;
  - when `S_X = 2X'`, `S_Y = 2Y'` and `Y' − X' = 2W`, then `L = 2W`.
- **(S3):** the index identity for every `r = 1…6` and every `j < 4r`.
- **(S4):** `slots ds (2r) = 2 · slots ds r` for every `ds` of length `≤ 6` and `r ≤ 4`.

Result: 4 114 checks, 0 failures (`logs/chkC50.log`). Controls, four of four fire:
- the sign `+Q_Y P_Z Q_X` breaks the inverse (400 of 400 cases);
- `2L ≠ S_Y − S_X` when `B_Z` is perturbed by `I` (400 of 400);
- `L ≠ 2W` when `Y' − X' = 2W + I` (400 of 400);
- the glue index as the bottom digit breaks (S3) (5 of 5 sizes `r = 2…6`).
