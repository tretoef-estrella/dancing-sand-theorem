# C50f — the glued system on `T(l)`: the even families as glued dances (paper v8 §10.7)

*Lean piece C50f of the Dancing Sand Theorem. Grepy Escribano, 10 October 2026. Folder `RequestProject/GlueEven/`, namespace `GlueEven`. Do not change any earlier file.*

Paper v8, proof of Theorem 10.22. Lemma 10.5 presents both sides of an even family as glued operators on `T(l) ⊕ T(l)`:
- **the fold side:** `X̄(2l + 2, i) ≅ coker glue(Ψ_{i+1}, Ψ_i)`, where `glue(X, Y) = [[X, 0], [(Y − X)/2, Y]]`. In Lean this is C39 `FoldHalf.A4_even`, with `glueOp (Psi (l+i+1)) (Psi (l+i)) (Zop (l+i))`.
- **the cube side:** `2X(2l + 2, i) ≅ coker glue(U, U′)`, with `U = Ψ_{i+1}(Ψ_{i+1} − 2)/2` and `U′ = Ψ_i(Ψ_i + 2)/2`. In Lean this is C39b `FoldCube.V6`, with `glueOp (thX − thY) (thX + thY) thY`.

The paper then applies Proposition 10.7 to the glued systems (Lemma 10.19: the glue commutes with the dance).

This piece does exactly that, over `ℤ_[2]`, and stops before the comparison of the two final matrices. That comparison (C50e, transported to `ℚ_[2]`) is the next piece, C50g.

Three facts are needed.
1. **A glued system of size 2 acts as `glueOp`.** For `1 × 1` systems `x, y, z`, the size-2 system `GlueDance.glueC h (x) (y) (z)` (with `h : 2 = 2 * 1`) acts on `Fin 2 → T` as `[[act x, 0], [act z, act y]]`. That is `FoldHalf.glueOp (act x) (act y) (act z)` after `v ↦ (v 0, v 1)`. This follows from the definition of `sysAct` (a sum over the source slot) and of `glueM`.
2. **The arms are the operators of Lemma 10.5.**
   - C49 `FoldOdd.F4`: `act (PsiF j) = Psi (l + j)`.
   - The lower-left arm `ZF i := −1 − (−1)^i·ShInvF` satisfies `2·ZF i = PsiF i − PsiF (i+1)` (C50c `A1`: `KF (i+1) − KF i = 2(−1)^i ShInvF`). It acts as `Zop (l + i) = −1 − parOp (l+i)·ShInv`, by C49 `parOp_T` and `F3`.
   - On the cube side, `2U = PsiF(i+1)(PsiF(i+1) − 2)` gives `2·act U = (Psi(d+1) − 2)·Psi(d+1)`, with `d = l + i` (C40 `act_mul`). By C39b `V3c`, `2·act U = 2(thX − thY)`. There is no 2-torsion, so `act U = thX − thY`. Likewise `act U′ = thX + thY`, and `act ZU = thY` when `U′ − U = 2·ZU`.
3. **The glued Proposition 10.7.** If two `1 × 1` systems dance congruently (C50 `PairRel`), C50 `D2` gives the dance of the glued system, and C40d `Q1` with `r = 2` gives its cokernel.

## Setting (reuse; do not redefine)

- C13 `Dance.slots`, `Dance.mCount`; C29 `Filt.T`; C32 `Families.ds`.
- C40 `FormalOps.Bf`, `FormalOps.act`, `act_add`, `act_sub`, `act_smul`, `act_mul`, `act_one`; C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`; C40c `FormalAct.sysAct`, `FormalAct.A1`; C40d `FormalProp.Q1`.
- C39 `FoldHalf.Psi`, `FoldHalf.Zop`, `FoldHalf.glueOp` (`glueOp_apply`), `FoldHalf.parOp`, `FoldHalf.ShInv`, `FoldHalf.A3`, `FoldHalf.A4_even`.
- C39b `FoldCube.thX`, `FoldCube.thY`, `FoldCube.V3c`, `FoldCube.V6`.
- C49 `FoldOdd.PsiF`, `FoldOdd.KF`, `FoldOdd.ShInvF`, `FoldOdd.F3`, `FoldOdd.F4`, `FoldOdd.parOp_T`, `FoldOdd.act_sub'`.
- C50 `GlueDance.glueC`, `glueM`, `gE`, `PairRel`, `S4`, `D2`, `D3`.
- C47 `RingK.covSys`; C48 `Cleanliness.Good`; C50b `DanceMod2.Cong2`, `D1`, `D3`; C50c `ArmsEven.A1`, `E1`, `E2`, `GPsi`, `uSys`.

Throughout:
- `A := ℤ_[2]`;
- `T := Filt.T ℤ_[2] l`, with `W := (l : ℤ)` and `BN := l + 1`;
- `ds := Families.ds l`, `k := ds.length`;
- `h21 : (2 : ℕ) = 2 * 1` (by `norm_num`).

## Definitions (new)

- `ZF (i : ℕ) : Bf ℤ_[2] := -(1 : Bf ℤ_[2]) - ((-1 : ℤ_[2]) ^ i) • FoldOdd.ShInvF`.
- `pairE (V : Type*) [AddCommGroup V] [Module ℤ_[2] V] : (Fin 2 → V) ≃ₗ[ℤ_[2]] V × V`, with `pairE V v = (v 0, v 1)` (Mathlib's `LinearEquiv.piFinTwo` or by hand).
- `abbrev PF (l r h : ℕ) : Type` is the factor of C40d `Q1`:
  `(a : Fin (Families.ds l).length) → (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]) ⧸ (2 : ℤ_[2]) ^ (h + (a : ℕ)) • (⊤ : Submodule ℤ_[2] (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]))`.
  It must be an `abbrev`, or a `def` with its `AddCommGroup` and `Module ℤ_[2]` instances, so that `≃ₗ` makes sense.

## Part S — a glued system of size 2 is `glueOp`

- **(S1)** For `N : DPLattice ℤ_[2]`, `W : ℤ`, `B : ℕ`, `x y z : Bf ℤ_[2]` and `v : Fin 2 → N.ι → ℤ_[2]`:
  `pairE _ (FormalAct.sysAct N W B (GlueDance.glueC h21 (fun _ _ => x) (fun _ _ => y) (fun _ _ => z)) v) = FoldHalf.glueOp (act N W B x) (act N W B y) (act N W B z) (pairE _ v)`.
- **(S2)** For every `h : ℕ`, the quotient of `Fin 2 → N.ι → ℤ_[2]` by the range of `(2 : ℤ_[2]) ^ h • sysAct N W B (glueC h21 …)` is linearly equivalent to the quotient of `(N.ι → ℤ_[2]) × (N.ι → ℤ_[2])` by the range of `(2 : ℤ_[2]) ^ h • FoldHalf.glueOp (act N W B x) (act N W B y) (act N W B z)`. State it as `Nonempty (… ≃ₗ[ℤ_[2]] …)`.

## Part O — the arms on `T(l)`

Let `l i B : ℕ` with `l + 1 ≤ B`.

- **(O1) The lower-left arm of the fold side.**
  - `(2 : ℤ_[2]) • ZF i = FoldOdd.PsiF i - FoldOdd.PsiF (i + 1)`;
  - `act (Filt.T ℤ_[2] l) (l : ℤ) B (ZF i) = FoldHalf.Zop (Filt.T ℤ_[2] l) ((l : ℤ) + i) (l + 1)`.
- **(O2) The cube side.** Let `U U' ZU : Bf ℤ_[2]` with
  `(2 : ℤ_[2]) • U = FoldOdd.PsiF (i + 1) * (FoldOdd.PsiF (i + 1) - (2 : ℤ_[2]) • 1)`,
  `(2 : ℤ_[2]) • U' = FoldOdd.PsiF i * (FoldOdd.PsiF i + (2 : ℤ_[2]) • 1)`, and
  `Agree (U' - U) ((2 : ℤ_[2]) • ZU)`.
  Write `thX := FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2)` and `thY` likewise. Then:
  - `act (Filt.T ℤ_[2] l) (l : ℤ) B U = thX - thY`;
  - `act (Filt.T ℤ_[2] l) (l : ℤ) B U' = thX + thY`;
  - `act (Filt.T ℤ_[2] l) (l : ℤ) B ZU = thY`.

## Part Q — the glued Proposition 10.7

Let `l B h : ℕ` with `l + 1 ≤ B`.

- **(Q1) General.** Let `X Y Z : Bf ℤ_[2]`, and let `Xk Yk` be matrices over `Bf ℤ_[2]` indexed by `Fin (Dance.slots (Families.ds l) 1)`, with
  `GlueDance.PairRel (Families.ds l) 1 (fun _ _ => X) (fun _ _ => Y) Xk Yk` and `Agree (Y - X) ((2 : ℤ_[2]) • Z)`.
  Then there is `Zk` with `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)` such that
  `Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h • FoldHalf.glueOp (act T W B X) (act T W B Y) (act T W B Z)) ≃ₗ[ℤ_[2]] PF l 2 h × ((Fin (Dance.slots (Families.ds l) 2) → ℤ_[2]) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ (h + (Families.ds l).length) • Matrix.mulVecLin (finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk)))))`.
- **(Q2) The fold side.** For every `i`, there are `Xk Yk Zk` with:
  - `GlueDance.PairRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF (i + 1)) (fun _ _ => FoldOdd.PsiF i) Xk Yk`;
  - `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)`;
  - `Nonempty (… ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h • FoldHalf.glueOp (FoldHalf.Psi (Filt.T ℤ_[2] l) (l + i + 1) (l + 1)) (FoldHalf.Psi (Filt.T ℤ_[2] l) (l + i) (l + 1)) (FoldHalf.Zop (Filt.T ℤ_[2] l) (l + i) (l + 1))) ≃ₗ[ℤ_[2]] PF l 2 h × (… finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk) …))`, with the same right side as (Q1).

  (The three operators are written exactly as `FoldHalf.A4_even` writes them, so that C50g can rewrite with it; their second argument is the integer `l + i + 1` or `l + i`, with `l i` cast to `ℤ`.)
- **(Q3) The cube side.** Let `U U' ZU` be as in (O2), and let `Uk U'k` satisfy `GlueDance.PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k`. Then there is `Zk` with `MAgree (U'k - Uk) ((2 : ℤ_[2]) • Zk)` and
  `Nonempty (… ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h • FoldHalf.glueOp (thX - thY) (thX + thY) thY) ≃ₗ[ℤ_[2]] PF l 2 h × (… finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Uk U'k Zk) …))`
  (`thX`, `thY` as in (O2), written out; the arguments exactly as in `FoldCube.V6`).
- **(Q4) The cube-side arms exist.** For every `l i` there are `U U' ZU : Bf ℤ_[2]` and `Uk U'k` with:
  - the two equations of (O2);
  - `Agree (U' - U) ((2 : ℤ_[2]) • ZU)`;
  - `GlueDance.PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k`.

  From C50c `E2` (with `ds := Families.ds l`): take `U := covSys ∅ 0 c U₀ e∅ e∅` and `U' := covSys ∅ 0 c U₀' e∅ e∅`, with `c := (((i + 1) / 2 : ℕ) : ℤ_[2])` and `e∅ := ⟨∅, Finset.empty_subset _⟩`. The two equations are those of `E2`. `ZU` exists because `PairRel`'s head gives `ContZero.MCong 1 U' U`: halve each coefficient, as in C50b `D3`.

  So that C50g can transport `U` to `ℚ_[2]`, (Q4) also returns `U₀ U₀' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]` with `Cleanliness.Good U₀`, `Cleanliness.Good U₀'`, `DanceMod2.Cong2 U₀ U₀'`, `U = RingK.covSys ∅ 0 c U₀ e∅ e∅` and `U' = RingK.covSys ∅ 0 c U₀' e∅ e∅` (the data of `E2`).

## Proof sketch

- **(S1)**: unfold `sysAct` (`toFun v s = Σ s', act (G s s') (v s')`), `glueC`, `glueM`, `gE` at `r = 1` (`gE h21 (g, 0) = g`), and `glueOp_apply`. Then `Fin.sum_univ_two`, and case on `s : Fin 2`. Two coordinates:
  - coordinate `0`: `act x (v 0) + act 0 (v 1) = act x (v 0)` (`act` of `0` is `0`, by `act_add`);
  - coordinate `1`: `act z (v 0) + act y (v 1)`.
- **(S2)**: (S1) gives a conjugation by `pairE`. Use `Submodule.Quotient.equiv` with `LinearEquiv.map` of the range: the range of `pairE ∘ F ∘ pairE⁻¹` is the image of the range of `F`. The scalar `2^h` commutes with `pairE`.
- **(O1)**:
  - The first identity: `PsiF j = dg(4f + 2j) + KF j`. `dg(4f + 2i) − dg(4f + 2i + 2) = −2·1` (coefficientwise), and `KF i − KF (i+1) = −2(−1)^i ShInvF` (C50c `A1`'s key step, `ArmsEven.kJ_succ_sub` or directly from `FoldOdd.KF`).
  - The second identity: `act_sub`, `act_one`, `act_smul`, then C49 `F3` (`act ShInvF = FoldHalf.ShInv`) and `parOp_T` (`parOp (l + i) = (−1)^i • 1`).
- **(O2)**:
  - `act` of `2 • U` is `2 • act U` (`act_smul`).
  - `act` of the product is the product of the acts (`act_mul` with `hnil := (FoldHalf.A3 ℤ_[2] l).2`, `BN = l + 1 ≤ B`). `act PsiF j = Psi (l + j)` by `FoldOdd.F4`.
  - So `2 • act U = (Psi(d+1)) * (Psi(d+1) − 2)`, which equals `(Psi(d+1) − 2) * Psi(d+1)` (the two factors commute: `Psi * (Psi − 2) − (Psi − 2) * Psi = 0` by `mul_sub`, `sub_mul`). By `FoldCube.V3c` (with `N = T`, `BN = l + 1`, `d = l + i`, `B = 2l + 2`, `hnil`, `2(l+1) ≤ 2l + 2`) this is `2 • (thX − thY)`.
  - Cancel `2`: `Module.End ℤ_[2] (T.ι → ℤ_[2])` has no 2-torsion (`smul_right_injective` with `two_ne_zero`, or extensionality and `mul_left_cancel₀` in `ℤ_[2]`).
  - `U'` is the same, with the `+` part of `V3c`.
  - `ZU`: `2 • act ZU = act (2 • ZU) = act (U' − U) = 2 • thY`, where the middle equality transports the `Agree` along `FormalAct.A1` (as in the proof of C50d `N0`), or along the floor bound of `act`. Then cancel `2`.
- **(Q1)**:
  - C50 `D2` (with `r = 1`, `r₂ = 2`, `h = h21`, `hZ` from the `Agree`, as `MAgree` of constant `1 × 1` matrices) gives `Zk` and `DanceRel (Families.ds l) 2 (glueC h21 …) (glueC (S4 …) Xk Yk Zk)`.
  - C40d `Q1` with `r = 2` gives the cokernel of `2^h • sysAct` of the glued system. Its first factor is `PF l 2 h`.
  - (S2) moves it to `glueOp`.
- **(Q2)**: C50c `E2` (`ds := Families.ds l`) gives `PairRel … (PsiF (i+1)) (PsiF i) Xk Yk`. (O1) gives `Agree (PsiF i − PsiF (i+1)) (2 • ZF i)` (equality). Apply (Q1) with `Z := ZF i`, then rewrite the three acts by `FoldOdd.F4` and (O1). Mind the cast `((l + i + 1 : ℕ) : ℤ) = (l : ℤ) + (i + 1 : ℕ)` (`push_cast`).
- **(Q3)**: (Q1) with `X := U`, `Y := U'`, `Z := ZU`, then (O2).
- **(Q4)**: C50c `E2`, then halve `U' − U` coefficientwise using the head of `PairRel` (`MCong 1`, C49b), or C50b `D3`.

## Checks done before sending

- **Brute force `chkC50f.py`.** It uses the lattice model of `chkC49.py`: `T(l)` from `chk_lattice_lib`, with exact rationals. The `2`-adic Smith form treats odd denominators as units of `ℤ_2`.
  - The cases: every `l ≤ 6`, `i = 0..6`, `B = l + 1` and `l + 3`.
  - (O1): `act ZF i = Zop(l + i)` on `T(l)`, and `2·ZF i = PsiF i − PsiF(i+1)` coefficientwise.
  - (O2):
    - the matrices `U = (Ψ_{i+1} − 2)Ψ_{i+1}/2`, `U′ = Ψ_i(Ψ_i + 2)/2` and `(U′ − U)/2` are `2`-integral;
    - `act` of the formal products `(1/2)·PsiF(i+1)(PsiF(i+1) − 2)` and `(1/2)·PsiF i(PsiF i + 2)` equals them;
    - the two factors commute.
  - **Theorem 10.22, numerically** (the target of C50g): the `2`-adic Smith form of `glue(Ψ_{i+1}, Ψ_i, Zop)` equals that of `glue(U, U′, (U′ − U)/2)`, for every `l ≤ 6` and `1 ≤ i ≤ 6`. Both Smith forms are defined, never `None`. At `i = 0`, which is not claimed here (C50h), they are equal too, 7 of 7.
  - **750 checks, 0 failures.** Log `logs/chkC50f.log`.
- **Controls (all four fire):**
  - `ZF` with the wrong sign: it does not act as `Zop` (98 cells).
  - `Zop` at `d + 1`: different (98).
  - The glue with `Z = 0`: a different Smith form (21).
  - The cube side built with the wrong arm (`Ψ_{i+2}` for `Ψ_{i+1}`): a different Smith form (14; integral in every cell).
- **Two errors of mine in the first runs, both in the test.**
  - My integrality test asked for denominator `1`. The model's coefficients are `1/(2s − 1)!!`, with odd denominators, which are units of `ℤ_2`. I replaced it by `v_2 ≥ 0`, and I added a check that every Smith form is defined.
  - One control («`U` with `+2` for `−2`») cannot fire. `Ψ(Ψ + 2)/2` and `Ψ(Ψ − 2)/2` differ by `2Ψ`, so they are congruent modulo `2`, and the same theory gives them the same group. That control negated nothing false. It is replaced by the wrong arm.

## Notes

- After this piece:
  - **C50g** proves Theorem 10.22 for `i ≥ 1`:
    - transport the two glued dances to `ℚ_[2]` (as C46 did for one arm), where C50c `P1` identifies the arms with `PathSum.XiOp 2 c η ζ` (`c ≥ 1` for `i ≥ 1`);
    - apply C50e `W4` to each arm, and C50 `D3` with C50e `G4` to the glued final matrices;
    - `glue(W₋, W₊)` is in `GL(ℤ_2)` (C50e `G3`, `G5`, `W3`), so the two final matrices are associates and have isomorphic cokernels;
    - the factors `PF l 2 h` are the same on both sides;
    - `FoldHalf.A4_even` and `FoldCube.V6` close it.
  - **C50h** proves `i = 0`, by congruences, as C49b did.
- (S1) and (S2) are stated for every `DPLattice` and every `W`, `B`; only Part O uses `T(l)`.
