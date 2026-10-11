# Summary of changes for run 8ef876e1-06ab-4b07-9cf6-20a67c8885be
I formalized and proved all 11 statements of Parts G, Z, V, R and C of `C49c_smith_form_and_cokernel_at_zero.md`: (G1), (G2), (Z3), (V4)–(V7), (R6), (R7), (C4) and (C5). They are in a new folder, `RequestProject/ZeroSmith/`, namespace `ZeroSmith`. `lake build RequestProject.ZeroSmith.All` succeeds with no errors or warnings. The folder has no `sorry`, no axioms and no `native_decide`, and `#print axioms` on all 11 theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The change is seven new files (`Defs`, `PartG`, `PartZ`, `PartV`, `PartR`, `PartC`, `All`). No existing file was changed, and the work is committed.

**Definitions.** Nothing the Setting lists as reused is redefined. The only new definition is `Data0`, in `Defs.lean`. The other new declarations are lemmas used in the proofs, each with a docstring naming the item it serves (for example `ZG_floor`, `ZG_ceil`, `ZG_main`, `Z3_sum`, `Z3_core`, `Z3_fin`, `coker_equiv_of_submatrix`, `coker_act_XiOpZ_all`).

**Where each item is** (each theorem's docstring names its item):
- **(G1), (G2):** `PartG.lean`. (G1) re-runs C15's `Z_floor`, `Z_ceil` and `Z_main` for any matrix `M'` that satisfies `Data0`, then transfers back along `slPerm`, as in the sketch.
- **(Z3):** `PartZ.lean`, following the sketch's block elimination. It works in blocks `Fin m ⊕ Fin 1` with Mathlib's `fromBlocks`, moved to `Fin (m + 1)` along `finSumFinEquiv`. Writing `Z = Dl · Y`, a column operation gives a lower-right corner `s`, and `s = 0` because `det X = 0`. A row operation then clears the bottom-left block; it has integer entries because `E j < N`.
- **(V4)–(V7):** `PartV.lean`. (V4) uses C49b (V1), (G2) and C46 `Z0`. (V5) combines (V4), (G1), (Z3) and C49b (V3). (V6) is C15 (Z3) mapped to `ℤ_[2]`. (V7) uses C46 (Z2) when `Ids ds ≠ ∅`; when `Ids ds = ∅`, both matrices are zero (C15 (Z1) and C49b (V2)). The matrix `X` is written out as `(finalM GkZ).submatrix cs cs` with `cs = Fin.cast (Smith2.slots_cast (Families.ds l))`.
- **(R6), (R7):** `PartR.lean`. (R6) combines C48b (T3), C40d (Q1), (V7) and C16 `X_equiv_coker`. (R7) splits into three cases: C48b (R2) for `c ≥ 1`, C48b (R0) for `c = 0, l = 0`, and (R6) for `c = 0, l ≥ 1`.
- **(C4), (C5):** `PartC.lean`. (C4) follows C49 (C1), with (R7) in place of its hypothesis; (C5) is C39 `A4_odd`, then (C4), then C39b `O5_X` read backwards.

**Hypotheses.** No statement needed a hypothesis the file does not give, and none was added. Three points about the written form:
- **`Data0` binders:** the file writes `∀ s s'` without types. Because `Dset` takes a natural number, Lean would read `s, s'` as naturals and `M' s s'` would not type-check, so the binders are typed `Fin (2 ^ Dance.mCount ds)`.
- **(G1):** the hypothesis `1 ≤ ds.length` is not used by the proof. It is kept as written, named `_hk`, and the docstring says so.
- **(C4):** each quotient is parenthesised, as the file asks.

`All.lean` imports every part and lists where each item is. The Properties table has 11 property rows, all marked proved, and one definition row for `Data0`.

# Summary of changes for run c6cd8d5a-2486-4e93-ae4a-88b5914ecd14
I formalized and proved all 15 statements of Parts K, T, C and V of `C49b_congruence_and_the_data_at_zero.md`: (K1)–(K6), (T1)–(T3), (C1)–(C3) and (V1)–(V3). They are in a new folder, `RequestProject/ContZero/`, namespace `ContZero`. `lake build RequestProject.ContZero.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on all 15 theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The change is six new files (`Defs`, `PartK`, `PartT`, `PartC`, `PartV`, `All`); no existing file was changed, and the work is committed.

**Definitions.** Nothing the Setting lists as reused is redefined. `Defs.lean` adds only `Cong` and `MCong`, written exactly as in the file. The other new declarations are small proof helpers, each with a docstring naming the item it serves (for example `mcong_iff`, `Cong.sum`, `eq_zero_of_forall_pow_mul`, `mfin_eq_finalMatrix`, `int_dvd_of_eq_pow_mul`). None of them is a new concept.

**Where each item is** (each theorem's docstring names its item):
- **(K1)–(K6):** `PartK.lean`. (K1), (K2) and (K3) are each one theorem that is a conjunction of all the clauses in the file. They are also available as separate lemmas (`Cong.mul`, `MCong.vsplit`, `MCong.reindex`, …).
- **(T1)–(T3):** `PartT.lean`. (T1) is proved by induction on `ds`, as in the sketch. (T3) uses (T1) and (T2): the difference is divisible by every power of 2, so it is 0.
- **(C1)–(C3):** `PartC.lean`. (C3) combines C40b `L4_sigma`, (C2), (T1), (T2) and C14 `finalMatrix_eq_map`. Divisibility in `ℤ` then comes from Mathlib's `PadicInt.norm_int_le_pow_iff_dvd`.
- **(V1)–(V3):** `PartV.lean`. (V1) compares the dance at `c = 0` with the dance at `c = 2^(N+k)`, where `k` is the length of `ds`, using C48b (T3), (C1), (T1), (T2), (C3), C46 (V1) and `theorem_D_ii`. This gives \(|\|a\| - \|b\|| \le 2\cdot 2^{-N}\) for every `N`; the triangle inequality is enough here, so the ultrametric step of the sketch isn't needed. (V3) is a conjunction: the row is zero, and the determinant is zero.

**Hypotheses.** No statement needed a hypothesis the file does not give, and no statement was changed. Points worth knowing:
- **(K4):** the proof only uses `MAgree (Q * P) 1` and `MAgree (P' * Q') 1`. The other two hypotheses are kept, as you asked. They are named `_h1` and `_h4` so the build has no unused-variable warnings, and the docstring says so.
- **Part V:** `cs` is written out as `Fin.cast (Smith2.slots_cast (Families.ds l))`, and the matrix `X` of (V3) as `fun s s' => finalM GkZ (cs s) (cs s')`.
- C44 `Stability.length_ds_pos` is never used, because the proof of (V1) does not need `k ≥ 1`.

`All.lean` imports every part and lists where each item is. The Properties table has 15 property rows, all marked proved, and one row for the two new definitions.

# Summary of changes for run 1810c6c2-dca6-4bbb-ace4-bae9edeb3fb3
I formalized and proved all nine statements of Parts F and C of `C49_the_fold_law_on_the_odd_families.md`: (F1)–(F6), (C1), (C2) and (C3). They are in a new folder, `RequestProject/FoldOdd/`, namespace `FoldOdd`. `lake build RequestProject.FoldOdd.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`, and `#print axioms` on all nine theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The change is five new files (`Defs`, `PartF`, `PartF4`, `PartC`, `All`); no existing file was changed, and the work is committed.

**Definitions.** Nothing the Setting lists as reused is redefined. `Defs.lean` adds only the file's new definitions: `cst`, `chC`, `shC`, `shInvC`, `ChF`, `ShF`, `ShInvF`, `KF`, `kJ`, `PsiF` and `SigF`. `shInvC` is defined by strong recursion, and its two equations from the file are proved as lemmas (`shInvC_zero`, `shInvC_eq`), which the file allows.

**Where each item is** (each theorem's docstring names its item):
- **(F1), (F2), (F3), (F5), (F6):** in `PartF.lean`.
- **(F4):** in `PartF4.lean`.
- **(C1), (C2), (C3):** in `PartC.lean`.

The equalities of (F1)–(F5) are stated and proved as equalities: in `Bf A` for (F1), (F2) and (F5), and between operators for (F3) and (F4). The proofs follow the file's sketch:
- (F3) identifies `act ShInvF` with `Ring.inverse Sh` by showing it is a two-sided inverse of `Sh`.
- (F4) uses C39 (A3) for (nil) and C39b (O4) for the weights.
- (F5) is proved coefficient by coefficient. The value `kJ j 1` uses `3 * dfi 2 = 1`.
- (C1) combines (F4), (F5) and (F6) with C48b (R2) when `j ≥ 1` and C48b (R0) when `l = 0`.
- (C2) and (C3) compose C39 (A4_odd), (C1) and C39b (O5_X) read backwards.

**Hypotheses.** No statement needed a hypothesis the file does not give, and none was added. The only change in form is in (C1): written exactly as in the file, Lean groups `… ⧸ range Psi … ≃ₗ[ℤ_[2]] … ⧸ range SigmaOp …` differently from what the file means, so the statement does not type-check. I added parentheses around each quotient so it reads as intended. This is noted in `All.lean`.

The files also contain a few small proof helpers, each with a docstring (for example `act_cst`, `coef_KF`, `kJ_one`, `flD_T`, `parOp_T`, `coker_act_XiOpZ`); none of them is a new definition. `All.lean` imports every part and lists where each item is. The Properties table has nine property rows, all marked proved, and one row for the new definitions.

# Summary of changes for run a5c4d914-ab58-42ef-b900-95990f4a43bd
I formalized and proved all six statements of Parts T and R of `C48b_the_dance_of_Xi_is_clean.md` — (T1), (T2), (T3), (R0), (R1), (R2) — in a new folder, `RequestProject/DanceXi/`, namespace `DanceXi`. `lake build RequestProject.DanceXi.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`, and `#print axioms` on the six theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The change is three new files (`PartT.lean`, `PartR.lean`, `All.lean`); no existing file was changed, and the work is committed.

**Reuse.** Nothing the Setting lists as reused is redefined. The only new declarations are small proof helpers:
- `finOneDnEmpty`: the unique equivalence `Fin 1 ≃ Dn ∅`;
- `quotSmulEquiv`: a linear equivalence gives isomorphic cokernels for multiplication by the same scalar;
- `mulVecLin_finalM_XiOpZ`, `sigma_nil`, `finOneSysTNil`.

**Where each item is** (each theorem's docstring names its item):
- **(T1)** `DanceXi.T1`. It is stated as an equality of matrices and holds by definition (`rfl`).
- **(T2)** `DanceXi.T2`, by induction on `ds`, following the proof sketch. It uses C48's (W5), (V3) and (L1), together with (T1). In the split step the new equivalence `Fin (r * 2) ≃ Dn (insert h P)` is built from `(Dance.splitIso r).symm`, `ofLex`, `e × id` and `splitDn`.
- **(T3)** `DanceXi.T3`: (T2) with `r = 1`, `h = 0`, `P = ∅` and `Γ = G0 α η z`, using (O1) and (O2).
- **(R0)** `DanceXi.R0`. `Q2_zero` turns the cokernel into that of multiplication by \(2^\alpha c\) on `Fin 1 → ℤ_[2]`. For `1 ≤ α`, `Dance.sigma ℤ_[2] [] α c` is also multiplication by \(2^\alpha c\), on a module free of rank one, so the two cokernels are isomorphic.
- **(R1)** `DanceXi.R1`: (T3) with `ds := Families.ds l` gives the dance hypothesis of C46 (R5).
- **(R2)** `DanceXi.R2`: (R0) when `l = 0`, (R1) when `l ≥ 1`.

**Hypotheses.** No statement needed a hypothesis the file does not give, and every statement keeps exactly the hypotheses written in the file. "There is `Gk` with …" is written `∃ Gk, …`, and "the cokernel is isomorphic to …" is written `Nonempty (… ≃ₗ[ℤ_[2]] …)`.

`All.lean` imports both parts and lists where each item is. The Properties table has six property rows (T1–T3, R0–R2), all marked proved.

# Summary of changes for run 556eee6a-5a32-4253-aa5f-420ac991f089
I formalized and proved every statement of Parts W, V and O of `C48_cleanliness_one_move.md`: (W1)–(W5), (V0)–(V3), (L1), (O1) and (O2). They are in a new folder, `RequestProject/Cleanliness/`, namespace `Cleanliness`. `lake build RequestProject.Cleanliness.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`, and `#print axioms` on all 12 theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The change is 6 new files (`Defs`, `Inverse`, `PartW`, `PartV`, `PartO`, `All`); no existing file was changed, and everything is committed.

**Reuse.** Nothing the Setting lists as reused is redefined. The proofs use:
- C47 (`RingK`): `Kr`, `theta`, `RS`, `oS`, `Dn`, `covSys`, `thetaSys`, `prodFun`, and the results (K3)–(K6), (S1)–(S3), (S5), (R2), (T1)–(T3);
- C40 (`FormalOps`): `Bf` and the `tw`/`v` maps;
- C20: `Doubling.dfi`;
- C40b (`FormalDance`): `MAgree`, `twP`/`twC`/`twB`/`twD`, `vsplit`, `CleanStep`;
- C46: `Smith2.XiOpZ`.

**New definitions** (`Defs.lean`), written as in the file: `InK`, `PayA`, `CoefB`, `Good`, `GB`, `GC`, `GP`, `GD`, `vsplitG`, `splitDn` and `G0`. `GD` is defined by cases on the order (`0` and `q + 1`), and `splitDn` is a Lean equivalence (`Equiv`) with the inverse given in the file.

**Where each item is** (every theorem's docstring names its item)
- **(W1)–(W5)** are `W1`–`W5` in `PartW.lean`. `W1` combines `W1_B`, `W1_C`, `W1_P` and `W1_D`; these are equalities of matrices over `Bf ℤ_[2]`.
- **(W3):** all its equalities are equalities, of functions and of matrices.
  - `GQ` is the recursion from the proof sketch, on `Δ.card + m` (`rinv` in `Inverse.lean`).
  - `Q·P = 1` comes from a left inverse built by the mirror recursion (`linv`), as in the sketch.
- **(W4)** follows the sketch, using the Schur complement `GD Γ − (GB Γ · GQ) · GC h Γ`.
- **(W5)** proves the exact formula for `2 * Γ' ∅ 0 y`, divisibility by 8, and conditions (a) and (b) one level up.
- **(V0)–(V3) and (L1)** are in `PartV.lean`. (V1) is an equality, checked in all four blocks.
- **(O1) and (O2)** are in `PartO.lean`. (O2) is an equality in `Bf ℤ_[2]`.

**Hypotheses.** No statement needed a hypothesis that the file does not give, and none was changed. In (V2), the identity `vsplitG h Γ {h} 0 = Γ ∅ 1` is stated without `Good Γ`, because it does not need it.

`All.lean` imports every part and says where each item is. The Properties table has 12 property rows, all marked proved, and 4 definition rows covering the 11 new definitions.

# Summary of changes for run 19843fc1-c990-4603-a5b9-47beb6d1bbfa
I formalized and proved every statement of Parts K, S, R and T of `C47_the_ring_K_and_covariant_systems.md` in a new folder, `RequestProject/RingK/`, namespace `RingK`. `lake build RequestProject.RingK.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on all 19 theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The work is 6 new files (`Defs`, `PartK`, `PartS`, `PartR`, `PartT`, `All`); no existing file was changed, and everything is committed.

**Definitions** (`Defs.lean`). `KRep`, `KRep.eval`, `Kr`, `S`, `thetaRep`, `theta`, `RS` (with its unit and product), `oS`, `Dn`, `covSys`, `thetaSys` and `prodFun` are written as in the file. `Bf` is C40's `FormalOps.Bf`, reused, and `red` is `PadicInt.toZMod`.
- `RS` is a separate name for the type `Finset ℕ → ℕ → S`. Its addition is pointwise; its `1` and `*` are the ones from Definition 7.
- **Something to check:** Mathlib does not know that `S` is a commutative ring, because it is missing one instance: the fact that the left and right actions of `ZMod 2` on `PowerSeries (ZMod 2)` agree (`IsCentralScalar`). I added that instance, plus a direct `CommRing S` instance so it is found quickly.

**Where each item is** (every theorem's docstring names its item)
- **(K1)–(K6)** `K1`…`K6` in `PartK.lean`. `K3` combines `K3_const`, `K3_add`, `K3_sub`, `K3_mul`, `K3_smul` and `K3_pow_mul` (also `K3_neg`). The representations for sums, products, shifts and inverses are exactly the formulas in the file.
- **(S0)–(S5)** in `PartS.lean`. (S0) is split into `S0` and `S0_theta`; `S1` combines additivity, multiplicativity, `theta 1 = 1`, the constants and constant multiples.
- **(R1), (R2)** in `PartR.lean`. The ring structure is the instance `RS.instCommRing`. `R1` records commutativity, associativity and `(2 : RS) = 0`. `R2` is proved by pairing each term with its partner and using characteristic 2, with the central binomial coefficient \(\binom{2a}{a}\) even for \(a \ge 1\).
- **(T0)–(T3)** in `PartT.lean`. `T1` combines `T1_mul`, `T1_add`, `T1_smul` and `T1_one`, as equalities in `Matrix (Dn P) (Dn P) (Bf ℤ_[2])`. The unit system `Γ₁` is written inline as `fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0`.

**Hypotheses.** No statement needed a hypothesis the file does not give, and none was changed. Statements written "for `ϑ = r.eval`" are stated directly about `r.eval`.

**Build setting.** `PartR.lean` raises Lean's instance-search limit (`synthInstance.maxHeartbeats`), because the `ring` tactic needs more than the default to work in `S`.

`All.lean` imports every part and lists where each item is. The Properties table has 19 property rows (K1–K6, S0–S5, R1, R2, T0–T3), all marked proved, and 6 definition rows.

# Summary of changes for run d36e2d4f-9831-41bf-86b3-ed425f50b3af
I formalized and proved all 17 statements of `C46_smith_form_and_cokernel_over_Z2.md` (Parts M, Z, G, V and R) in a new folder, `RequestProject/Smith2/`, namespace `Smith2`. `lake build RequestProject.Smith2.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`, and `#print axioms` on all 17 theorems lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 7 new files (`Defs`, `PartM`, `PartZ`, `PartG`, `PartV`, `PartR`, `All`); no existing file was changed, and everything is committed.

**Definitions** (`Defs.lean`): only the three new ones, written as in the file: `Bf.map`, `XiOpZ` and `trunc`. Nothing listed as reused is redefined. The coercion \(\iota\) is Mathlib's `PadicInt.Coe.ringHom`, and `cs` is `Fin.cast (slots_cast ds)`, where `slots_cast` is a one-line lemma, not a definition.

**Where each part is**
- **(M1)–(M5)** in `PartM.lean`, as `M1`–`M5`. (M4) is proved by induction on the digit list.
- **(Z0)–(Z2)** in `PartZ.lean`. In (Z1), \(\det(1+2W)\) is shown to be a unit by reduction mod 2.
- **(G1), (G2)** in `PartG.lean`. (G1) re-runs the proof of C15 (S3) for any matrix `M'` with the stated support and entry valuations, using `DanceSmith.floor_minor`, `golden_ceiling` and `smith_of_bounds`, and transfers back along `slPerm`. (G2) follows from C15 (S1) and (P1).
- **(V1), (V2)** in `PartV.lean`. (V1) maps the dance to \(\mathbb{Q}_2\) with (M4) and (M5), then applies `Conjugation.T_eta` and `Windows.theorem_D_ii` / `theorem_D_iii`.
- **(R1)–(R5)** in `PartR.lean`. They use `FormalProp.Q1`, `FormalProp.Q3` and `FamilyGroup.X1`, as requested.

**Hypotheses: one point needs your attention**
- **(M3), the clauses for `twP`, `twC`, `twB`, `twD`:** as written in (M3) they carry no hypothesis, and in that form they are false. These blocks involve `dfi`: for \(\mathbb{Z}\to\mathbb{Q}\), `dfi 2` is \(0\) in \(\mathbb{Z}\) but \(1/3\) in \(\mathbb{Q}\). I stated these four clauses under `[OddUnits A]`, the hypothesis the file gives for the same maps in (M2). Every other clause of (M3) has no hypothesis. If you want this handled differently, let me know.
- **(G1):** `1 ≤ ds.length` and `1 ≤ i` are kept as in the file, but the proof does not use them, because the entry valuations are given directly. They are named `_hk` and `_hi`, and the docstring says so.
- **(Z2)** is proved more generally: over any commutative ring and any finite index type.
- **Parts V and R** use exactly (H). `‖η‖ = 1` follows from `IsUnit η`, and `‖ζ j f‖ ≤ 1` holds automatically because `ζ` takes values in \(\mathbb{Z}_2\).
- **(Z0), (Z1):** membership in `(2 : ℤ_[2]) ^ N • ⊤` is stated in the bracketed form the file gives, `∃ r, … = 2 ^ N * r`.

Every theorem and helper lemma has a docstring naming its item of C46, and `All.lean` documents the encodings and the reuse. The Properties table has 3 definition rows and 17 property rows (M1–M5, Z0–Z2, G1, G2, V1, V2, R1–R5), all marked proved.

# Summary of changes for run 76de0979-d8f2-404c-9f0f-d8442b5ce66a
I formalized and proved every statement of `C45_conjugation_and_general_eta.md` in a new folder, `RequestProject/Conjugation/`, namespace `Conjugation`. `lake build RequestProject.Conjugation.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`, and `#print axioms` on `C1`–`C5`, `D0`, `I`, `X1`, `X2`, `T_eta`, `T1eta`, `T2eta`, `F1eta` and `F1eta_gen` lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 8 new files (`Defs`, `PartC1`, `PartC2`, `PartC4`, `PartD`, `PartX`, `PartT`, `All`). The folders C1–C44 are untouched, and everything is committed.

**Reuse.** Nothing from the Setting is redefined. The proofs use:
- C40: `Bf`, the twist pieces and `vplus`/`vprime`;
- C40b: `Agree`, `MAgree`, `twP`/`twC`/`twB`/`twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`, `paySys`, `L4_sigma`, `L5`;
- C13: `slots`, `slots_eq`, `splitIso`, `mCount`;
- C3 `oE`; C14 `Dset`, `Ids`; C32 `ds`; C10 `Mc`;
- C42: the floor formulas for a slot of `d :: ds`;
- C43: `piF`, `XiOp`, `SigOp`, `coef_mul_split`;
- C44: `hadOne`, `nest`, `F1`, `T1`, `T2`, `sigOp_magree_paySys`.

**Definitions** (`Defs.lean`): `cj` and `cjSys`, written exactly as in the file.

**Where each part is**
- **(C1)** `C1` (`PartC1.lean`), with the individual lemmas such as `cj_mul`, `cjSys_mul` and `magree_cjSys`.
- **(C2)** `C2` (`PartC2.lean`). All five identities are **exact equalities**, not just agreement.
- **(C3)** `C3` (`PartC2.lean`), covering both the twist move and the split move.
- **(C4)** `C4` (`PartC4.lean`), stated with the file's closed-form weights `w (q j) * u ^ oE (Dset ds j)`, where `q j = ⌊j / 2^m⌋` (`qSlot`). It holds for every `r`, not only `r = 1`. A recursive description, `wkRec`, is proved equal to the closed form (`wkRec_eq`).
- **(C5)** `C5` (`PartC4.lean`): the general formula (`finalM_cjSys`) and the case `r = 1` (`C5_one`).
- **(D0)** `D0` (`PartD.lean`).
- **(I)** `I` (`PartD.lean`): the right inverse is built by the recursion of C43 (P0), the left inverse by the mirror recursion, and the two are shown to agree.
- **(X1), (X2)** `X1` and `X2` (`PartX.lean`).
- **(T1η), (T2η), (F1η)** (`PartT.lean`): `T_eta` gives one `GSig` that satisfies all three. `T1eta`, `T2eta` and `F1eta` state them separately, in the form of the file.

**Hypotheses**
- **Part T:** `T_eta` uses all the hypotheses in the file. Only the dance of `Ξ` is assumed. The two-sided inverses come from (I), and the dance of `Σ` from C40b (L4) together with (D0).
- **(F1η) is more general** (`F1eta_gen`): the formula holds for every dance `GSig` of `SigOp α c η` and every digit list, assuming only `α ≥ 1` and `η ≠ 0`.
- **(X1):** the `SigOp` half (`X1_sig`) does not need `η ≠ 0`.
- **Scope:** Parts C and D are stated over any commutative ring (for (I), any field).

Every docstring names its part of C45, and `All.lean` documents the encodings. The Properties table has one definition row and twelve property rows (C1–C5, D0, I, X1, X2, T1η, T2η, F1η), all marked proved.

# Summary of changes for run 2cccc89d-3209-4a4e-b43d-0cdbff644701
I formalized and proved every statement of `C44_stability_and_rigidity.md` in a new folder, `RequestProject/Stability/`, namespace `Stability`. `lake build RequestProject.Stability.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on `S0`, `S1`, `S2`, `A1`, `A2`, `A3`, `F1`, `F2`, `T1` and `T2` lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 7 new files (`Basic`, `PartS`, `Defs`, `PartA`, `PartF`, `PartT`, `All`); the folders C1–C43 are untouched. Everything is committed.

**Reuse.** Nothing from the Setting is redefined. The proofs use:
- C3 `oE`, `delta`;
- C10 `a`, `pi0`, `Mc`, `lemma_4_5`, `lemma_4_5_empty`, `A4_subadditivity`;
- C13 `slots`, `slots_eq`, `pσ`, `κσ`, `Mfin`;
- C14 `Ids`, `Dset`, `Dlab_inj` (the injectivity of the dancers), `theorem_4_4`, `H3_final_matrix`;
- C32 `Families.ds`;
- C40b `Agree`, `MAgree`, `DanceRel`, `finalM`, `paySys`, `L4_sigma`, `danceRel_unique`;
- C42 `C109`;
- C43 `SigOp`, `XiOp`, `R`.

**Definitions**, written exactly as in the file:
- `hadOne` and `Wt` (`Basic.lean`);
- `nest`, `Amat` and `nuA` (`Defs.lean`);
- the diagonal factors \(d_1, d_2\) of (F2), as `F2d1` and `F2d2` (`PartF.lean`).

`All.lean` documents the encodings: \(\|x\| \le 2^{-s}\) is written `(2 : ℝ) ^ (-(s : ℤ))`, and slots are read through `s.val`.

**Where each part is**
- **(S0), (S1), (S2)** (`PartS.lean`), for every \(s \ge 1\).
  - In (S1), \(\det(1+N)\) is a unit by reduction mod 2 (`norm_det_one_add`).
  - \((1+N)^{-1}\) stays in `Wt S ν 0` by Cayley–Hamilton (`inv_mem_of_closed`).
  - The rest follows the proof sketch.
- **(A1), (A2), (A3)** (`PartA.lean`). In (A3), `B` is the finite geometric series of the nilpotent part `1 − Amat ds`.
- **(F1), (F2)** (`PartF.lean`). `F1_gen` and `F2_gen` hold for any digit list.
- **(T1), (T2)** (`PartT.lean`): C43 `R` gives the entrywise `E` (set to 0 where the `Σ` entry is 0), then (S2) is applied with \(s = \alpha - 1\). (T2) follows from \(\|1+e\| = 1\) when \(\|e\| < 1\).

**Hypotheses**
- **Part S:** the decidability of `S` is not needed (the proofs are classical), so I left it out. All other hypotheses of the setting are used.
- **(F1) is more general:** `l ≥ 1` and `c ≥ 1` are not needed, so they are left out.
- **(F2) is more general:** `l ≥ 1` is not needed, so it is left out.
- **(T1) and (T2)** take exactly the file's hypotheses, and all of them are used. `B`, `YΞ` and `YSig` enter through C43 (R) and C42 (C109).
- **Naming:** the `Σ`-side variables are named `YSig` and `GSig`, because `Σ` is reserved notation in Lean.

Every docstring names its part of C44. The Properties table has one definition row and ten property rows (S0–S2, A1–A3, F1, F2, T1, T2), all marked proved.

# Summary of changes for run 198fbc5c-ff86-43a1-9587-6e3be990b5fb
I formalized and proved every statement of `C43_path_sum.md` in a new folder, `RequestProject/PathSum/`, namespace `PathSum`. `lake build RequestProject.PathSum.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on `P0`, `P1`, `P2` and `R` lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 5 new files (`Defs`, `Aux`, `PartP`, `PartR`, `All`); the folders C1–C42 are untouched. Everything is committed.

**Reuse.** Nothing from the Setting is redefined. The proofs use C40 `FormalOps.Bf` (its product and unit), C40b `Agree`, `DanceRel` and `finalM`, C42 `InvFloors.C109` and `gamma` (C29 `Filt.T`, C32 `Families.ds`, C3 `Rulers.oE` and C14 `Windows.Dset` come in through the statement of `C109`), and C20 `OddUnits`. The project had no instance `OddUnits ℚ_[2]`, so I proved one, `instOddUnitsPadicTwo`: an odd natural number is non-zero in a field of characteristic zero.

**Definitions** (`Defs.lean`): `piF`, `XiOp`, `SigOp` and `sL`, written exactly as in the file. The bound \(2^{-(\alpha-1)}\) is written `(2 : ℝ) ^ (-(α - 1 : ℤ))`, using the norm on `ℚ_[2]`.

**Where each part is**
- **(P0)** `P0` (`PartP.lean`), by strong induction on `L`. It is stated over any field, which is more general than the file.
- **(P1)** `P1`: by (P0), using the recursion \(\mathrm{sL}(L+1,f) = -(L+1)\,\eta\,\mathrm{sL}(L,f-1)/\pi(f)\) (`sL_succ`). This shows that the operator with coefficients `sL` is a right inverse of `Σ`.
- **(P2)** `P2`, Lemma 10.10. It includes `sL α c η L f ≠ 0` and is proved by strong induction on `L` (`P2_gen`).
  - The term \(a = 1\) gives `sL(L, f)`.
  - Each term \(a \ge 2\) is rewritten exactly as \(z \prod \pi(d)\,(-1)^a/(a!\,\eta^a)\) (`term_identity`).
  - Its bound uses \(v_2(\pi(d)) \ge \alpha\) and \(v_2(a!) \le a-1\) (Legendre's formula from Mathlib).
  - The terms are summed with the ultrametric inequality.
- **(R)** `R` (`PartR.lean`): `C109` for `Ξ` and for `Σ` (same `l`, so the same `gamma`), then (P1) and (P2) at the same `L` and `f`. If the `Σ` entry is 0, then `γ = 0` (since `sL ≠ 0`) or the floor condition fails, and in both cases the `Ξ` entry is 0 too.

**Hypotheses**
- **All hypotheses are used.**
- **The hypothesis `α ≥ 2` in (P2) and (R)** is only used through `α ≥ 1`. `P2_gen` states the more general version.
- **The bound `B` in (R)** is only needed to apply `C109`; the conclusion does not depend on it.
- **Naming in (R):** the `Σ`-side variables are named `YSig`, `GSig`, because `Σ` is reserved notation in Lean. Otherwise the statements are as in the file.

Every docstring names its part of C43, and `All.lean` documents the encodings. The Properties table has one definition row and four property rows (P0, P1, P2, R), all marked proved.

# Summary of changes for run d4e089ce-8968-4f48-87e2-98420f6923c1
I formalized and proved every statement of `C42_floors_and_corollary_10_9.md` in a new folder, `RequestProject/InvFloors/`, namespace `InvFloors`. `lake build RequestProject.InvFloors.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on `F1`–`F6` and `C109` lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 6 new files (`Digits`, `Defs`, `PartF`, `PartC`, `PartC109`, `All`). The folders C1–C41 are untouched, and everything is committed.

**Reuse.** Nothing from the Setting is redefined. The proofs use C3 `Rulers.oE`, C13 `Dance.slots`/`mCount`/`splitIso` (through C40d's `FormalProp.splitEquiv`), C14 `Windows.Dset`/`Ids`/`rank`/`Ids_cons`, C18 `DPLattice` (its weight axiom (W)), `one`, `wtV`, `tensorV`, C20 `phi`, C29 `Filt.T`, C32 `Families.ds` (and its (B0b)), C40 `Bf`/`act`/`flD`, C40b `Agree`/`MAgree`/`DanceRel`/`finalM`, C40c `sysAct`/`N2`/`A1`/`sysAct_mul`/`sysAct_one`/`pack`/`vpack`/`unitEquiv`, and C41 `inH`, `outH`, `inj0`, `out1`, `relab`, `castLat`, `ri`, `V5`.

**Definitions** (`Defs.lean`)
- `slotOf`, `inIdx` and `outIdx` follow the same recursion along `l` as `inH` and `outH`, and depend only on `l` and `r`.
- `inIdx` and `outIdx` are the cases `b = 0` and `b = 1` of one shared recursion, `ioIdx b`:
  - twist step: the index `(b, i)`;
  - split step: the index `(a, (b, i))`, where `a` is the second component of `splitEquiv r`.
- The lattice equalities are crossed by a small index transport, `castIdx` (the index version of `castLat`). The slot equalities are crossed by `Fin.cast`.
- The constants of the word are `gamma l X Y` (`PartC.lean`), written exactly as in the file.

**Where each part is**
- **(F1)–(F6):** `F1`, …, `F6` (`PartC.lean`), stated exactly as in the file.
  - Each comes from a strong induction on `l` in `PartF.lean`.
  - (F4) and (F5) are proved together: the floor of `ioIdx b` is `o_D + b(2^k − 1)`.
  - The bit bookkeeping for `Dset (d :: ds)` is in `Digits.lean`.
  - (F6) uses `Dset ⊆ Ids` and C32 (B0b).
- **(C109):** `C109` (`PartC109.lean`), stated exactly as in the file.
  - (A1), (A2) and (N2) make `sysAct (fun _ _ => Ξ)` a linear equivalence whose inverse is `sysAct (fun _ _ => Y)`.
  - (V5) then gives `IsUnit` and the formula for the inverse.
  - The entries are computed by `entry_sysAct`, using (F1), (F2), the weight axiom (W) and (F4)–(F6).

**Hypotheses**
- **All hypotheses of the file are used.**
- **(F6) is more general:** it also holds with any natural number in place of `j` (`F6_nat`).
- **The bound `B` in (C109):** it is only needed to form the action that (V5) is applied to; the conclusion does not depend on it.
- **Instances:** `[IsDomain A] [CharZero A] [OddUnits A]` are needed to form `T`. In (C109), `IsDomain K` comes from `Field K`.

Every docstring names its part of C42, and `All.lean` documents the encodings. The Properties table has two definition rows (the new definitions, and `gamma`) and seven property rows (F1–F6, C109), all marked proved.

# Summary of changes for run 86ac37fe-7261-49ec-ab2a-7fba3e2343e3
I formalized and proved every statement of `C41_inverse_block.md` in a new folder, `RequestProject/InvBlock/`, namespace `InvBlock`. `lake build RequestProject.InvBlock.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on `V1`–`V5` lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 4 new files (`Defs`, `PartV1`, `PartV3`, `All`); the folders C1–C40d are untouched. All work is committed.

**Reuse.** Nothing from the Setting is redefined. The proofs use these existing objects directly:
- C13: `Dance.slots`; `Dance.splitIso`, through C40d's `FormalProp.splitEquiv`.
- C18: `DPLattice`, `one`.
- C29: `Filt.T`, with `T_zero` and its defining equation.
- C32: `Families.ds`, with `ds_zero` and its defining equation.
- C40: `Bf`.
- C40b: `MAgree`, `twP`/`twC`/`twB`/`twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM`.
- C40c: `sysAct`, `pack`, `vpack`, `unitEquiv`, `N1`, `N2`, `A1`, `sysAct_mul`/`one`/`sub`/`smul`, `A3_conj`, `A4_apply`, `T1`, `T2`.
- C40d: the induction is modelled on `Q1_aux`.

C40c's `pivotEquiv`/`schur_eq` and C40d's `Q0` turned out not to be needed.

**Encodings** (docstrings of `Defs.lean` and `All.lean`):
- Vectors are functions `n → N.ι → A` and `Fin ns → A`.
- `inj₀ x = pack (x, 0)` is `inj0` and `out₁ w = (pack.symm w).2` is `out1`.
- `lift N W B' Q G v = pack (−sysAct N W B' (Q * twC G) v, v)`.
- `inH l r` and `outH l r` are defined by recursion on `l`, following the defining equations of `T` and `ds`:
  - \(l = 0\): the identity through `unitEquiv`.
  - Twist step: `inj₀ ∘ inH'` and `outH' ∘ out₁`.
  - Split step: the same, through `vpack` and the relabelling of C40c (A3).
- `inH` and `outH` take only `l` and `r` as arguments, never a system. The type equalities `T A (n+1) = phi (T A (n/2))` and `T A (n+1) = tensorV (phi (T A (n/2)))`, and the slot-count equalities, are transported by two small helpers: a linear equivalence along an equality of lattices, and a reindexing along `Fin.cast`.

**Where each part is**
- **Definitions (new):** `inH`, `outH` (`Defs.lean`).
- **(V1)** `V1` and **(V2)** `V2` (`PartV1.lean`).
- **(V3)** `V3`, stated exactly as in the file (`PartV3.lean`). It comes from `V3_aux`, a strong induction on `l` for all `r`, `G`, `Gk` and `B ≥ l+1`. `V3_aux` is stated for any list `ds` with `Families.ds l = ds`, so that the type of `Gk` can be unfolded.
  - \(l = 0\): (A1) and (A4_apply).
  - Twist step: `L = lift ∘ L'`, using (V1).
  - Split step: `L = vpack ∘ lift ∘ relabel⁻¹ ∘ L'`, using (V2) and (A3_conj).
- **(V4)** `V4` and **(V5)** `V5` (`PartV3.lean`). In (V5), the matrix is invertible by (V4) and `Matrix.mulVec_injective_iff_isUnit`.

**Hypotheses**
- **(V1) and (V2) are more general.** The half `MAgree (Q * twP G) 1` of the clean step (for (V2), `MAgree (Q * twP (vsplit G)) 1`) is never used, so I left it out; the docstrings say so.
- **All other hypotheses are used.**
- **Instances.** `[IsDomain A] [CharZero A] [OddUnits A]` are needed to form `phi` and `T`. In (V5), `IsDomain K` comes from `Field K`.

Every docstring names its part of C41. The Properties table has one definition row (`inH`/`outH`) and five property rows (V1–V5), all marked proved.

# Summary of changes for run 23cdce92-9d3b-4182-bcaf-0642dc2f3b8d
I stated and proved every statement of `C40d_proposition_10_7.md` in a new folder, `RequestProject/FormalProp/`, namespace `FormalProp`. `lake build RequestProject.FormalProp.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on `Q0`, `Q1`, `Q2`, `Q2_zero`, `Q3` and `Q4` lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 5 new files (`Aux`, `PartQ0`, `PartQ1`, `PartQ`, `All`); the folders C1–C40c are untouched. All work is committed.

**Reuse.** Nothing from the Setting is redefined. The proofs use these existing objects directly:
- C13: `Dance.mCount`, `slots`, `slots_eq`, `splitIso`, `dance`, `Mfin`, `pσ`, `κσ`, and the helpers behind `Dance.D2_clocks` (`PQ`, `pqCast`, `funFinEquiv`, `quotSmulTopCongr`).
- C18: `DPLattice`, `one`.
- C29: `Filt.T` with `T_zero`, `T_odd`, `T_even`.
- C32: `Families.ds` with `ds_zero`, `ds_odd`, `ds_even`.
- C34: `BaiCounts.S1`.
- C40b: `DanceRel`, `CleanStep`, `finalM`, `paySys`, `L4_sigma_clean`.
- C40c: `sysAct`, `quotEquivConj`, `N2`, `A1`, `A3equiv`, `A4equiv`, `A4`, `S1equivQ`, `S2equivQ`.

C40's `act_bound` and C40b's `L6` turned out not to be needed. C40c's `pack`, `vpack`, `T1`, `T2` and `N1` are used only inside `S1equivQ` and `S2equivQ`.

**Encodings** (docstring of `All.lean`):
- `k` is written `(Families.ds l).length`, which is what `Dance.nLen` unfolds to, and `m` is written `Dance.mCount (Families.ds l)`.
- A cokernel is `M ⧸ LinearMap.range f`, and `c M` is `(c • ⊤ : Submodule A M)`.
- The direct sum of the factors \(a = 0, \dots, k-1\) is the finite product `(a : Fin k) → …`.

**Where each part is**
- **(Q0)** `Q0` (`PartQ0.lean`). It shows `|(T A l).ι| = |Dance.Idx (ds l)|` by strong induction, then applies `BaiCounts.S1`.
- **(Q1)** `Q1` (`PartQ.lean`), stated exactly as in the file. It comes from `Q1_aux` (`PartQ1.lean`), an induction on the list `ds l`, for all `l`, `r`, `G`, `Gk`, `B ≥ l+1` and `h` at once:
  - Empty list: (A1) turns `G` into `Gk` on `one A`, then (A4) finishes.
  - `false :: rest`: (S1) with `N = T A l'`, then the induction hypothesis at `h+1`.
  - `true :: rest`: (S2), then the relabelling (A3) along `j ↦ ofLex ((splitIso r).symm j)`, then the induction hypothesis at `r*2` and `h+1`.
  - The new factor is counted with (Q0) and flattened with `Fin.consLinearEquiv`, as in `D2_clocks`.
- **(Q2)** `Q2` covers `k ≥ 1`: the factor \(a = 0\) is the zero module and is dropped, and the remaining factors are reindexed by \(a \mapsto a+1\). `Q2_zero` covers `k = 0`, stated for `T A 0` as in the file.
- **(Q3)** `Q3`: (Q1) for both systems, plus an isomorphism between the cokernels of `c • M` and `c • (P*M*Q)` when `P` and `Q` have unit determinant.
- **(Q4)** `Q4`: C40b's `L4_sigma_clean`, then (Q1) with `r = 1`, then a reindexing along `Fin.cast (slots_eq ds 1).symm`.

**Hypotheses**
- **Extra instances.** `Filt.T` only exists over `[IsDomain A] [CharZero A] [OddUnits A]`, so every statement carries these instances, as the file says.
- **The bound needs no transfer.** The induction is run for every `B ≥ l+1` directly, since that is exactly the bound (S1), (S2) and (A4) require. So `act_bound` was not needed.
- **`Q2_zero` is more general.** It needs only `1 ≤ B` (that is, `B ≥ l+1`) and no dance hypothesis.
- **All other hypotheses are used.**

Every docstring names its part of C40d. The Properties table has five property rows (Q0–Q4), all marked proved.

# Summary of changes for run 84a3b2d3-7a3e-4441-8849-311c46001212
I formalized and proved every statement of `C40c_the_action_of_a_system_and_one_move.md` in a new folder, `RequestProject/FormalAct/`, namespace `FormalAct`. `lake build RequestProject.FormalAct.All` succeeds, and the files compile with no warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on N1, N2, A1–A4, `A3_conj`, `A4_apply`, T1, T2, S1 and S2 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 6 new files (`Defs`, `PartN`, `PartA`, `PartT`, `PartS`, `All`); the earlier folders C1–C40b are untouched. All work is committed.

**Reuse.** Nothing from the Setting is redefined. The existing objects are used directly, including C40's `act`, `blockOp`, `schur`, `T0`, `T1`, `V0`, `V1` and `S3equiv` (the explicit form of `S3`), C40b's `MAgree`, `twP`/`twC`/`twB`/`twD`, `vsplit`, `CleanStep`, `finalM` and `C4`, and C29's `Filt.T` with `T_zero`/`T_odd`/`T_even`. (N1) is the same statement as C39's `FoldHalf.E0`, so `N1` simply restates it.

**Encodings** (`Defs.lean`, `All.lean`):
- `sysAct`, `pack` and `vpack` are written exactly as in the file. `pack` and `vpack` are linear equivalences whose inverses read the slots with `slice 0` and `slice 1`.
- A vector of `N^{⊕n}` is `n → N.ι → A`. For `phi N`, the basis is `Fin 2 × N.ι`.
- A cokernel is `M ⧸ LinearMap.range f`, and `c M` is `(c • ⊤ : Submodule A M)`.

**Where each part is**
- **Part N** (`PartN.lean`): `N1` and `N2`.
- **Part A** (`PartA.lean`):
  - (A1) is `A1`.
  - (A2) is `sysAct_one`, `sysAct_mul`, `sysAct_add`, `sysAct_sub` and `sysAct_smul`, collected in `A2`.
  - (A3) is `A3_conj` (conjugation by `LinearEquiv.funCongrLeft`) and `A3`.
  - (A4) is `A4_apply` and `A4`.
- **Part T** (`PartT.lean`): `T1` and `T2`.
- **Part S** (`PartS.lean`): `S1` and `S2`. Each "≃ₗ[A]" statement also has an explicit equivalence for a given clean-step witness `Q`: `S1equivQ`, `S2equivQ`, and likewise `A3equiv`, `A4equiv`.
- The proof of (S1) follows the sketch in the file. By (T1), the action on `phi N` is conjugate (by `pack`, and by `pack` composed with the swap) to C40's `blockOp`. The pivot is a linear equivalence with inverse `sysAct Q`, by (A1) and (A2). The Schur complement equals `2 • sysAct G'`. C40's `S3` then finishes the step.
- (S2) is (T2) plus (N1), followed by (S1) on the index type `n × Fin 2`.

**Hypotheses**
- **Extra instances.** `phi` and `T` only exist over `[IsDomain A] [CharZero A] [OddUnits A]`, so (N1), (N2), (T1), (S1) and (S2) carry these instances, as the file says. Everything else holds over any commutative ring.
- **(A2) needs less than stated.** `1 ≤ B` is only used for the unit, and (nil BN) with `BN ≤ B` only for the product. Sums, differences and scalars are also proved for every `B` with no hypothesis, which is more general.
- **All other hypotheses of the file are used.** (T2), like the file, has no (top W).

Every docstring names its part of C40c. The Properties table has one definition row and four property rows (Parts N, A, T, S); all four property rows are marked proved.

# Summary of changes for run afeddeb6-2004-49ea-b54d-237d18561b66
I formalized and proved every statement of `C40b_the_formal_dance_of_payment_systems.md` in a new folder, `RequestProject/FormalDance/`, namespace `FormalDance`. `lake build RequestProject.FormalDance.All` succeeds. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on C1–C4 and L1–L6 lists at most `propext`, `Classical.choice` and `Quot.sound`. The only change is 6 new files (`Defs`, `PartC`, `PartL1`, `PartL2`, `PartL`, `All`); C1–C40 are untouched. All work is committed.

**Reuse.** Nothing from the Setting is redefined. These are used directly: C40 `Bf` (with its ring structure and `A`-action), `Bf.fd`, `Bf.dg`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`, `act`; C18's condition (W), in (C4); C20 `dfi`; C11 `pT`, `κT`; C12 `pSp`, `κSp` with their value lemmas; and C13 `slots`, `slots_eq`, `splitIso`, `relabP`, `relabK`, `danceAux`, `dance`, `Mfin`, `pσ`, `κσ`, `mCount`. C40's `B4`, `T1` and `V1` motivate the definitions but turned out not to be needed by any proof.

**Encodings** (docstrings in `Defs.lean` and `All.lean`):
- `Agree`, `MAgree`, `ext0`, `paySys`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `Clean` and `finalM` are written exactly as in the file.
- Matrices are Mathlib's `Matrix n n (Bf A)`. `(2 : A) • G` is the entrywise action of `A`.
- Payment systems live on index types with a `LinearOrder`.
- `DanceRel` is defined by recursion on `ds`, with the file's three clauses. Its result `Gk` is a matrix on `Fin (Dance.slots ds r)`.
- In (L2), `PS = fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')`.

**Where each part is**
- **Part C** (`PartC.lean`): `C1`, `C2`, `C3`, `C4`, plus the individual lemmas `Agree.mul`, `MAgree.vsplit`, etc.
- **(L1)** (`PartL1.lean`): `L1`, which includes the two exact equalities `L1_twP` and `L1_schur`, and the `CleanStep` with `Q = 1`.
- **(L2)** (`PartL2.lean`): `L2`, i.e. `twP = 1` exactly, the agreement, and the `CleanStep`.
- **(L3)–(L6)** (`PartL.lean`):
  - `L3`.
  - `L4`, made of `L4_dance` and `finalM_paySys`.
  - The corollary for `σ`: `L4_sigma`, for the explicit witness, and `L4_sigma_clean`, as `Clean` plus an existential witness, using `Fin.cast (slots_eq ds 1).symm`.
  - `L5` and `L6`.

**Hypotheses and generality**
- **(C4) uses only half of (top W).** It needs `N.wt i ≤ W`; the parity condition is unused.
- **(L2) holds exactly.** `L2_schur_eq` proves the second equality as an exact equality, which is stronger than the agreement in the file. The file's own checks had observed this.
- **No finiteness needed for the pivots.** The equalities `twP … = 1` in (L1) and (L2) hold without assuming `n` finite.
- **All other hypotheses are used.** The no-2-torsion hypothesis is used in (L5) and `IsUnit u` in (L6).

Every docstring names its part of C40b. The Properties table has one definition row and two property rows (Part C and Part L); both property rows are marked proved.

# Summary of changes for run 0246c6df-10e6-4a81-b1aa-10212a5affea
I formalized and proved every statement of `C40_the_formal_operators.md` in a new folder, `RequestProject/FormalOps/`, namespace `FormalOps`. `lake build RequestProject.FormalOps.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on `instRing`, `instAlgebra`, B2–B4, T0, T1, V0, V1 and S1–S3 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 7 new files (`Bf`, `Defs`, `PartB`, `PartT`, `PartV`, `PartS`, `All`); C1–C39b are untouched.

**Reuse.** Nothing from the Setting is redefined. These are used directly: C18 `DPLattice` (with the axioms `W_F`, `P0_F`, `P1_F`), `bvec`, `tensorV` with `tensorV_Fd_b0` and `tensorV_Fd_b1`; C20 `OddUnits`, `dfi`, `phi` and `B3`; C39 `FoldHalf.E0`. `H` and `Doubling.B1` turned out not to be needed by any proof.

**Encodings** (docstrings in `Bf.lean`, `Defs.lean` and `All.lean`):
- `Bf A` is a new structure with one field, `coef : ℕ → ℤ → A`, so its multiplication is not the pointwise one. Extensionality is `Bf.ext_iff`.
- `0`, `+`, `−` and scalar multiplication act coefficientwise. `1`, the product, `Bf.fd` and `Bf.dg` are written exactly as in the file.
- `flD`, `act`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`, `blockOp` and `schur` are also written exactly as in the file. The floor is `(W − N.wt i) / 2` with integer division.
- The submodule `c K₁` is written `(c • ⊤ : Submodule A K₁)`, Mathlib's pointwise scalar multiple of `⊤`.
- Each "≃ₗ[A]" statement is given both as an explicit equivalence (`S1equiv`, `S2equiv`, `S3equiv`) and as a `Nonempty` theorem.

**Where each part is**
- **Part B**:
  - (B1): `Bf.instRing` and `Bf.instAlgebra` (built from `Bf.smul_mul` and `Bf.mul_smul`), with the simp lemmas `coef_add`, `coef_mul`, `coef_one`, `coef_fd`, `coef_dg`.
  - (B2): `flD_one`, `flD_add`, `flD_mul`, collected in `B2`, plus `flDHom` (`flD N W` as a ring hom).
  - (B3): `B3`.
  - (B4): `act_bound`, `act_one`, `act_add`, `act_smul`, `act_mul`, `act_fd`, `act_dg`, collected in `B4`.
- **Part T**: `T0`; `T1_b0` and `T1_b1`, collected in `T1`.
- **Part V**: `V0_top` and `V0_nil`, collected in `V0`; `V1_b0` and `V1_b1`, collected in `V1`.
- **Part S**: `S1`, `S2`, `S3`.

**Hypotheses**
- **(top W) is unused in (B3), (B4) and (V1).** Because the floor uses integer division, `(W − (w − 2a)) / 2 = (W − w) / 2 + a` holds for every integer `w`, with no parity condition. So these three are stated without (top W), which is more general; the docstrings say so.
- **(nil BN) is not needed for part of (B4).** `act 1 = 1`, additivity, compatibility with scalars and `act (dg p) = flD p` hold without it. They are also given as separate lemmas without (nil BN), for every `B` or every `B ≥ 1`.
- **Where the hypotheses are used.** (top W) is used in (T0), (T1) and the first half of (V0). (nil BN) is used in the rest of (B4), in (T1), the second half of (V0) and (V1).
- **Extra instances in Part T.** `Doubling.phi` can only be formed over a ring with `[IsDomain A] [CharZero A] [OddUnits A]`, so Part T carries these instances, as the file's Setting says.

Every docstring names its part of C40. The Properties table has one definition row and four property rows (Parts B, T, V, S); the four property rows are marked proved.

# Summary of changes for run 579e5944-e17c-407a-86cc-c2beb8273961
The Lean formalization is already done: my previous message described Lean files that are in the project, not just an informal explanation. Every statement of `C39b_the_cube_side_on_the_half_lattice.md` is stated and proved in `RequestProject/FoldCube/`, namespace `FoldCube`. I just rebuilt it to confirm: `lake build RequestProject.FoldCube.All` succeeds with no errors or warnings. The folder contains no `sorry`, no `axiom` declarations and no `native_decide`. `#print axioms` on each main theorem lists only `propext`, `Classical.choice` and `Quot.sound`. All work is committed, and C1–C39 are unchanged.

**Files**
- `Defs.lean`: the new definitions `Jop`, `Gp`, `SigmaOp`, `halfJJ`, `thetaOp`, `thX` and `thY`, written exactly as in the file. They reuse the existing C18/C20/C38/C39 objects without redefining any of them.
- `Aux.lean`: general helpers — building a quotient isomorphism from a surjective map, diagonal operators, how `F` commutes past a diagonal operator, and cancelling a factor of 2.
- `PartO1.lean`:
  - `O1`, through the explicit `O1equiv`.
  - `O2`, through `O2equiv`; the class of `x` goes to `2·[x]`.
  - `O2_pi`: `ι → A` has no 2-torsion over a characteristic-zero domain.
- `PartO3.lean`:
  - `O3`, through `O3equiv`, proved as in the sketch: conjugate by the diagonal of floor units `σ` and multiply on the right by `−u⁻¹`.
  - `O4`.
  - `O5` (first form) and `O5_X` (second form) of Lemma 10.4(b) over `ℤ_[2]`.
- `PartV.lean`: `V1` (through `V1equiv`), `V2` and `V2_phi`, and `V4` (through `V4equiv`).
- `PartV3.lean`: `V3a`, `V3b` and `V3c`, collected in `V3`.
- `PartV5.lean`: `V5` (through `V5equiv`) and `V6` (Lemma 10.5(b) over `ℤ_[2]`).
- `All.lean`: documents the encodings, which existing object is reused where, and the hypotheses.

**One hypothesis to know about.** `Doubling.phi` can only be formed over rings with `[IsDomain A] [CharZero A] [OddUnits A]`. So the results that mention it — (O1), the second sentence of (V2), (V3), (V5), and the definitions `thX` and `thY` — carry these instances, as the file's Setting says.

**Hypotheses.** Some results hold more generally than stated, and their docstrings say so: (O2), (V1), the first sentence of (V2) and (V4) hold over any commutative ring, and (O3) needs only `[OddUnits A]`. No hypothesis of the file is unused. Every docstring names its part of C39b.

The Properties table has one definition row and two property rows (Part O and Part V); both property rows are marked proved.

# Summary of changes for run f1cf204b-2757-42c9-87b8-7fb51c87a70d
I formalized and proved every statement of `C39_the_fold_on_the_half_lattice.md` in a new folder, `RequestProject/FoldHalf/`, namespace `FoldHalf`. `lake build RequestProject.FoldHalf.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on S1–S4, E0–E5 and A1–A4 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 7 new files (`Defs`, `Ops`, `Quot`, `PartS`, `PartE`, `PartA`, `All`); C1–C38b are untouched.

**One hypothesis differs from the file.** `Doubling.phi` (C20) can only be formed over a ring with `[IsDomain A] [CharZero A] [OddUnits A]`. So Part E, (A1) and (A2) carry these two extra instances; the file's Setting lists only `OddUnits`.

**Reuse.** Nothing from the Setting is redefined. These are used directly: `DPLattice`, `H`, `bvec`/`slice`, `wtV`, `tensorV`, `dfi`, `phi` with `B3` (and `B1`), `signOp`, `expF`, `aOp`, `tauOp`, `Xbar`, `Filt.T` (`T_zero`/`T_odd`/`T_even`), `Lemma35.Fd_eq_zero_of_bound` and `FoldGroup.XbarFam`.

**Encodings** (in the docstrings of `Defs.lean` and `All.lean`):
- `Ch`, `Sh`, `parOp`, `ShInv` (`Ring.inverse` in `Module.End A (N.ι → A)`), `Psi` and `Zop` are written exactly as in the file.
- `glueOp X Y Z (m, m') = (X m, Z m + Y m')` is defined for operators on any module, which is more general.
- In (E4), `id (bvec 0 x) : (phi N).ι → A` is there only so that the sum `bvec 0 x + aOp … (bvec 0 y)` type-checks.
- `PE` and `QE` are the file's `P` and `Q`; `beta` is `β`.
- Each "≃ₗ[A]" statement is given both as an explicit definition (`betaEquiv`, `A1equiv`, `A2equiv`) and as a `Nonempty`/existence theorem.

**Where each part is**
- **Part S** (`PartS.lean`):
  - `S1`: `Sh = 1 + Σ` of commuting nilpotent terms.
  - `S2`, `S3`, `S4`. These three hold without (nil), so they are stated without it (more general).
- **Part E** (`PartE.lean`):
  - `E0`, `E1`, `E2`.
  - `E3` comes from two general facts in `Ops.lean`, valid on any DP-lattice with `F^{(r)} = 0` for `r ≥ B`. First, `signOp·expF·signOp = Σ(−1)^r F^{(r)}` is inverse to `expF`, so `aOp² = 1`. Second, `expF·F + F·expF = expF·H − H·expF`, so `aOp` commutes with `tauOp`.
  - `E4`, with the explicit inverse of `β`.
  - `E5`.
- **Part A** (`PartA.lean`):
  - `A1`: the class of `β(x, y)` is sent to the class of `x + y`.
  - `A2` follows the file's sketch. The map `ψ(b₀u₀ + b₁u₁) = u₀ + (1 − a)u₁` turns `tauOp` into `f = 1 + tauOp − aOp`. Then `β⁻¹` and the slot change `(u, v) ↦ (v − u, u)` turn `f` into `glueOp (Psi (d+1)) (Psi d) (Zop d)`.
  - `A3`, by strong induction on `l`.
  - `A4` (also split as `A4_odd` and `A4_even`), from `T_odd`/`T_even`, (A1)–(A3) and the bounds of the file.

**Hypotheses.** (nil) is used in (S1) and in all of Parts E and A. Every docstring names its part of C39. The Properties table has one definition row and three property rows (Parts S, E, A); the three property rows are marked proved.

# Summary of changes for run 02a121a5-8239-42de-8301-7bebd9343fb9
I formalized and proved every statement of `C38b_the_folded_cube_and_proposition_103.md` in a new folder, `RequestProject/FoldGroup/`, namespace `FoldGroup`. `lake build RequestProject.FoldGroup.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on K1, K2, K3, D1, D2, D3, P1 and P2 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 5 new files (`Defs`, `PartK`, `PartD`, `PartP`, `All`); C1–C38 are untouched.

**Reuse.** Nothing from the Setting is redefined; the listed objects are used directly, and `All.lean` says which ones are used. C17's `D2`, `psi`, `range_tensor_eq` and `cokerTensorEquiv` serve only as models: their proofs are repeated for `Gbar n`. C32's `T3` serves as a model for (D3), using its reindexing `famReindex`. A few listed items are not referenced by name: C38 `G3` and `G3Z` (the explicit `G3equiv` is used instead), and C38 `aElt`, `transl` and `foldSub`, which enter only through `G3equiv` and `C2`.

**Encodings** (in the docstrings of `Defs.lean` and `All.lean`):
- `XbarFam lam i` is written exactly as in the file. The centre is the integer `lam + 2 * i` and the bound is the natural number `lam + 2 * i + 1`.
- `twoM M` is `(nsmulAddMonoidHom 2).range`, i.e. the range of `x ↦ 2 • x`, as an `AddSubgroup M`.
- Every "≃" statement is a `Nonempty` theorem. Where an equivalence can be built explicitly, it is also given as a definition: `cokerBarEquivKBar`, `twoMPi`, `twoMProd`, `twoMCongr` and `twoMPadic`.

**Where each part is**
- **Part K** (`PartK.lean`):
  - `K1`, for every commutative ring.
  - `K2`, proved as the sketch says. The sum map splits off a copy of `ℤ`. Its kernel is torsion: lift through `push`, then use C17 `cokerEquivK` and `K_finite`. So the kernel is finite, and C17's `torsionEquivOfProd` identifies it with `KBar n`.
  - `K3`, from right exactness of the tensor product together with (K2) and C17 `D1`.
- **Part D** (`PartD.lean`):
  - `D1`: (K3), then `G3equiv` over `ℤ_[2]`, then C38 `C2`.
  - `D2`: uses `λ + 2·((n − λ)/2) = n` on the support, from C31 (M3) and `L 0 = [0]`.
  - `D3`: reindexes (D2) by value and multiplicity, as in C32 (T3).
- **Part P** (`PartP.lean`):
  - The four (P1) facts, collected in `P1`.
  - `P2` (Proposition 10.3). It chains (D2), `HX` factor by factor, (P1) and C32 `T2` to get an equivalence `ℤ_[2] × Syl2 (KBar n) ≃+ ℤ_[2] × twoM (Syl2 (K n))`. C37 `Mirror.cancel_torsion` then removes the `ℤ_[2]` factor.

**Hypotheses**
- The product part of (P1) is proved for every index type, not only finite ones, which is more general than the file.
- In (P2), both `HX` (only for `λ ≥ 1`) and `n ≥ 1` are used: `n ≥ 1` makes every `λ` in `L n` at least 1, by C31 (M3).
- No hypothesis is unused.

Every docstring names its part of C38b. The Properties table has one definition row and three property rows (Parts K, D, P); the three property rows are marked proved.

# Summary of changes for run 5fde1d99-6aa7-41e9-8775-fa26a284af24
I formalized and proved every statement of `C38_the_fold_in_the_group_ring.md` in a new folder, `RequestProject/Fold/`, namespace `Fold`. `lake build RequestProject.Fold.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on G1, G2, G3, G3Z, L0–L4 and C1–C2 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 6 new files (`Defs`, `PartG`, `PartL`, `Transport`, `Corollary`, `All`); C1–C37 are untouched.

**Reuse.** Nothing from the Setting is redefined; the listed objects are used directly, and `All.lean` says which ones are used. A few listed items are not referenced by name:
- C17 `coker`, `K`, `Syl2` — `cokerBar` and `KBar` are defined the same way.
- C20 `Iso.trans`, `Iso.symm`.
- C31 `m`, `Z1_D2` — (C2) comes from (C1) using the hypotheses of C28 `Lift2.Z1` and C21 `Twist.C3_hyp`, the same way C31 gets `Z1_D2`.
- C32 `Q1`. It only says such an equivalence exists, and only mentions `Fd 1` and `H`. So I rebuilt its equivalence with the same recursion as a definition, `dsumMapEquiv`. That way it can be shown to carry every `Fd r` and every diagonal operator component by component.

**Encodings** (in the docstrings of `Defs.lean` and `All.lean`): all 14 definitions are written exactly as in the file.
- `Gbar n` is Mathlib's quotient group `G n ⧸ AddSubgroup.zmultiples (aElt n)`, and `mk n` is the quotient map, as an additive homomorphism.
- `push` sums over `univ.filter (mk n g = x)`.
- `signOp` uses integer division and `natAbs`.
- Each "≃ₗ[A]" statement is given both as an explicit definition (`G3equiv`, `G3Zequiv`, `L3equiv`, `L4equiv`, `foldEquivXbar`) and as a `Nonempty` theorem. (C1) and (C2) are only `Nonempty`, because C31 (D2) is.

**Where each part is**
- **Part G** (`PartG.lean`): `G1`; `G2`, made of `push_surjective`, `ker_push` and `push_lap`; `G3`, with `G3equiv_symm_mk` showing the map is induced by `push`; `G3Z`, the case `A = ℤ` for `cokerBar`. The proofs use the fact that the coset of `g` is `{g, g + aElt n}`.
- **Part L**:
  - `L0`, `L1` (Lemma 10.1) and `L2` are in `PartL.lean`. `L1` is proved by induction along the recursion of `psi`: on the two slots, `aOp` acts as \((x_0,x_1)\mapsto(a\,x_0,\,-a(x_0+x_1))\).
  - `L3` and `L4` are in `Transport.lean`. `L3_charZero` covers the last sentence of (L3), through C25 `P1`. `L4_map` is the general form of (L4) for lists `l.map f`.
- **Part C** (`Corollary.lean`): `foldEquivXbar` gives `(G n → A) ⧸ foldSub A n ≃ Xbar (tensorPow A n) n (n + 1)`, from `psi_comm`, `Tn = tauOp` and (L1). `C1` then follows from (Q0), (D2), (L3) with (P1), and (L4). `C2` is the case `ℤ_[2]`.

**Hypotheses**
- In (L3), `IsWtPres u.inv.toLin` is kept as in the file but not used; it is named `_hinv`.
- Every hypothesis of (C1) is used.
- Parts G, (L0), (L1), (L2) and (L4) hold for every commutative ring with no extra hypothesis.

Every docstring names its part of C38. The Properties table has one definition row and three property rows (Parts G, L and C); the three property rows are marked proved.

# Summary of changes for run dbf16242-ca0b-4fba-8227-585e89a2fe59
I formalized and proved every statement of `C37_the_mirror_that_doubles.md` in a new folder, `RequestProject/Mirror/`, namespace `Mirror`. `lake build RequestProject.Mirror.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on A1–A5, B1, B2, C1, F1, F2, X1–X5, Y1 and Y2 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 7 new files; C1–C36 are untouched.

**Reuse.** Nothing from the Setting is redefined; the listed objects are used directly. A few listed items are not referenced by name: C31 `M4`, C33 `M2`, `S1_lam`, `S1_xi` and C36 `E1`. C32 `B0b` is used only through C33 `S1_succ`, and C33 `S3_card` only through `Windows.card_Ids`.

**Encodings** (in the docstrings and in `Mirror/All.lean`):
- "Odd" is `% 2 = 1`.
- The doubled sequence of `x` is `fun j => x (j / 2)`, of length `2 * N`.
- `J = i + o_D`, the shift `(2^e − 1 − λ)/2`, `k`, `I`, `k'` and `I'` are written out in full.
- `S n` is written out as `CubeLaplacian.Syl2 (CubeLaplacian.K n)`, and "≅" is `Nonempty (… ≃+ …)`.

**Where each part is**
- **Part A** (`Families.lean`): `A1`, `A2`, `A3`, `A4`, `A5`. Each item is also its own lemma (`A1_map`, `A3_even`, `A5_h_zero`, …).
- **Part B** (`Clocks.lean`): `B1`, `B2`, in `ℤ`. Both rest on the complement rule \(s_2(2^f-1-b)=f-s_2(b)\).
- **Part C** (`Theorem.lean`): `C1`. It uses B1/B2 and A5, plus the valuation \(v_2(J)=t_1-1\).
- **Part F** (`Fit.lean`): `F1` comes from the characterization of the fit (C1, Lemma 7.1, global form) and uniqueness, not from an algorithm. `F2` is computed on the doubled level sets.
- **Part X** (`Exps.lean`): `X1`–`X5`, exactly as stated in the file.
- **Part Y** (`Group.lean`): `Y1`, `Y2`. These are proved for the groups themselves (not only for the exponent multisets), starting from C33 `M2equiv`:
  - each family `λ + 1` with `λ < 2^e − 1` gives `XFam λ i × XFam λ i` (`famDouble`);
  - the top family gives the extra factor `Q (2^e + e − 1)` (`famTop`);
  - the extra `ℤ_[2]` factors are cancelled through 2-power torsion, as the file suggests (`cancel_torsion`);
  - `Q a ≃+* ZMod (2^a)` goes through `PadicInt.toZModPow` (`QequivZMod`).

**Hypotheses**
- In (A5), the items `h' t = h t` and `h'(D) = h(D)` do not need `I ⊆ range k`; they are also stated as separate lemmas without it. The combined `A5` keeps the file's hypotheses.
- In (C1) and (X1)–(X3), `e ≥ 1` is kept as in the file, but it already follows from `λ < 2^e − 1`.
- Every other stated hypothesis is needed.

Every docstring names its part of C37. The Properties table has six new rows (Parts A, B, C, F, X, Y), all marked proved.

# Summary of changes for run bf28bdd8-06ed-4c29-b849-cf8396e89252
I formalized and proved every statement of `C36_the_podium_corollary.md` in a new folder, `RequestProject/PodiumCor/`, namespace `PodiumCor`. `lake build RequestProject.PodiumCor.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on g0, D0, D1, E1–E3, L1–L3, W1, W2, B0–B8, P1–P3 and G1–G3 lists only `propext`, `Classical.choice` and `Quot.sound`. The only change is 11 new files; C1–C35 and C35b are untouched.

**Reuse.** Nothing from the Setting is redefined. The C3, C13, C14, C16, C17, C31–C35 and C35b objects are used directly. C33 (S4) is used through its explicit equivalence `S4equiv`, and C34's counting lemmas are reused for the layers. These listed items turned out not to be needed:
- C33 `M1` and `S4_Q0`;
- C34 `A3_pos`, `A3_zero` and the `l0_*` lemmas (Part D proves the same facts for every layer);
- C35 `La`, `Lb` and `Lc_*` (used only through (Ld));
- C35b `H1` and `H2`.

**Encodings** (each is described in a docstring and in `PodiumCor/All.lean`):
- `layer` and `cExp` are written exactly as you specified.
- `smallExps`, `bigExps`, `famExps` and `exps` are `Multiset ℕ`, written out as in the file, with `s = (Windows.Ids (ds λ)).card`.
- `gmax N` is `Finset.sup'` of `φ` over `Ico 1 N` for `N ≥ 2`, and `0` otherwise. Its defining property (g0) is proved as `g0`.
- `c r` is `cExp (Syl2 (K n)) r : ℕ`, compared with integers through the cast to `ℤ`.
- "The `r`-th largest exponent" is `((exps n).sort (fun a b => b ≤ a)).getD (r − 1) 0`.

**Where each part is**
- **Part D** (`Layers.lean`): (D0) `D0`; (D1) `D1`, with its five items also proved separately (`layer_congr`, `layer_prod`, `layer_pi`, `layer_padic`, `layer_Q`).
- **Part E** (`Dictionary.lean`): `E1`, `E2`, `E3`. (E2) and (E3) are instances of `cExp_le_iff` and `cExp_eq_getD`, which hold for any group whose layers are \(2^{\#\{x\in M:\,j<x\}}\) for some multiset \(M\).
- **Part L** (`Mult.lean`): `L1`, `L2`, `L3`. These use the recursion `L (n+1) = (L n).flatMap Vdot` directly.
- **Part W** (`Shift2.lean`): `W1`, `W2`.
- **Part B** (`Bounds.lean`): `B0`–`B8`.
- **Part P** (`Corollary.lean`, with the counting of exponents above and at `G` in `Counting.lean`): `P1`, `P2`, `P3`.
- **Part G** (`Gao.lean`): `G1`, `G2`, `G3`. The case `n = 3` goes through `exps 3 = {3, 3, 1}`, which comes from `L 3 = [1, 1, 3]`.

**Hypotheses**
- In (L1), `1 ≤ n` is kept but not used.
- In (B0) and (B1), `λ ≥ 1` is kept but not used, because it follows from `m λ n ≠ 0`.
- (B3) is stated without `s ≥ 1`, which neither part needs.
- Every other stated hypothesis is used.

Every docstring names its part of C36. The Properties table has one definition row and seven property rows (Parts D, E, L, W, B, P, G), all marked proved.

# Summary of changes for run ffecadc3-41d6-4c41-b684-66eaeef1a37f
I formalized and proved every statement of `C35b_the_podium_walk.md` in a new folder, `RequestProject/PodiumWalk/`, namespace `PodiumWalk`. `lake build RequestProject.PodiumWalk.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on H1, H2, T1, T2, T3, Z1, Z2 and C1 lists only `propext`, `Classical.choice` and `Quot.sound`. The only changes are six new files (`Walk.lean`, `Steps.lean`, `Head.lean`, `Shift1.lean`, `Shift0.lean`, `All.lean`); C1–C35 are untouched.

**Reuse.** Nothing from the Setting is redefined. The objects you listed are used directly, including `fit`, `ifit`, `levelSet`, `phi`, `clock`, `dancer`, `yPool`, `yPool0`, `ds`, `S1_lam`, and C35's `psi`, `P`, `tAt`, `Y`, `La` and `M5`. Two neighbouring results from those same pieces are also used: C8's `yhat` and C9's cell clocks and cell shift.

**Encodings** (in the docstrings and in `All.lean`):
- \(\lambda\) is `lam`, `d = Families.ds lam`, `k = d.length`, `I = Windows.Ids d`, `s = I.card`, `N = 2 ^ Dance.mCount d` (equal to \(2^s\)).
- `Y l = Podium.Y k I l` and `t₁ = Podium.tAt k I 0`.
- A sum over \(q < 2^l\) is a sum over `Finset.range (2 ^ l)`.
- A maximum is written with an explicit witness: `(∃ l₀ in range, v = f l₀) ∧ ∀ l in range, f l ≤ v`.
- One helper definition is added: `tailVal k I l := −ψ(I ∖ P_l)`. `phi_Y` proves \(k + K + \texttt{tailVal} = \varphi(Y_l)\).

**Results**
- **Part H** (`Head.lean`): (H1) `H1` and (H2) `H2`.
- **Part T** (`Shift1.lean`): (T1) `T1`, (T2) `T2` and (T3) `T3`.
- **Part Z** (`Shift0.lean`): (Z1) `Z1` and (Z2) `Z2`.
- **Part C** (`Head.lean`): (C1) `C1`.
- Each result is also proved for an arbitrary digit list, under the names `*_ds`. In `C1_ds`, \(\lambda\) is `Rulers.lam k I`.

**How the proofs go.**
- **Part H.** `house_head` proves, by induction along the walk (C7 (W3) and (Cut)), that the first level set of the fit of every house is the set of positions \([0, 2^l)\). Lemma 7.9 (I1)/(I2) and C9's cut lemma show the cell shift keeps this level set. Integrality and consequence (L) then give (H1). (H2) holds because `yPool d i` is the real fit, so it is non-increasing.
- **Part C.** (C1) combines (H2), (H1), a re-indexing from positions \(< 2^l\) to subsets of \(P_l\), and C35 `M5`, applied with the maximum of \(\varphi\) on \([1, \lambda+i]\).
- **Parts T and Z.** These follow the walks of the houses \((I,k,0,1)\) (`house_T`) and \((I,k,K-1,1)\) (`house_Z`). The walk increment works out to the constant \(-\psi_c\) in the first house, and to \(2^c\) at position 0 and \(-\psi_c\) elsewhere in the second (`dWalk_zero`, `dWalk_top`). The pooled clocks are linked to these houses through C16 `R1`/`R2` and Lemma 7.9 (I3).

**Hypotheses.**
- No statement uses `λ ≥ 1`, so it is left out; all results hold for every \(\lambda\).
- (T2) is stated without `1 ≤ s`, which follows from `1 ≤ p < N`.
- (Z2) is stated without `2 ≤ s`, which follows from `1 ≤ q < N − 1`.
- (Z1) uses `1 ≤ s`, (T3) uses `0 ∈ I`, and (H1), (H2), (C1) use `i ≥ 1`.

Every docstring names its part of C35b. I added four property rows to the Properties table (Parts H, T, Z and C), all marked proved.

# Summary of changes for run 4f36edd7-b6b9-4d74-9e7f-a79e5a9db67b
I formalized and proved every statement of `C35_the_podium_arithmetic.md` in a new folder, `RequestProject/Podium/`, namespace `Podium`. `lake build RequestProject.Podium.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`, and `#print axioms` on every main theorem lists only `propext`, `Classical.choice` and `Quot.sound`. The only changes are five new files (`Defs.lean`, `Clearings.lean`, `Carries.lean`, `Mean.lean`, `All.lean`); C1–C34 are untouched.

**Reuse.** Nothing from the Setting is redefined. I used C3's `Rulers.s2`, `v2`, `kappa`, `phi`, `oE`, `minOr`, `h` (and `next` through it), `t1`, `hSum`, `lam`, `clock` and `proposition_5_3` directly. `Rulers.xi` and `lemma_5_0_xi` are only used inside `proposition_5_3`, so they never appear by name.

**Encodings** (described in the docstrings and in `Podium/All.lean`):
- `psi k I E : ℤ := Σ_{t∈E} ((Rulers.h k I t : ℤ) − 2^t)`.
- `P I l := I.filter (fun t => (I.filter (· < t)).card < l)`, the definition the file recommends.
- `tAt k I l := Rulers.minOr k (I \ P I l)`.
- `Y k I l := 2^k + Rulers.oE (I \ P I l)`.
- `clear N q := 2^q * (N / 2^q)`.
- The family is given by `hI : I ⊆ Finset.range k`, and `s = I.card`.
- The subsets `D ⊆ P_l` are the elements of `(P I l).powerset`.
- The bracket \([2^q \le m \bmod 2^q + o]\) is an `if … then 1 else 0`.

**Results**
- **Part P** (`Defs.lean`): (P0) `P0`.
- **Part L** (`Clearings.lean`):
  - (La) `La`.
  - (Lb) `Lb_le` and `Lb`.
  - (Lc) `Lc_Y_eq_clear`, `Lc_clear_eq_Y`, `Lc_Y_le_Y_one` and `Lc_clear_Y_one`.
  - (Ld) `Ld` and `Ld_one`.
- **Part K** (`Carries.lean`): (K) `K`, for any `a : ℕ` (so `a = 0` is allowed, as in the file). The proof counts the carries of `a + B` using Kummer's theorem from Mathlib.
- **Part M** (`Mean.lean`, with (M3) in `Carries.lean`): `M1` (from C3 `proposition_5_3`), `M2`, `M3`, `M4` and `M5`.

**Hypotheses that turned out not to be needed.** In these cases I proved the more general statement and say so in the docstring:
- (P0) does not use `I ⊆ range k`, and uses `l ≤ s` only for `|P_l| = l`.
- (La), the first part of (Lc), (M2) and (M4) hold for every `l`, not just `l ≤ s`.
- In (Lb), the hypothesis `N ≥ 1` follows from `1 ≤ y ≤ N`, so I left it out.
- `Y_l ≤ Y_1` holds for every `l ≥ 1`; it needs neither `1 ≤ s`, `l ≤ s` nor `I ⊆ range k`.

(M5) does use `l ≤ s`, to count the \(2^l\) subsets of \(P_l\). Every docstring names its part of C35.

In the Properties table I added one definition row (the five new definitions) and four property rows (Parts P, L, K and M), all marked proved.

# Summary of changes for run 2456f22c-7821-478b-826c-bb3a96310b4f
I formalized and proved every statement of `C34_bais_counts.md` in a new folder, `RequestProject/BaiCounts/`, namespace `BaiCounts`. `lake build RequestProject.BaiCounts.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on A1, A2, A3_pos, A3_zero, F1, F2, S1, S2, S3, S3_short, B1 and B2 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added six files (`Layers.lean`, `Clocks.lean`, `Counts.lean`, `Family.lean`, `Corollary.lean`, `All.lean`); C1–C33 are unchanged.

**Reuse.** Nothing from the Setting is redefined; the C1, C3, C7, C13, C14, C16, C17, C31, C32 and C33 objects are used directly. C33 (S4) is used through its explicit equivalence `S4equiv`. Six listed items turned out not to be needed: C31 `M4`, `L1`, `L2` and C33 `M1`, `S1_lam`, `S2`, `S3_card`.

**Encodings** (described in the docstrings and in `BaiCounts/All.lean`):
- `twoPow G j : AddSubgroup G` is \(2^jG = \{2^j\cdot x\}\).
- `l0 G = Nat.card (G ⧸ twoPow G 1)` and `l1 G = Nat.card (twoPow G 1 ⧸ (twoPow G 2).addSubgroupOf (twoPow G 1))`, exactly as you specified.
- \(\lambda\) is written `lam`.
- `c1 lam` is \(c_1(\lambda)\) and `aN n` is \(a_n\).
- A sum over the positions of `L n` is a sum over `j : Fin (L n).length`.

**Results**
- **Part A** (`Clocks.lean`):
  - (A1) `A1`.
  - (A2) `A2`.
  - (A3) `A3_pos` and `A3_zero`.
  - The proof of (A1) needs one extra fact, that \(\kappa \ge 0\), proved here as `kappa_nonneg`.
- **Bookkeeping for the layers** (`Layers.lean`):
  - Invariance under `≃+`: `l0_congr`, `l1_congr`.
  - Multiplicativity over products of two and over finite dependent products: `l0_prod`, `l1_prod`, `l0_pi`, `l1_pi`.
  - Values on `Q e` and on `ℤ_[2]`: \(\ell_0(Q\,e)=2\) for \(e\ge1\), \(\ell_1(Q\,e)=2\) for \(e\ge2\) and \(1\) for \(e\le1\), and \(\ell_0(\mathbb Z_2)=\ell_1(\mathbb Z_2)=2\).
- **Part F** (`Family.lean`): (F1) `F1` and (F2) `F2`. Both go through C33 (S4), the geometric sums of the sketch, and (A3) for the big clocks.
- **Part S** (`Counts.lean`):
  - (S1) `S1`.
  - (S2) `S2`, by induction with the `Vdot` rule.
  - (S3) `S3`, plus `S3_short` for the claim that the only families with length ≤ 1 are \(\lambda = 1, 2\).
- **Part B** (`Corollary.lean`): (B1) `B1` for \(n \ge 1\) and (B2) `B2` for \(n \ge 2\). Both use C33 (M2), the layer bookkeeping, (F1), (F2), (S2), (S3), and C31 (L3), (L4), (M3).

**Hypotheses.** In (A1), the hypothesis `1 ≤ i ∨ D ≠ ∅` is kept as in the file but is not used. `A1_general` proves the statement without it, because when \(D=\emptyset\) already \(\xi = 2^k + o_I \ge 2\). `A3_zero` uses this general form, so it does not need the fact `dancer (I λ) (j+1) ≠ ∅`. The hypothesis `1 ≤ k` is needed: `A1_k_zero` shows the clock equals 1 when \(k=0\), \(I=D=\emptyset\), \(i=1\). Every docstring names its part of C34.

The Properties table has one definition row (the layers) and four property rows (Parts A, F, S, B), all marked proved.

# Summary of changes for run 960dc443-fefb-47dd-938b-1219372d6e2b
I formalized and proved every statement of `C33_the_main_theorem.md` in a new folder, `RequestProject/MainTheorem/`, namespace `MainTheorem`. `lake build RequestProject.MainTheorem.All` succeeds with no errors or warnings. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on every main result shows only `propext`, `Classical.choice` and `Quot.sound`. I only added four files (`Shape.lean`, `Group.lean`, `Theorem.lean`, `All.lean`); C1–C32 are unchanged.

**Reuse.** Nothing from the Setting is redefined. The objects of C3, C7, C13, C14, C16, C17, C31 and C32 are used directly. `Rulers.clock` comes in through C16's `yPool`/`yPool0` and `Rulers.xi`. Two listed items are not used: C7 `lemma_0a` and C31 `M4`.

**Encodings** (described in the docstrings and in `MainTheorem/All.lean`):
- `ℤ_[2]` is `PadicInt 2`, and `λ` is written `lam`.
- `k λ`, `I λ` and `N λ` are written out in full in each statement as `(ds lam).length`, `Windows.Ids (ds lam)` and `2 ^ Dance.mCount (ds lam)`.
- "`X ≅ Y`" is `Nonempty (… ≃ₗ[ℤ_[2]] …)` in Parts S and G, and `Nonempty (… ≃+ …)` in Part M. Explicit equivalences are also given: `S4equiv`, `G2equiv`, `M1equiv`, `M2equiv`.

**Results**
- **Part S** (`Shape.lean`):
  - (S1) `S1_lam`, `S1_oE`, `S1_succ`, plus `S1_xi`, which says \(\xi_D = \lambda + 1 - 2 o_D\).
  - (S2) `S2` and `S2_length`.
  - (S3) `S3_subset` and `S3_card`.
  - (S4) `S4` (built from `Submodule.quotientPi`) and `S4_Q0`.
  - (S5) `S5_order`, `S5_zero` (proved for every `I`) and `S5_unique`.
- **Part G** (`Group.lean`):
  - (G0) `XFam` is defined by cases on the shift, exactly as in the file. It carries the product module structure, and its two equations `XFam_zero`/`XFam_succ` hold by `rfl`.
  - (G1) `G1_pos` and `G1_zero`. They follow from C16 `T1`/`T2`, where the exponents are natural numbers equal to the pooled clocks.
  - (G2) `G2`, from C16 `T1`, `T2`, `T2_empty` and (S2), reindexing by `Int.toNat`. When `I = ∅`, the product over the empty index set is collapsed.
- **Part M** (`Theorem.lean`):
  - (M1) `M1`: C32 `T3`, then (G2) on each factor. A factor has `m λ n ≥ 1`, so `λ ∈ L n`, so `λ ≥ 1` by C31 (M3).
  - (M2) `M2`: C32 `T2`, then (G2).
  - (M3) `M3_support`, `M3_shift`, `M3_self`, `M3_zero`.

**Hypotheses.** All statements match the file. In `M3_self` the hypothesis `1 ≤ n` is not needed; it is kept as in the file and the docstring says so. Every docstring names its part of C33.

The Properties table has one definition row (`XFam`) and five property rows (Part S, Part G, M1, M2, M3), all marked proved.

# Summary of changes for run 7a8f97ec-66ef-4c37-aa2c-22409ac329c0
I formalized and proved every statement of `C32_theorem_38_the_groups_of_the_families.md` in a new folder, `RequestProject/Families/`, namespace `Families`. `lake build RequestProject.Families.All` succeeds with no warnings. The folder has no `sorry`, no new axiom and no `native_decide`. `#print axioms` on B0b, B1, B1a, B1b, B2, B2Z, Q0, Q1, Q2, T1, T2 and T3 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files (6 of them); C1–C31 are unchanged.

**Reuse.** Nothing listed in the Setting is redefined. The objects of C11, C12, C13, C14, C16, C17, C18, C20, C21, C28, C29, C30 and C31 are used directly, including C12's `thetaEquiv`/`A2_theta_comp_F`, C20's `Doubling.B1`, and C31's `D2`, `M3` and `le_of_mem_L`.

**Encodings** (described in each file's docstring and in `Families/All.lean`):
- A vector of a lattice `M` is `M.ι → A`; a vector of the tower is an element of `⨁ _ : Dance.Idx ds, A`, read through its coordinates.
- "`X ≅ Y`" is `Nonempty (… ≃ₗ[A] …)` or `Nonempty (… ≃+ …)`, as written in the file. Explicit equivalences are also given.
- `ℤ_[2]` is `PadicInt 2`.

**Results**
- **B0** (`Digits.lean`): `ds` is defined by well-founded recursion. Its three equations are `ds_zero`, `ds_odd` and `ds_even`; (B0b) is `B0b`.
- **B1** (`Tower.lean`):
  - `B1` is the existence statement, with properties (a) and (b).
  - `Theta A λ` is a chosen equivalence, with `B1a` and `B1b`.
  - The proof is by strong induction, as in the sketch. In the odd case `b_e n ↦ embΦ e (Θ n)`. In the even case `b_a ⊗ b_e n ↦ embVΦ a e (Θ n)`, followed by C12's `theta`.
- **B2** (`Group.lean`): `sigL` is the operator of the file. `sigEquiv` is the explicit equivalence, built from `Θ λ` and the identification `m ↦ m ι_0`; `B2` and `B2Z` are the statements.
- **Q** (`Quot.lean`):
  - `Q0`.
  - `Q1`, written in the componentwise form of C18 `C1`. It also comes in a general form for lists `l.map f` (`dsumMap_exists`).
  - `Q2`, with the explicit `isoEquiv`.
- **T** (`Theorem.lean`):
  - `T1`, with the explicit `T1equiv`, under the hypotheses of C30 (A1).
  - `T2`, which is Theorem 3.8 over `ℤ_[2]`. The hypotheses come from C28 `Lift2.Z1` and C21 `C3_hyp`.
  - `T3`, the multiplicity form. It is obtained from T2 by reindexing the positions of `L n` by entry and by rank among equal entries.

**Hypotheses.** In (B2) and (B2Z) the hypothesis `1 ≤ α` is kept as in the file but is not used. Both `sigL` and `Dance.pσ` carry the same factor `2^(α−1)`, so the statement holds for every `α`; the docstrings say this. Every hypothesis of T1 is used (through C31 (D2)).

Every docstring names its part of the file. The Properties table has 2 definition rows (`ds`, `sigL`) and 8 property rows (B0, B0b, B1, B2/B2Z, Q0–Q2, T1, T2, T3), all marked proved.

# Summary of changes for run 148c191c-56d2-47c9-b1e0-6a48ac5750ad
I formalized and proved every statement of `C31_theorem_36_the_family_decomposition.md` in a new folder, `RequestProject/FamDec/`, namespace `FamDec`. `lake build RequestProject.FamDec.All` succeeds. The folder has no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on M3, M4, P1, L1–L4, D3 and Z1 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added four new files (`Mult.lean`, `Perm.lean`, `Decomp.lean`, `All.lean`). C1–C30 are unchanged.

**Reuse.** Nothing listed in the Setting is redefined. I used the C18–C30 objects directly, including C29's `T`, `tpow`, `T_zero`, `T_odd`, `T_even`, `tpow_succ` and `T1`, and C30's `A1`, `K1`, `dsumList` and the explicit isomorphisms behind (K4a), (K4c), (K4d) and (K4e). Some listed items turned out not to be needed and are not used: C20 `D3`, `lemma35Iso`, `HasDeltaFilt`/`HasNablaFilt` by name, (K2), (K3) and (K4b).

**Encodings** (described in the docstrings and in `FamDec/All.lean`):
- A formal sum \(\sum_\lambda c_\lambda[\lambda]\) is a `List ℕ` with `c` copies of `λ`. Order is irrelevant: lists are compared up to `List.Perm`. The paper's `λ` is written `lam`.
- `Vdot` is defined by well-founded recursion on `n + 1` and `n / 2`. The three equations of (M1) are proved as `Vdot_zero`, `Vdot_odd` and `Vdot_even`.
- `L 0 = [0]`, `L (n+1) = (L n).flatMap Vdot`, and `m lam n = (L n).count lam`.
- "`X ≅ Y`" means `Nonempty (Doubling.Iso X Y)`.
- The hypotheses of C30 (A1) are explicit arguments.
- `ℤ_[2]` is `PadicInt 2`.

**Results**
- **Part M** (`Mult.lean`): (M1); (M2); (M3) as `M3` together with `mem_L_zero`; (M4) as `M4`. M4 comes from a general lemma: any list of numbers below `k` is a permutation of its count-replicate expansion.
- **Part L** (`Mult.lean`): `L1`–`L4`. The proof goes through the recursions `m 2 (n+1) = m 1 n` and `m 1 (n+1) = m 0 n + 2·m 2 n`, which follow from counting `1`, `2` and `λ+1` in `Vdot λ`.
- **Part P** (`Perm.lean`): `P1` (induction on the permutation, using `dsumComm`, `dsumAssoc` and `dsumIso`) and `P2` (induction on the list, using (K4a)). Both hold over any commutative ring.
- **Part D** (`Decomp.lean`):
  - `D1` by strong induction on `λ`, as in the sketch.
  - `D2` by induction on `n`, using `tensorVIso`, (K4c), D1 and P2.
  - `D3` from D2, M4 and P1.
- **Part Z** (`Decomp.lean`): `Z1_D1`, `Z1_D2`, `Z1_D3` and the combined `Z1`. The hypotheses come from C28 `Z1` and C21 `C3_hyp`.

**Unused hypotheses.** In (L2) and (L3) the hypothesis `1 ≤ n` is not needed; it is kept as in the file and noted in the docstrings. `m_self` proves `m n n = 1` for every `n`. In (L4), `1 ≤ n` is needed, since `m 2 0 = 0`. Every hypothesis of (A1) is used in Part D.

Every docstring names its part of the file. The Properties table has 2 definition rows (`Vdot`, and `L`/`m`) and 8 property rows (M3, M4, P1/P2, D1, D2, D3, Lemma 3.7, Z1), all marked proved.

# Summary of changes for run dbbc5c96-f532-4e48-b1dd-d5a7a1dca1da
I formalized and proved every statement of `C30_the_step_of_theorem_36.md` in a new folder, `RequestProject/Step36/`, namespace `Step36`. `lake build RequestProject.Step36.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on W1, W2, A1, Z1 and K1–K4 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files (4 of them); C1–C29 are unchanged.

**What is reused.** Nothing in the Setting is redefined. The objects from C18–C29 are used directly, plus two C23 results not on the list: `distribLeftIso` and `P8`.

**Encodings** (described in each file's docstring and in `Step36/All.lean`):
- A vector of `M` is `M.ι → A`, with `δ_i = Pi.single i 1`.
- An isomorphism is a `Doubling.Iso`. "`X ≅ Y`" means either an explicit `Iso` (a `def`) or `Nonempty (Iso X Y)`.
- "Weight-preserving" is C25's `IsWtPres`. Over `B` it refers to `baseChange φ _`, which keeps the weights of the lattice over `A`.
- In (A1), "reduces to `lemma35Iso`" means `bc φ e.hom.toLin = (lemma35Iso φ h2 N).hom.toLin`, and the same for `inv`.
- `ℤ_[2]` is `PadicInt 2`.

**Results**
- **Part W** (`PartW.lean`):
  - `himg_wt` is the finite check on the eight rows of `himg`. `qWt q` is the target weight minus the common term \(2\,\mathrm{wt}_N(i)\).
  - `W1` follows from `himg_wt` through `lemma35Iso_single`.
  - `W2` follows from `W1` by C28 `isWtPres_inverse`.
- **Part A** (`PartA.lean`): `A1` is proved as in the file: C29 `T3`, then (W1) and (W2), then C28 `C3` with `ē = lemma35Iso φ h2 N`.
- **Part K** (`PartK.lean`):
  - (K1) `tensorVOneIso` (with its action on basis vectors) and `K1`, which includes `tensorV (one A) ≅ phi (one A)`.
  - (K2) `phiDsumIso` is C23 `isoOfReindex` along `Equiv.prodSumDistrib`. The operators commute because `1 ⊗ inl` and `1 ⊗ inr` are the morphisms `phiHom inlHom` and `phiHom inrHom`. `K2` gives the image of every basis vector, in both directions.
  - (K3) `dsumZeroIso`, `zeroDsumIso`, `tensorVZeroIso`, `phiZeroIso` and `K3`.
  - (K4) `dsumList`, with `dsumList_nil` and `dsumList_cons` as theorems, and:
    - (a) `K4a`;
    - (b) `K4b` (stated with `List.Forall₂`) and `K4b_get` (same length and `L.get k ≅ L'.get k`);
    - (c) `K4c`, (d) `K4d`, (e) `K4e`.
    - Each also comes with an explicit isomorphism `def`.
- **Part Z** (`PartA.lean`): `Z1_W1`, `Z1_W2`, `Z1_A1` and the combined `Z1`, for `φ = PadicInt.toZMod`. The hypotheses come from C28 `Z1` and C21 `C3_hyp`.

**Hypotheses**
- Every hypothesis of `A1` is used. `h2` could be derived from `H2 φ`, but it is kept as in the file.
- Statements in Part K that do not mention `phi` hold over any commutative ring.
- The optional weight-preservation of the Part K maps (C25 (P1)) is not restated.

Every docstring names its part of the file. The Properties table has 8 property rows (W1, W2, A1, K1, K2, K3, K4, Z1), all proved, and one definition row (`dsumList`).

# Summary of changes for run c29eb434-acc1-4f50-a779-aecfa26ceab3
I formalized and proved every statement of `C29_filtrations_and_dance_lattices.md` in a new folder, `RequestProject/Filt/`, namespace `Filt`. `lake build RequestProject.Filt.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on S1, S2, I1, I2, E1, E2, E3, V1, V2, T0, T1, T2, T3, `T3_T` and Z1 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files (6 new files); C1–C28 are unchanged.

**What is reused.** Nothing from the Setting is redefined:
- C18: `DPLattice`, `Hom`, `H`, `delta`, `nabla`, `one`, `V`, `tensorV`, `T5_*`.
- C19: `Hom.comp`, `ShortExact`, `S1`, `S2`, `S4` (and through them `fDelta`, `gDelta`, `fNabla`, `gNabla`).
- C20: `phi`, `phiHom`, `A3`, `Iso`, `Iso.ofInverse`, `Iso.symm`, `Iso.ofDataEquiv`, `deltaIso`, `nablaIso`, `OddUnits`.
- C22: `dsum`, `inlHom`, `sndHom`. C23: `tensorVHom`, `tensorVHom_bvec`.
- C25: `IsWtPres`, `P1`. C27: `HasDeltaFilt`, `HasNablaFilt`, `G7`, `zeroL`, `F2`. C28: `isWtPres_inverse`.

A few listed objects were not needed and are not used: `A2`, `Iso.trans`, `tensorVHom_id`, `tensorVHom_comp`, `inrHom`, `fstHom`, `dsumHom`.

**Encodings** (each file's docstring and `Filt/All.lean` describe them):
- In (S1)/(S2) the new lattice has basis a finite type `κ` with decidable equality and weights `wK`. Weight preservation of `j`, `p`, `q`, `s` is the raw form of `IsWtPres`. Stability is stated as `X.Fd r (j x) ∈ range j`, or `x ∈ ker q → X.Fd r x ∈ ker q`, and the same for `Ed`.
- [char 0] means `[IsDomain A] [CharZero A]`; [Φ] adds `[OddUnits A]`.
- `T` is defined by well-founded recursion: `T (n+1)` is `phi (T (n/2))` for even `n` and `tensorV (phi (T (n/2)))` for odd `n`. `tpow` is defined by ordinary recursion.
- `ℤ_[2]` is `PadicInt 2`.

**Results**
- **Part S** (`Sub.lean`): `sub` / `subHom` / `S1` and `quot` / `quotHom` / `S2`. The basis, weights and operators are exactly those of the file, and `j`, `q` are morphisms.
- **Part I** (`PartI.lean`): `I1` (both filtrations) and `I2` (`one A` and `V A` have both filtrations).
  - In I1, the case where `X` is empty splits by the ring. Over a nontrivial ring the isomorphic lattice is also empty. Over the zero ring every lattice has both filtrations, which is proved directly.
- **Part E** (`PartE.lean`):
  - `E1` follows the sketch: induction on the filtration of `Q`, with the sub-lattice `K = g⁻¹(range f')` built through (S1) from the C27 (G7) sections. The maps are `j(u,v) = f u + σ(f' v)` and `p x = (ρ(x − σ f' ρ' g x), ρ' g x)`.
  - `E2` uses the dual construction, by induction on the filtration of `N'` with the quotient lattice of (S2).
  - `E3` gives the direct-sum statements for both filtrations.
- **Part V** (`PartV.lean`):
  - `V1` [char 0]. `tensorVHom f` agrees with C20's `phiLin f`, so it is exact. `V ⊗ Δ(l)` and `V ⊗ ∇(l)` are handled with C19 (S1)/(S2) for `l ≥ 1` and (S4) for `l = 0`.
  - `V2` [Φ] uses `A3`, `deltaIso` and `nablaIso`.
- **Part T and Z** (`PartT.lean`):
  - `T0`: the defining equations `T_zero`, `T_odd`, `T_even`, `tpow_zero`, `tpow_succ` as theorems.
  - `T1` [Φ], `T2` [char 0], `T3` [Φ], plus `T3_T` for `N = T l`.
  - `Z1`: T1–T3 for `ℤ_[2]`.

**Hypotheses.** Every hypothesis of the stated results is used. The [char 0] assumptions are needed only to get weight preservation from C25 (P1).

Every docstring names its part of the file. The Properties table has 3 definition rows (`sub`, `quot`, `T`/`tpow`) and 14 property rows for C29, all marked proved.

# Summary of changes for run 848f2784-fc10-4f24-a312-d459c479b81a
I formalized and proved every statement of `C28_lifting_mod_2_and_corollary_34.md` in a new folder, `RequestProject/Lift2/`, namespace `Lift2`. `lake build RequestProject.Lift2.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on D1–D3, L0–L2, C1–C3, Z1, `Z2_L2` and `Z2_C3` shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C27 are unchanged.

**What is reused.** Nothing listed in the request is redefined. I use C18's `DPLattice`, `Hom` and `H`; C19's `Hom.ext'`; C20's `Iso` and `Iso.ofInverse` (which includes `Hom.ofInverse`); C21's `bc`, `bc_comp`, `bc_id`, `bc_add`, `bc_smul`, `bc_single_apply`, `baseChange` and `bcHom`; C25's `IsWtPres`; and C27's `Lin`, `Pair`, `IsCocycle`, `G2`, `d`, `G4`, `HasDeltaFilt`, `HasNablaFilt` and `V4`, plus a few existing C27 weight lemmas.

**Encodings** (each file's docstring and `Lift2/All.lean` describe them):
- **Hypotheses:** each is an explicit proposition passed as an argument: `H1 φ` (surjective), `H2 φ` (`φ a = 0 ↔ ∃ b, a = 2 * b`), `H3 A` (no 2-torsion), and `OneAddTwoUnit A` (every `1 + 2a` is a unit, the hypothesis of (C1)).
- **Weight-preserving maps over `B`:** `IsWtPres` with respect to `baseChange φ M` and `baseChange φ N`, which carry the weights of `M` and `N`.
- **"Invertible":** `IsUnit u` in `Module.End A (ι → A)`, together with `Function.Bijective u`.
- **Isomorphisms:** stated with both underlying maps.
- **Part Z:** `ℤ_[2]` is `PadicInt 2`, and `φ` is `PadicInt.toZMod`.

**Results**
- **Part D** (`Basic.lean`):
  - `D1`: there is a unique `U` with `T = 2 • U`, and `U` is weight-preserving whenever `T` is.
  - `D2`: if `2 • c` is a cocycle, so is `c`. Each equation of (G2) for `2 • c` is twice the same equation for `c`, so it cancels by (H3).
  - `D3`: there is a cocycle `δ` with `d φ0 = 2 • δ`, obtained from G4 and D2.
- **Part L** (`PartL.lean`):
  - `L0`: the entrywise lift.
  - `L1`: a weight-preserving `h` with `d h = 0` is a morphism.
  - `L2`: `h = φ0 − 2 • ψ`, with `d ψ = δ` from C27 (V4). The conclusion gives both `bc φ h.toLin = h̄.toLin` and `bcHom φ h = h̄`.
- **Part C** (`PartC.lean`):
  - `C1`: `det(1 + 2W) = 1 + 2c`, shown by reducing modulo the ideal `2A`.
  - `C2`: if `bc φ u = 1`, then `u` is bijective.
  - `C3` (Corollary 3.4): the inverse of the lift `f` is built with `Iso.ofInverse`. It is weight-preserving and reduces to `ē.inv`.
- **Part Z** (`PartZ.lean`): `Z1`, `Z2_L2` and `Z2_C3`.

**Hypotheses used by each statement**
- D1: (H2) and (H3). Its existence half, `D1_exists`, needs only (H2).
- D2: (H3). D3: (H2) and (H3).
- L0: (H1). L1: none. L2: (H1), (H2) and (H3).
- C1: only the hypothesis of (C1).
- C2: (H2) and the hypothesis of (C1). The file also lists (H3), but it is not needed, so I dropped it; this makes C2 more general than stated, and the docstring says so.
- C3: all four.

Every docstring names its part of the file. The Properties table has one definition row (the hypotheses) and 11 property rows for C28, all marked proved.

# Summary of changes for run 51e14db3-d9b5-4080-93dc-46c7cf45bfbd
I formalized and proved every statement of `C27_cocycles_and_filtrations.md` in a new folder, `RequestProject/Cocycle/`, namespace `Cocycle`. `lake build RequestProject.Cocycle.All` succeeds with no errors or warnings. The folder contains no `sorry`, no axiom declarations and no `native_decide`. `#print axioms` on G2–G7, F2 and V1–V6 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C26 are unchanged.

**What is reused.** Nothing listed in the request is redefined:
- from C18: `DPLattice`, `IsDP`, `Hom`, `delta`, `nabla`, plus `InWt`;
- from C19: `Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`;
- from C20: `Iso`, built with `Iso.ofInverse`;
- from C25: `IsWtPres`, `pr`, `HasWt`, `P1`, `P2_*`, `E1`, `E2`, `K_vec`, `comm_prW_of_shift`, `exists_section`, `exists_retraction_of_section`.

`E3` is not used: V5 gets the weight-preservation hypotheses from `P1` directly.

**Encodings** (each file's docstring and `All.lean` describe them):
- A vector is a function `ι → A`, with `δ_i = Pi.single i 1`.
- `Lin M N` is the type of linear maps between the two vector spaces. A pair `c = (cF, cE)` lives in `Pair M N = (ℕ → Lin M N) × (ℕ → Lin M N)`.
- On `N.ι ⊕ M.ι`, the vector `(u, v)` is `Sum.elim u v`. `blk a b d` is the block upper-triangular operator `(u, v) ↦ (a u + b v, d v)`.
- `IsCocycle c` means `IsDP` holds for the glued data. `glue M N c hc` is the glued DP-lattice.
- `IsCoboundary c` means `∃ ψ, IsWtPres ψ ∧ d ψ = c`.
- Isomorphisms are stated together with their underlying maps.

**Results**
- **(G0)** `zeroL`; **(G1)** `glue`.
- **(G2)** `G2 : IsCocycle c ↔ CocycleEqs c`, where `CocycleEqs` lists (W), (P0), (P1) and (K) as in the file, with the binomial in (K) taken at `M.wt i`. `cocycles M N` is the submodule of cocycles.
- **(G3)** `incl`, `proj` and `G3`.
- **(G4)** `G4`: conjugating by `[[1, ψ], [0, 1]]`, through a general lemma `isDP_transport` that carries `IsDP` across a weight-preserving map intertwining the operators.
- **(G5)** `G5`: coboundary ⇔ `proj` has a section ⇔ `incl` has a retraction. The weight-diagonal part is `wd ψ'`, and `wd_eq_sum` shows it equals `Σ_w pr w ∘ ψ' ∘ pr w`.
- **(G6)** `G6a` (with `G6a_pcomp`, `G6a_qcomp`, `G6a_d_pcomp`, `G6a_d_qcomp`), `G6b` and `G6c`.
- **(G7)** `G7` gives `σ`, `ρ`, the cocycle `ρ ∘ X.Fd r ∘ σ` / `ρ ∘ X.Ed r ∘ σ`, and `θ : Iso X (glue …)`, with `θ x = (ρ x, g x)`, `θ⁻¹(u, v) = f u + σ v`, `θ ∘ f = incl` and `proj ∘ θ = g`. `G7_split` is the consequence that every such sequence splits.
- **(F1)** The inductive predicates `HasDeltaFilt` and `HasNablaFilt`; **(F2)** `F2`.
- **(V1)–(V6)** `V1`, `V2`, `V3`, `V4` (cocycle vanishing and splitting), `V5` (characteristic zero, no weight hypotheses) and `V6` (`ℤ_[2]`).

**Hypotheses.** One hypothesis is unused: in `G6a`, the weight preservation of `ψ` in the identities `d(ψ ∘ i) = (dψ) ∘ i` and `d(j ∘ ψ) = j ∘ dψ`. I kept it as the file states it; the identities hold for every linear `ψ`, and the docstring says so. Every other hypothesis is used.

**Files**
- `Basic.lean`: Setting, G0–G2.
- `Weights.lean`: auxiliary weight lemmas.
- `PartG.lean`: the G2 submodule, G3, G4.
- `PartG56.lean`: G5, G6.
- `PartG7.lean`: G7.
- `PartFV.lean`: Parts F and V.
- `All.lean`: index.

The Properties table has 3 definition rows for C27 and 16 property rows, all marked proved.

# Summary of changes for run 4b5ee80c-bea4-4181-bf58-c93572a5e438
I formalized and proved every statement of `C26_lifting_and_extension.md` in a new folder, `RequestProject/LiftExt/`, namespace `LiftExt`. `lake build RequestProject.LiftExt.All` succeeds with no errors or warnings. The folder contains no `sorry`, no `axiom`, no `admit` and no `native_decide`. `#print axioms` on `L0`, `L1`, `X1_gen`, `X1` and `B1`–`B5` shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C25 are unchanged.

**What is reused.** Nothing listed in the request is redefined. From C18 I use `DPLattice`, `Hom`, `delta`, `nabla`, `weylWt`, `deltaF` and `deltaE`. From C19 I use `Hom.id`, `Hom.comp`, `Hom.ext'` and `ShortExact`; C20's `Iso` enters through C25's isomorphisms. From C25 the files use:
- the objects `IsWtPres`, `pr`, `HasWt`, `trM`, `dual`, `dualHom`, `isoDualDual`, `isoDualDelta`, `isoDualNabla`, `sW` and `sWHom'`;
- the results `P1`, `P2_*`, `D5` and `W1`;
- the auxiliary lemmas `K_vec`, `sW_single`, `trM_comp`, `trM_trM`, `dualHom_wtPres` and `exists_retraction_of_section`.

**Encodings** (each file's docstring and `All.lean` describe them):
- A vector is a function `M.ι → A`, with `δ_i = Pi.single i 1`.
- The only new definition is `WtIn K a b` ("`K` has weights in `[a, b]`"), meaning `∀ i, a ≤ K.wt i ∧ K.wt i ≤ b`.
- The duality is C25's `dual` / `dualHom`, together with its identity isomorphisms.
- `ℤ_[2]` is Mathlib's `PadicInt 2`.

Every docstring names its part of the file.

**Results**
- **Part L** (`Basic.lean`):
  - `L0` is (L0).
  - `L1` is Lemma W in lifting form. It gives `x` of weight `l` with `g x = h δ_0`, and a lift `h'` with `h'.toLin = sW x` and `Hom.comp g h' = h`.
  - `L1_W4` checks that C25 (W4) is a special case.
- **Part X** (`PartX.lean`): I proved the more general statement the file invites. `X1_gen` allows `K` to have weights in `[−l−1, l+1]`, and `X1` (with `[−l, l]`) follows from it. Both give `x`, a linear `ρ` with `f ∘ ρ = id − sW x ∘ g` (and `ρ ∘ f = id`), and `k'` with `k'.toLin = k ∘ ρ` and `Hom.comp k' f = k`. The delicate point (`k'` commuting with `E^{(s)}`) works as in the file's sketch:
  - two maps agree if they agree on the range of `f` and on the vectors `F^{(r)} x`;
  - for `j < s`, `E^{(s−j)} x = f y_j` with `y_j` of weight `l + 2(s−j)`, so `k y_j = 0`;
  - the term `j = s` is killed because `ρ ∘ sW x = 0`.
- **Part B** (`PartB.lean`):
  - `B1` (lifting) and `B2` (extension) hold for all `l m`. Each is split into `_le` (`m ≤ l`, by (L1) or (X1)) and `_gt` (`m > l`, by (D5), the duality isomorphisms and transposing back with `trM_comp`/`trM_trM`, then (X1) or (L1)).
  - `B3` (with `B3_lift` and `B3_ext`) covers a domain of characteristic zero with no weight hypotheses, via (P1).
  - `B4` is the case `ℤ_[2]`.
  - `B5` obtains the section and the retraction of C25 (E2) from `B1` and `B2` with `Hom.id`.

**Hypotheses.** Every hypothesis of every statement is used; none is extra.

The Properties table has one definition row (`WtIn`) and 9 property rows (L0, L1, X1, X1_gen, B1–B5). All 9 properties are marked proved.

# Summary of changes for run aec9cbab-aaaf-46fb-84f2-8aa551319c14
I formalized and proved every statement of `C25_lemma_W_and_ext.md` in a new folder, `RequestProject/LemmaW/`, namespace `LemmaW`. `lake build RequestProject.LemmaW.All` succeeds with no errors or warnings. The folder contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on P1–P3, D1–D5, W1–W5 and E1–E4 shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C24 are unchanged.

**Reused, not redefined:**
- from C18: `DPLattice`, `IsDP`, `Hop`, `H`, `Hom`, `delta`, `nabla`, `weylWt`, `deltaF`, `deltaE`, `nablaF`, `nablaE`, plus the existing lemmas `IsDP.dual`, `deltaF_eq` and `deltaE_eq`;
- from C19: `Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`;
- from C20: `Iso`, `Iso.ofInverse`.

Every docstring names its part of the file, and `All.lean` is an index that also lists the encodings.

**Encodings**
- **Vectors:** a vector is a function `M.ι → A`, and `δ_i = Pi.single i 1`.
- **Weights:** `IsWtPres φ` means `φ (δ_i) j = 0` whenever `M.wt i ≠ N.wt j`. `pr M w` keeps the coordinates of weight `w`, and `HasWt M w z` means `pr M w z = z`.
- **Transpose:** `trM φ = Matrix.toLin' (LinearMap.toMatrix' φ)ᵀ`, so `trM φ (δ_k) i = φ (δ_i) k`.
- **Extensions:** an extension is a `ShortExact f g`. It splits when `g` has a section, or `f` a retraction, in `Hom`.
- **Dual:** `dual M` has the same basis and weights, with `F^{(r)} = trM (M.Ed r)` and `E^{(r)} = trM (M.Fd r)`. `dualHom f` has underlying map `trM f.toLin`.
- **Isomorphisms:** an isomorphism is a `Doubling.Iso`, with underlying maps `.hom.toLin` and `.inv.toLin`.
- **Section:** `sW x` is the linear map `z ↦ Σ_r z_r • F^{(r)} x`, so `sW x (δ_r) = F^{(r)} x`.

**Results**
- **Part P** (`Basic.lean`):
  - `P1_H` gives `(N.wt j − M.wt i)·f(δ_i) j = 0` over any commutative ring; `P1` concludes over a domain of characteristic zero.
  - `P2` covers weight-preserving maps, `F^{(r)}` and `E^{(r)}`.
  - `P3` gives the weights of an extension.
- **Part D** (`Dual.lean`):
  - **D1:** `dual`, with `IsDP` and the basis-vector formulas. The delicate point, (K) for the dual, is C18's `IsDP.dual`, which already carries out the basis-vector check with the weight shift; C18's `tr` is definitionally `trM`.
  - **D2:** `dualHom`, `dualHom_id`, `dualHom_comp`, `dualHom_wtPres`.
  - **D3:** `isoDualDual : dual (dual M) ≅ M`, both maps `LinearMap.id`.
  - **D4:** `D4_delta` and `D4_nabla` show the bases, weights and operators agree. `isoDualDelta` and `isoDualNabla` have both maps the identity.
  - **D5:** the dual of a short exact sequence is short exact. A surjection onto a free module has a linear section, which gives a linear retraction of `f`; then transpose.
- **Part W** (`PartW.lean`):
  - `W1` and `W2`.
  - `W3`: `sWHom`, whose underlying map is `sW x`, is a `Hom (delta A l) X` and a section of `g`. The proof uses (K) extended linearly to vectors of one weight (`K_vec`).
  - `W4` is Lemma 3.2; `W5` is the characteristic-zero version.
- **Part E** (`PartE.lean`):
  - `E1`: a section exists iff a retraction exists.
  - `E2` is Lemma 3.3's first sentence, with both cases: `E2_le` (m ≤ l) and `E2_gt` (m > l, via D5, D4, W4, D2 and D3), then E1.
  - `E3` is the characteristic-zero version; `E4` is the case `ℤ_[2]`.

**Hypotheses:** `W1` is stated without the weight-preservation hypothesis on `f` and without the bound on the weights of `N`. It doesn't need them, so it is slightly more general than the file. Every other statement uses all of its hypotheses.

The Properties table has 2 definition rows and 17 property rows for C25. All 17 properties are marked proved.

# Summary of changes for run 7a4cf945-43a0-4d02-b176-dc91253b5163
I formalized and proved every statement of `C24_lemma_35_second_sentence.md` in the new folder `RequestProject/Lemma35b/`, namespace `Lemma35b`. Both files build without errors or warnings. Neither contains `sorry`, `axiom`, `admit` or `native_decide`. `#print axioms` shows that every main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. No file in the C1–C23 folders was changed.

**Files**
- `RequestProject/Lemma35b/Basic.lean` covers Parts I, B and F.
- `RequestProject/Lemma35b/PartL.lean` covers Part L.

Each file's docstring explains how the objects are encoded, and every docstring names the part of the C24 file it corresponds to.

**Encodings.** Everything uses the existing C18–C23 objects, as you asked:
- A DP-lattice over `A` is a finite free module `M.ι → A` with weights and divided-power operators.
- An `Iso` has `hom`/`inv` morphisms, whose underlying linear maps are `.toLin`.
- `tensor M N` has basis `M.ι × N.ι`, and `dsum M N` has basis `M.ι ⊕ N.ι`.
- `baseChange φ` and the Frobenius twist `frob h2` keep the same basis.
- Basis vectors are written `Pi.single i 1`.

**Results.** Each isomorphism is stated together with its underlying linear maps.
- **Part I:** `Iso.refl`, plus how `.toLin` behaves under `trans` and `symm` (I1). `dsumComm` (I2) and `dsumAssoc` (I3) are given with their maps as reindexings and their values on basis vectors.
- **Part B**, for any ring homomorphism `φ`:
  - (B1) base change commutes with `kron` and with finite sums, and `bcTensorIso` is the identity;
  - (B2) `bcDsumIso` is the identity;
  - (B3) `bcIso` is given by `bcHom`/`bc`.
- **Part F:** (F1) `frob (M ⊗ N) ≅ frob M ⊗ frob N` and (F2) `frob (dsum M N) ≅ dsum (frob M) (frob N)`, both by the identity, with weights and operators equal. (F3) `frobIso` has the same underlying maps as the original isomorphism.
- **Part L:**
  - (L4) `isoL4 h2 X : V^{⊗3} ⊗ X ≅ (V ⊗ V^{[1]}) ⊗ X ⊕ (V ⊗ X)^2`, built as the composite listed in the file. Theorem `L4` gives its value on each basis vector `δ_{(a,(b,(c,x)))}` as the sum over the terms of `hL(δ_{(a,(b,c))})`, sent on by `L4img`.
  - (L5) `L5` is the `Nonempty Iso` statement. `lemma35Iso` is the explicit chain of steps 1–8, and `lemma35Iso_single` gives its basis-vector formula exactly as in the file (through `L5img`).
  - (L6) the case `ℤ_[2] → ZMod 2`, using C21's `C3_hyp`.

**Notes on hypotheses**
- `L5`'s statement does not mention `h2 : (2 : B) = 0`, but the hypothesis is used: it is needed to build `lemma35Iso`.
- The weight and operator equalities in F1 and F2 don't use `h2`. It appears only because `frob` needs it.

The Properties table is up to date: all 13 C24 entries (I1–I3, B1–B3, F1–F3, L4, L5, the explicit L5 isomorphism, L6) are marked proved and point to these two files.

# Summary of changes for run 4cd90d1b-7aa1-4d18-b5b8-b05220aae147
I formalized and proved every statement of `C23_the_tensor_product.md` in a new folder, `RequestProject/Tensor2/`, namespace `Tensor2`. `lake build RequestProject.Tensor2.All` succeeds with no errors or warnings. The folder contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on `P1`–`P8`, `tensor`, `tensorIso` and `tensorVIso` shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C22 are unchanged.

**Reused, not redefined:** from C18, `DPLattice`, `IsDP`, `H`, `Hom`, `V`, `tensorV`, `bvec` and `one`; from C19, `Hom.id` and `Hom.comp`; from C20, `Iso`, `Iso.ofInverse` and also `Iso.ofDataEquiv`; from C22, `dsum` and `dsumHom`. No statement needed `slice`, `delta` or `nabla`, so they are not used. Every docstring names its part of the file, and `All.lean` is an index that also lists the encodings.

**Encodings**
- **Vectors:** a vector of a lattice `M` is a function `M.ι → A`, and `δ_i` is `Pi.single i 1`.
- **Pure tensors:** `tprod m n` is the function `(i,j) ↦ m i * n j`, so `δ_{(i,j)} = δ_i ⊗ δ_j`.
- **`f ⊠ g`:** `kron f g` is the linear map whose matrix is the Kronecker product of the two matrices. It satisfies the file's formula exactly (`kron_single_apply`), and `(f ⊠ g)(m ⊗ n) = f m ⊗ g n`.
- **Reindexing along a bijection `e`:** the map `f ↦ f ∘ e⁻¹`, which sends `δ_x` to `δ_{e x}`; its inverse is `g ↦ g ∘ e`.

**Results**
- **(P1)** `tensor M N` has basis `M.ι × N.ι`, weights `M.wt i + N.wt j`, and `F^{(r)} = Σ_{a=0}^{r} M.Fd a ⊠ N.Fd (r−a)` (likewise `E`). `P1` / `tensor_isDP` prove (W), (P0), (P1) and (K). (P1) uses Vandermonde over ℕ; (K) uses Vandermonde over ℤ (`Ring.add_choose_eq`) with an explicit reindexing of the four-fold sum. The coproduct formula on pure tensors is `tensor_Fd_tprod` / `tensor_Ed_tprod`.
- **(P2)** `kronHom f g`, whose underlying map is `f ⊠ g`, is a `Hom`. It preserves identities and composites, and `tensorIso` has underlying maps `u.hom ⊠ v.hom` and `u.inv ⊠ v.inv`.
- **(P3)** `tensorVIsoTensor M : tensorV M ≅ V A ⊗ M`, with `LinearMap.id` both ways. The bases and weights agree, and C18's operators equal the tensor-product ones (`tensorV_Fd_eq`, `tensorV_Ed_eq`).
- **(P4)** `assocIso` reindexes along `((i,j),k) ↦ (i,(j,k))`.
- **(P5)** `distribRightIso` reindexes along `(inl i,k) ↦ inl (i,k)` and `(inr j,k) ↦ inr (j,k)`. `distribLeftIso` reindexes along `(i,inl j) ↦ inl (i,j)` and `(i,inr k) ↦ inr (i,k)`.
- **(P6)** `tensorVHom f`, with underlying map `id ⊠ f`, is a `Hom`, and `bvec e m ↦ bvec e (f m)`. It preserves identities and composites, and gives `tensorVIso`.
- **(P7)** `dsumIso`, with underlying maps `dsumHom u.hom v.hom` and `dsumHom u.inv v.inv`.
- **(P8)** `unitLeftIso` reindexes along `((),i) ↦ i`, and `unitRightIso` along `(i,()) ↦ i`.

For (P3), (P4), (P5) and (P8), the theorem states both underlying linear maps and their values on basis vectors in both directions. The statements are those of the file; none carries an extra or unused hypothesis.

The Properties table has a row for the `tensor` definition and one row each for (P1)–(P8); all eight are marked proved.

# Summary of changes for run 3f5c9bd7-bf19-43c6-bee9-5785f26ab6b1
I formalized and proved every statement of `C22_lemma_35_over_F2.md` in a new folder, `RequestProject/Lemma35/`, namespace `Lemma35`. `lake build RequestProject.Lemma35.All` succeeds with no errors or warnings. The folder contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on `S1`, `S2`, `L1`, `L2`, `L3` and the basis-table theorems shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C21 are unchanged.

**Reused, not redefined:** from C18, `DPLattice`, `IsDP`, `H`, `Hom`, `V`, `tensorV`, `delta` and `bvec`; from C19, `Hom.id` and `Hom.comp`; from C20, `Doubling.Iso` (and its `Hom.ofInverse`); from C21, `Twist.frob`. Every docstring names its part of the file, and `All.lean` is an index that also lists the encodings.

**Encodings**
- **Direct sum:** `dsum M N` has basis `M.ι ⊕ N.ι`, weights `Sum.elim M.wt N.wt`, and `F^{(r)}`, `E^{(r)}` acting blockwise through `blk f g z = Sum.elim (f (z ∘ inl)) (g (z ∘ inr))`. The blockwise map `f ⊕ g` is `dsumHom f g`.
- **Maps given on basis vectors:** `ofImg v` is the linear map sending the basis vector at `i` to `v i`.
- **`V^{⊗3}`:** `T3 B = tensorV (tensorV (V B))`. The word `e_1e_2e_3` is `w e_1 e_2 e_3`, the basis vector at `(e_1, (e_2, e_3))`.
- **`D`:** `D3 B = dsum (delta B 3) (dsum (V B) (V B))`. Its basis vectors `e_r`, `b_e`, `c_e` are `eD r`, `bD e`, `cD e` (at `inl r`, `inr (inl e)`, `inr (inr e)`).
- **`V ⊗ V^{[1]}`:** `VV1 h2 = tensorV (Twist.frob h2 (V B))`. The basis vector `b_e b'_{e'}` is `bb e e'`.

**Results**
- **(S1) `S1`:** proved over any commutative ring, giving `dsum`.
- **(S2) `S2`:** the inclusions `x ↦ Sum.elim x 0`, `y ↦ Sum.elim 0 y` and the projections `z ↦ z ∘ inl`, `z ↦ z ∘ inr` are `Hom`s; `f ⊕ g` is a `Hom`; and it preserves identities and composites.
- **(L1) `L1`:** `g` and `h` match the file's tables exactly (`g_basis`, `h_basis`). They are `Hom`s with `h ∘ g = Hom.id` and `g ∘ h = Hom.id`, so `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)` (`isoL1`), and `g(e_r) = F^{(r)}(000)`.
- **(L2) `L2`:** `u` and `u⁻¹` match the file's tables (`u_basis`, `uinv_basis`). They are mutually inverse `Hom`s (`isoL2`), and `u(e_r) = F^{(r)}(b_0 b'_0)`.
- **(L3) `L3`:** both isomorphisms exist for `B = ZMod 2`.
- **Extra:** `g_not_hom_int` proves the proof sketch's remark that over `ℤ`, `g` is not a `Hom`.

**Proof method:** commutation with `F^{(r)}` and `E^{(r)}` is checked coordinate by coordinate for `r = 1, 2, 3`. For `r = 0` it follows from (P0). For `r ≥ 4` both sides vanish, because every weight lies in `[−3, 3]`. Commutation with `H` holds because each basis vector is sent to a vector of the same weight.

**Hypotheses:** `h2 : (2 : B) = 0` is used for the `Hom` and inverse claims, and to form `V^{[1]}`. The basis tables and `g(e_r) = F^{(r)}(000)` hold without it. No hypothesis is otherwise unused.

**Build time:** most of the full build goes to `L1Comm.lean`, the coordinate check of `g` against `F^{(r)}` and `E^{(r)}`, which takes about 4 minutes.

The Properties table has rows for (S1), (S2), (L1), (L2) and (L3), all marked proved.

# Summary of changes for run 8d8b879c-b088-455b-8468-c77bb2fb55b9
I formalized and proved every statement of `C21_reduction_mod_2_and_the_twist.md` in a new folder, `RequestProject/Twist/`, namespace `Twist`. `lake build RequestProject.Twist.All` succeeds with no errors or warnings. The folder contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on `R0`–`R3`, `T0`–`T2`, `C0`–`C3` and `C3_hyp` shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C20 are unchanged.

The C18, C19 and C20 objects you listed are reused, not redefined, as are the closed formulas `phiFd_even` … `phiEd_odd_b0`. Every docstring names its part of the file. `All.lean` is an index that also lists the encodings.

**Encodings**
- **Base change of a linear map:** `bc φ f := Matrix.toLin' ((LinearMap.toMatrix' f).map φ)`, so `f^φ (δ_i) j = φ (f δ_i j)` (`bc_single_apply`).
- **Base change of a lattice and a morphism:** `M^φ` is `baseChange φ M`, with the same basis and weights and `F^{(r)} = bc φ (M.Fd r)`, `E^{(r)} = bc φ (M.Ed r)`. `f^φ` is `bcHom φ f`.
- **Frobenius twist:** `M^{[1]}` is `frob h2 M`, where `h2 : (2 : B) = 0`. Its weights are `2·wt`, and `F^{(r)} = frobOp M.Fd r` (`F^{(r/2)}` for even `r`, `0` for odd `r`); likewise for `E`. `frobHom h2 f` is the same linear map as `f`.
- **Isomorphism:** `Doubling.Iso`. The statements of (R3) and (C2) also say that both underlying maps are `LinearMap.id`.

**Results**
- **Part R** (any commutative rings `A`, `B` and any `φ : A →+* B`):
  - `R0`.
  - `R1`: proved by pushing each axiom through `bc`.
  - `R2`.
  - `R3`, with the explicit isomorphisms `VIso` and `tensorIso`.
- **Part T** (only `h2` assumed):
  - `T0` (Lucas at 2, negative `x` included): proved by induction on `x` in both directions with Pascal's rule.
  - `T1`: stated for raw DP data. `frob_data` gives the data of the twist and `H_frob` shows `H` acts as `2H`.
  - `T2`.
- **Part C:**
  - `C0`.
  - `C1`: the six formulas for every vector `n`, first checked on basis vectors and then extended linearly.
  - `C2` (Proposition 3.1 (c)), via `prop31Iso`.
  - `C3_hyp`: the instance check for `ℤ_[2]`, `ZMod 2` and `PadicInt.toZMod`, including `PadicInt.toZMod 2 = 0`.
  - `C3`.

**Generality and hypotheses**
- In (C0), oddness of the two families of `c_j` is proved for every `j`, not only for the ranges in the file.
- (C0) assumes only `[OddUnits A]`; `IsDomain` and `CharZero` are not needed there.
- In (C1)–(C3), `IsDomain` and `CharZero` are needed to form `Doubling.phi N`, and `OddUnits` is needed for `φ(⅟(2s−1)!!) = 1`.
- In (T2), `h2` is only needed to form the twists as DP-lattices; the proof that `f` commutes with them does not use it.
- No hypothesis is otherwise unused.

The Properties table has a setting row and one row each for (R0)–(R3), (T0)–(T2) and (C0)–(C3); all eleven property rows are marked proved.

# Summary of changes for run a60cc4f4-0386-4ab3-8afd-2b3b8a14a5f2
I formalized and proved every statement of `C20_the_doubling_functor.md` in a new folder, `RequestProject/Doubling/`, namespace `Doubling`. The whole project builds with no errors or warnings, and the new folder contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on every main theorem shows only `propext`, `Classical.choice` and `Quot.sound`. Only files in the new folder were added; C1–C19 are unchanged.

From C18 I reused `DPLattice`, `IsDP`, `H`, `Hom`, `one`, `V`, `bvec`, `delta`, `nabla`, `T5_delta_zero` and `T5_delta_one`, and from C19 `Hom.id`, `Hom.comp` and `ShortExact`; none of them is redefined. Every docstring names its part of the file. `All.lean` is an index that lists the encodings.

**Setting and encodings**
- **Ring:** `[IsDomain A] [CharZero A] [OddUnits A]`. The class `OddUnits` has one field, exactly `hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A)`.
- **`ℤ_[2]`:** the instance check is `padicInt_two_hodd`, plus `instance : OddUnits ℤ_[2]`.
- **Inverse double factorials:** \(⅟(2s−1)!!\) is `dfi s := Ring.inverse ((2s−1)‼)`, so `dfi 0 = 1` and \(⅟(2s+1)!! = \) `dfi (s+1)`.
- **\(\Pi_c\):** `piOp N S c` is the polynomial \(\prod_{j\in S}(4X + c_j)\) evaluated at the operator \(FE\). The index ranges of the file are `range s`, `range (s+1)` and `Icc 1 s`.
- **\(\Phi(N)\):** `phi N` has basis `Fin 2 × N.ι`, weights \(2w_i \pm 1\), and `b_e n` is `bvec e n`. `F^{(r)}` and `E^{(r)}` are defined on the basis vectors `b_e e_i` by exactly the seven closed formulas of the file, then extended linearly. The seven formulas are also restated as theorems (`phiFd_even`, …, `phiEd_odd_b0`).
- **Weight vectors:** "`n` of weight `w`" is C18's `InWt`.
- **\(\Phi\) on morphisms:** `phiHom f` is \(1 \otimes f\).
- **Isomorphism:** `Iso M N` is a pair of `Hom`s, one each way, whose `Hom.comp`s are `Hom.id`.

**Results**
- **Part A:** `A1` (the data satisfy `IsDP`, so `phi N : DPLattice A`), `A2` and `A3`. For (A1) I followed the file's sketch: I checked the recursions \(F^{(1)}F^{(r)} = (r+1)F^{(r+1)}\) and \(E^{(1)}E^{(r)} = (r+1)E^{(r+1)}\) and the relation \([E,F] = H\) from the closed formulas. A general lemma (`isDP_of_rec`) then derives (P1) and Kostant's formula (K) over a domain of characteristic zero.
- **Part B:** `B1`, `B2` (\(r! \cdot F^{(r)} = (F^{(1)})^r\), and the same for `E`) and `B3` (the `F` formulas for every vector `n`).
- **(D1) and (D2):** `D1`/`D1_iso` and `D2`/`D2_iso`. The maps `deltaMap` (with `c_R`) and `nablaMap` (with `d_R`) and their inverses are given explicitly. They are shown to be morphisms by checking \(F^{(1)}\), \(E^{(1)}\) and `H` directly on basis vectors, then extending to all divided powers by the recursions and cancellation in the domain. Weyl's theorem on complete reducibility is not used.
- **`d_R`:** it is defined in closed form, and `dN_rec` proves that it satisfies the file's recursion.
- **(D3):** `D3` and `D3'`, obtained from (D1) at \(\mu = 0\), C18's (T5) and functoriality of \(\Phi\).

**Hypotheses:** every hypothesis is used. The `IsDomain`, `CharZero` and `OddUnits` assumptions are needed to build `phi`, so every theorem that mentions `phi` carries them. The basis formulas themselves (`phiFd_even`, …) are stated without them. The odd-integer inverses are taken with `Ring.inverse`, so `dfi` and `piOp` need no hypothesis to be defined.

The Properties table has one row for the setting definitions and one row each for (A1), (A2), (A3), (B1), (B2), (B3), (D1), (D2) and (D3); all nine property rows are marked proved.

# Summary of changes for run 3209f52c-d440-404c-9809-39c063fbb3bc
I formalized and proved every statement of `C19_weyl_filtrations_of_V_tensor.md` in a new folder, `RequestProject/WeylFilt/`, namespace `WeylFilt`. The whole project builds with no errors or warnings, and the new folder contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all the main theorems shows only `propext`, `Classical.choice` and `Quot.sound`. Only files in the new folder were added; C1–C18 are unchanged.

From C18 I reused `DPLattice`, `IsDP`, `H`, `Hom`, `V`, `tensorV`, `bvec`, `delta`, `nabla`, `T5_delta_one` and `T5_nabla_one` without redefining them. `one` is not needed by any statement, so it is not used. As in your request, `V ⊗ M` is C18's `tensorV M`. Every docstring names its part of the file, and `All.lean` is an index that lists the encodings.

**Encodings** (`Basic.lean`, `Maps.lean`)
- **Lattices:** `Δ_A(l)` and `∇_A(l)` are C18's `delta A l` and `nabla A l`, with basis `Fin (l+1)`; the basis vector `e_r` (or `w_r`) is `Pi.single r 1`. In `V ⊗ M`, `b_e m` is `bvec e m`.
- **Parameter `m − 1`:** this is subtraction on `ℕ` (which stops at 0), so every statement that uses it assumes `m ≥ 1`.
- **Out-of-range basis vectors:** `ev l k` (with `k : ℤ`) is `e_k` when `0 ≤ k ≤ l` and `0` otherwise, matching the file's convention.
- **The four maps:** `fDeltaLin`, `gDeltaLin`, `fNablaLin` and `gNablaLin` are defined by their values on basis vectors, exactly as in the file, and extended linearly (`Basis.constr`). The basis formulas are restated as theorems (`…Lin_single`), and the file's case list for `gΔ` is `gDeltaLin_cases`. The corresponding morphisms are `fDelta`, `gDelta`, `fNabla` and `gNabla`.
- **Morphisms:** `Hom.id` and `Hom.comp` are the identity and composition.
- **Short exact sequence:** `ShortExact f g` means `f` is injective, `g` is surjective, and `range f = ker g`.

**Results** (all over an arbitrary commutative ring `A`)
- **(M1)** `M1_fDelta`, `M1_gDelta`, `M1_fNabla`, `M1_gNabla`: each map commutes with every `F^{(r)}`, every `E^{(s)}` and `H`. The proofs check the file's Pascal-type identities coordinate by coordinate.
- **(M2)** `M2`: the underlying maps of `Hom.id` and `Hom.comp` are the identity and the composite, composition is associative, and `Hom.id` is a unit on both sides.
- **(S1)** `S1` and **(S2)** `S2`: the two short exact sequences, for `m ≥ 1`. As in the file's sketch, `ker g ⊆ range f` is proved by explicitly constructing a preimage; no rank argument is used.
- **(S3)** `S3`: `fΔ(e'_0) = b_0 e_0`, and `range fΔ` is the `A`-span of the `F^{(R)}(b_0 e_0)` for `0 ≤ R ≤ m+1`.
- **(S4)** `S4` (with `S4_delta` and `S4_nabla` for the explicit maps `phiDelta`/`psiDelta` and `phiNabla`/`psiNabla`): there are morphisms both ways whose composites are the identities. They are built from `fΔ` and `g∇` at `m = 0`, which are bijective, together with C18's (T5) `Δ_A(1) = V = ∇_A(1)`.

**Generality and hypotheses**
- (M1) for `fΔ` and `g∇`, and (S3), hold for every `m`. This is more general than the file's `m ≥ 1`, so they carry no `m ≥ 1` hypothesis.
- (M1) for `gΔ` and `f∇`, and (S1) and (S2), assume `m ≥ 1`, and the proofs use it. No hypothesis is unused.

The Properties table has one row for the setting definitions and one row each for (M1), (M2), (S1), (S2), (S3) and (S4). The six property rows are marked proved.

# Summary of changes for run a46e4881-98bd-4cde-95b8-281978b5e066
I formalized and proved every statement of `C18_divided_power_lattices_and_the_dictionary.md` in a new folder, `RequestProject/DPLattice/`, namespace `DPLattice`. The folder builds with no errors or warnings and contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all the theorems below shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C17 are unchanged. From C17 I reused `CubeLaplacian.G`, `e`, `lap`, `K`, `Syl2` and `D2`. Every docstring names its part of C18, and `All.lean` is an index that also lists the encodings.

**Encodings** (`Basic.lean`, `Tensor.lean`, `Weyl.lean`, `PartT.lean`)
- **DP-lattice:** `DPLattice A` is a structure with a basis `ι : Type` (with `Fintype` and `DecidableEq`), a weight `wt : ι → ℤ`, and two families `Fd Ed : ℕ → Module.End A (ι → A)`. The axioms (W), (P0), (P1) and (K) are a field `isDP : IsDP wt Fd Ed`, stated exactly as in the file, with `Ring.choose` on `ℤ` cast to `A`. (W) is stated as: every coordinate of `F^{(r)} δ_i` outside weight `wt i − 2r` is zero (similarly for `E`).
- **`H`, morphisms, "equal data":** `H M` is the diagonal operator `(H f) i = wt i * f i`. Morphisms are `Hom`, and "equal data under a bijection" is `DataEquiv`.
- **`𝟙` and `V`:** `one A` and `V A`. In `V`, `F^{(1)}` and `E^{(1)}` are given by their 2×2 matrices.
- **`V ⊗ M`:** `tensorV M`, on the basis `Fin 2 × ι`, with `wt (e,i) = wtV e + wt i`. `bvec e m` is the vector `b_e m` (with `m` in slot `e`), and the coproduct formulas are lemmas (`tensorV_Fd_b0`, …).
- **`V^{⊗n}`:** `tensorPow A n`, defined by recursion: `𝟙` for `n = 0`, then `V ⊗ V^{⊗n}`.
- **Weyl lattices:** `delta A l` is `Δ_A(λ)` and `nabla A l` is `∇_A(λ)`, given by matrices on `Fin (λ+1)`. The file's formulas are proved as `delta_Fd_single`, `delta_Ed_single`, `nabla_Fd_single` and `nabla_Ed_single`. In these formulas the binomials are `Nat.choose`, because `λ − r ≥ 0`.

**Results**
- **Part T:**
  - `T1`, `T2`, `T3` and `T4`.
  - (T4) for `∇` is proved by induction on `λ`, through a surjective map from `V ⊗ ∇(λ)` onto `∇(λ+1)` that commutes with all the divided powers. `Δ` is the transpose of `∇` with `F` and `E` swapped.
  - (T5): `T5_delta_zero` and `T5_nabla_zero` give equal data with `𝟙` under `Fin 1 ≃ Unit`. `T5_delta_one` and `T5_nabla_one` are literal equalities of DP-lattices: `delta A 1 = V A` and `nabla A 1 = V A`.
- **Part L** (`Dictionary.lean`):
  - (L1) `L1_F` and `L1_H`. `pt A n S` is the basis index of the pure tensor with `b_1` on the positions in `S` (position 0 is the first tensor factor), and `pt_bijective` shows these are exactly the basis vectors.
  - (L2) `L2`, with an explicit `Ψ = psi A n` built by recursion on `n` (`psi_comm`). I checked the identity `Ψ ∘ lap = (F^{(1)} + n − H) ∘ Ψ` directly instead of going through the group-ring basis of the file's sketch.
- **Part C** (`Corollary.lean`): (C1) `C1`, with the explicit equivalence `C1equiv`; (C2) `C2`, obtained by composing C17's (D2) with (C1).

**Hypotheses:** none is unused. In (C1) and (C2), `Fintype J` and `DecidableEq J` are what identify the quotient of the product with the product of the quotients.

The Properties table has one row for the setting definitions and one row each for Parts T, L and C; the three part rows are marked proved.

# Summary of changes for run 544ce1db-f31b-4b7b-a7e5-746f59e82d23
I formalized and proved every statement of `C17_the_laplacian_in_the_group_ring.md` in a new folder, `RequestProject/CubeLaplacian/`, namespace `CubeLaplacian`. The folder builds with no errors or warnings and contains no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all the theorems listed below shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C16 are unchanged and none of them is imported. Each docstring names its part of C17. `All.lean` is an index that also lists the encodings.

**Encodings** (`Basic.lean`)
- **Group and group ring:** `G n = Fin n → ZMod 2` and `e n i = Pi.single i 1`. `R n = AddMonoidAlgebra ℤ (G n)`, which as a type is `G n →₀ ℤ`.
- **Elements of the ring:** `x`, `s`, `sS S = ∏ i ∈ S, s i` (so `sS ∅ = 1`) and `sigma` (σ). `mulSigma` is left multiplication by σ, as a `ℤ`-linear map.
- **Laplacian:** `lap A n f g = n * f g − ∑ i, f (g + e i)` works over any commutative ring `A`. Then `L n = lap ℤ n` and \(\sigma_A\) = `lap ℤ_[2] n`.
- **Cokernel and sandpile group:** `coker n = (G n → ℤ) ⧸ range (L n)` and `K n = Submodule.torsion ℤ (coker n)`.
- **2-part:** `Syl2 T = {x | ∃ e, 2^e • x = 0}`, as an additive subgroup.
- **The identification \(R = \mathbb{Z}^G\):** `toFun n : R n ≃ₗ[ℤ] (G n → ℤ)`, sending `f` to `g ↦ f g`.
- **\(R_+\) and \(T(n)\):** `Rplus n = span ℤ {s_S | S ≠ ∅}`. `T n = Rplus n ⧸ (range σ·).comap (Rplus n).subtype`, i.e. the range of σ on all of `R`, pulled back to \(R_+\).
- **Coefficients** in the basis \((s_S)\) are read as `(sBasis n).repr f S`.

**Results**
- **Part A** (`GroupRing.lean`): `A1`, `A2`, `A3` and `A4`. For (A4), `sBasis n : Module.Basis (Finset (Fin n)) ℤ (R n)` satisfies `sBasis n S = sS n S`. The \(s_S\) span `R`, and since there are \(2^n = |G|\) of them, that is enough to make them a basis over \(\mathbb{Z}\).
- **Part B** (`Laplacian.lean`):
  - (B1) `B1` gives the pointwise formula, and `B1'` says `toFun ∘ (σ·) = L ∘ toFun`.
  - (B2) `B2`, with the explicit equivalence `B2equiv`.
- **Part C** (`Triangular.lean`, `Cokernel.lean`):
  - (C1) `C1` (the \(s_\emptyset\)-coefficient of \(\sigma f\) is 0) and `C1_range` (`range (σ·) ≤ R_+`).
  - (C2) `C2_maps`, `C2_triangular` (a nonzero \(s_U\)-coefficient of \(\sigma s_S\) forces \(U = S\) or \(|S| < |U|\)), `C2_diagonal` (the diagonal entry is \(2|S|\), nonzero for \(S \ne \emptyset\)), `C2_injective` (for the restriction `sigmaPlus : R_+ → R_+`) and `C2_finiteIndex`.
  - (C3) `C3`: `R ⧸ range σ ≃ₗ[ℤ] ℤ × T n`, and `T n` is finite.
  - (C4) `C4`: `K n ≃ₗ[ℤ] T n`, `K n` is finite, and `coker n ≃ₗ[ℤ] ℤ × K n`.
- **Part D** (`TwoAdic.lean`, `Reduction.lean`):
  - (D1) `D1`: for every finite abelian group `T`, `T ⊗[ℤ] ℤ_[2] ≃+ Syl2 T`.
  - (D2) `D2`: `(G n → ℤ_[2]) ⧸ range (lap ℤ_[2] n) ≃+ ℤ_[2] × Syl2 (K n)`. The proof follows the file's sketch: right exactness of the tensor product, the isomorphism \((G \to \mathbb{Z}) \otimes \mathbb{Z}_2 \cong (G \to \mathbb{Z}_2)\), then (C4) and (D1).

**Differences from the file and hypotheses**
- No statement uses a hypothesis that its proof does not need.
- (C2) "maps \(R_+\) to \(R_+\)" is stated as `(Rplus n).map (mulSigma n) ≤ Rplus n`. In fact σ maps all of `R` into \(R_+\), by (C1).
- The triangularity statement in (C2) is proved for every `S`, not only for `S ≠ ∅`; this is slightly more general than the file.
- Isomorphisms are stated as `Nonempty (… ≃ₗ[ℤ] …)`, or `Nonempty (… ≃+ …)` in Part D, as in the file. The explicit equivalences are also available as definitions.

The Properties table has one row for the setting definitions and one row each for Parts A, B, C and D; the four part rows are marked proved.

# Summary of changes for run 8cfae8e6-0512-4162-b40d-a344db04d5c3
I formalized and proved every statement of `C16_the_family_group_over_Z2.md` in a new folder, `RequestProject/FamilyGroup/`, namespace `FamilyGroup`. The new files build with no errors or warnings, and contain no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all the theorems listed below shows only `propext`, `Classical.choice` and `Quot.sound`. I only added files: C1–C15 are unchanged. Each docstring names its part of C16, and `All.lean` is an index that also lists the encodings.

**Encodings** (`Basic.lean`)
- **The ring:** `A` is `ℤ_[2]`. Every isomorphism is a `ℤ_[2]`-linear equivalence, stated as `Nonempty (… ≃ₗ[ℤ_[2]] …)`.
- **The group of the tower:** `X ds α i := Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α i)`.
- **Small clocks:** `SC ds` is exactly the first factor of `Dance.proposition_4_3`.
- **Big clocks:** `Q e := ℤ_[2] ⧸ Ideal.span {2 ^ e}`.
- **Clocks of C15:** reused as named — `DanceSmith.Cst`, `yHat`, `yHatS`, `xClk`.
- **Pooled raw clocks:** `yPool ds i` is \(\hat y_i\) and `yPool0 ds` is \(\hat y_0\). They are built from `Rulers.clock`, `TheoremF.dancer` and `AntitonicFit.ifit`; `yPool0` pools over the `N − 1` positions `j ↦ dancer I (j+1)`.
- **Exponents:** natural numbers `E p` together with the equation `(E p : ℤ) = …`. Products run over `Fin N` or `Fin (N − 1)`.

**Results**
- **Part L** (`Cokernel.lean`, any commutative ring):
  - (L1) `L1`;
  - (L2) `L2_range` and `L2`;
  - (L3) `L3_unit` and `L3_zero`.
- **Part U** (`Cokernel.lean`): `U1` and `U2`.
- **Part X** (`Group.lean`): `X1`, `X2`, `X3`.
  - The proof chains `Dance.proposition_4_3` over `ℤ_[2]`, `Windows.theorem_D_iv`, (U2) and (L2), then uses `DanceSmith.S3`, `Z3` or `Z1`.
  - (L3) removes the odd units.
  - The positions are reindexed by `Fin.revPerm` in (X1). In (X2) they are reindexed by an equivalence `Unit ⊕ Fin (N−1) ≃ Fin N` that sends `()` to `N − 1` and `q` to `N − 2 − q`.
- **Part R** (`Raw.lean`): `R0`, `R1`, `R2`.
  - (R0) is proved directly: shifting the fit by a constant gives the fit of the shifted sequence, the level sets are unchanged, and `AntitonicFit.blockF_add_mul` handles the rounding.
  - (R1) uses `Rulers.proposition_5_3` and `TheoremF.lemma_0a`.
  - (R2) uses `Rulers.proposition_5_4_c`, together with `dancer I (j+1) ≠ ∅` for `j + 1 < N`. The identifications `CellFloor.xSharp`/`Houses.xH` = `Rulers.xSharp` and `GoldenMatching.xVal` (with α = 1) = `Rulers.xD` hold by unfolding the definitions.
  - (R1) and (R2) each give both forms in the file: the expanded equation, and `k + C + ŷ p = ŷ_i(p)` (resp. `k + K + ŷ♯ q = ŷ_0(q)`).
- **Part T** (`TheoremX.lean`): `T1`, `T2`, and `T2_empty` for the case `I = ∅` ((X3) with α = 1).

**Hypotheses and differences from the file**
- (R2) is stated without the hypothesis `I ≠ ∅`. It is not needed, because for `I = ∅` there is no position `q < N − 1 = 0`.
- Every other hypothesis is used:
  - `k ≥ 1`, `α ≥ 1`, `i ≥ 1` and `I ≠ ∅` enter through `DanceSmith.S3` and `Z3`;
  - `α ≥ 1` enters (X3) through `DanceSmith.Z1`;
  - `i ≥ 1` enters (R1) through `Rulers.proposition_5_3`.

The Properties table has one row for the definitions and one row each for Parts L, U, X, R and T; the five result rows are marked proved.

# Summary of changes for run 6c933352-e293-4734-80c0-a08698138b91
I formalized and proved every statement of `C15_smith_form_of_the_dance_matrix.md` in a new folder, `RequestProject/DanceSmith/`, namespace `DanceSmith`. The whole project builds with no warnings in the new files, no `sorry`, no new axioms and no `native_decide`. `#print axioms` on `P1`, `P2`, `P2_general`, `Q1`, `Q2`, `S1`–`S3` and `Z1`–`Z3` lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C14 are unchanged. Each docstring names its part of C15, and `All.lean` is an index that lists the encodings.

I reused, unchanged, all the objects you named.

**Encodings**
- **The matrix:** \(M\) is `Windows.finalMatrix ℤ ds α i` on `Fin N`, with `N = 2 ^ Dance.mCount ds`.
- **Bit reversal:** `bitRev m p` reverses the `m` lowest bits of `p`. `sl ds p = bitRev m p` is the slot map, and `slPerm ds` is the same map as a permutation.
- **The o-order matrix:** `Mo ds α i = M.submatrix (sl ds) (sl ds)`, i.e. `Mo p q = M (sl p) (sl q)`.
- **Clocks for \(i \ge 1\):** `xClk ds α i j` is `xVal k I α (i−1) (dancer I j)`, `yHat = ifit N xClk` is \(\hat y\), and `Cst = α·2^k + kappa (i−1) (2^k)` is \(C\).
- **Clocks for \(i = 0\):** `yHatS ds α = CellFloor.yhatSharp I k (2^k−1) α` is \(\hat y^\sharp\).
- **Smith forms:** `P * A * Q = diagonal …`. Exponents that the file writes as integers become natural numbers `E j` together with the equation `(E j : ℤ) = …`.

**Results**
- **Part P** (`Basic.lean`): `P1` (`sl` is an involution, hence a bijection, and `Dset ds (sl p) = dancer I p`); `P2_general` (any permutation, any `n`) and `P2` (for `Mo`).
- **Part Q** (`SmithForm.lean`):
  - `Q1` is proved directly: elimination with a pivot of least 2-valuation, where every row or column operation has odd determinant, followed by sorting the diagonal with `Tuple.sort`. Mathlib's Smith normal form is not used.
  - `Q2` gives `dd A r = Σ_{j<r} e j` for `r ≤ ρ`, every minor of size `r > ρ` is zero, and `det A ≠ 0 ↔ ρ = n`.
- **Part S** (`Positive.lean`): `S1`, `S2`, `S3`. The lower bound uses `SmithBounds.lemma_A1`, `Houses.lemma_A'_cost`/`lemma_A'_clock` and `CellFloor.theorem_B_floor`. The upper bound uses `GoldenMatching.corollary_D` (in `Golden.lean`). The two are combined by (Q1), (Q2) and `Divisors.theorem_B_without_M` (in `Bounds.lean`). Monotonicity comes from `CellFloor.lemma_7_9_I2`.
- **Part Z** (`Zero.lean`): `Z1`, `Z2`, `Z3`.

**Where the proof differs from the file**
- **Lower bound for \(i = 0\):** I used `CellFloor.theorem_B_floor` with zero penalties for the house \((I, k, K−1, α)\) instead of `theorem_C_floor`. By `lemma_7_9_I3` it gives the same sums of \(\hat y^\sharp\), and it covers every minor, including those through the zero row of ∅ and the column of \(I\), which the file's argument skips over.
- **Upper bound for \(i = 0\):** I applied `corollary_D` with \(\mu = K−1\) to a modified `Mo`: columns with \(D ≠ ∅\) are doubled, and the row of ∅ is replaced by \((2^{αK}, 0, …, 0)\). This leaves the rows used for every \(r \le N−1\) unchanged, and the factor \(2^{r−1}\) it introduces is divided out.

**Hypotheses:** none is unused. `k ≥ 1` enters through `Windows.theorem_D_iii`; `α ≥ 1` through `theorem_D_ii`/`theorem_D_iii` and the C9 results; `i ≥ 1` and `I ≠ ∅` are used where stated. `Z1` is more general than the file: it does not need `k ≥ 1`.

The Properties table lists the two groups of definitions (`sl`/`Mo` and the clocks) and the ten results ((P1), (P2), (Q1), (Q2), (S1)–(S3), (Z1)–(Z3)), all marked proved.

# Summary of changes for run a49f4cd1-8363-47e0-8dfb-e3c1b60415c3
I formalized and proved every statement of `C14_windows_and_theorem_D.md` in a new folder, `RequestProject/Windows/`, in namespace `Windows`. The whole project builds with no warnings in the new files, no `sorry`, no new axioms and no `native_decide`. `#print axioms` on `theorem_D`, `W_windows`, `theorem_4_4`, `H1_dance` and `H3_final_matrix` lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C13 are unchanged. Each docstring names its part of C14, and `All.lean` is an index that lists the encodings.

I reused, unchanged, all the objects you named from C10, C3, C11, C12 and C13. The proof also uses (A1) of C10, through `B1_rescaling`.

**Encodings** (`Basic.lean`):
- **Digit lists:** `ds : List Bool`, lowest digit first; `ds[t]?` is the t-th entry.
- **The family `I(ds)`:** `Ids ds`, which is `Finset.range ds.length` filtered by `ds[t]? = some true`. `mem_Ids` and `card_Ids` (\(|I(ds)| = m\)) are proved.
- **Rank:** `rank I t = #{u ∈ I : u < t}`.
- **Dancers `D(ds, s)`:** `Dset ds s`, written exactly as in the file, for `s : ℕ`; a slot `s : Fin _` is read through `s.val`.
- **Prefixes:** `ds.take h`.
- **Scalars:** \(\pi_0\) is `Deficit.pi0 (α : ℤ) i`, \(c_h\) is `Deficit.c (Ids ds) h`, and windows are `Finset.Ico`.
- **Ring homomorphisms:** `φ ∘ p` is `fun s f => φ (p s f)`, and matrices are mapped with `Matrix.map`.
- **Final matrix `M`:** `finalMatrix A ds α i` is `Mfin (dance ds 1 (pσ α i) κσ)` read on `Fin (2^m)` through `Fin.cast`, as in `Dance.proposition_4_3`.

**Results:**
- **Part H** (`Hom.lean`):
  - (H1): `H1_pT`, `H1_κT`, `H1_pSp`, `H1_κSp`, `H1_relabP`, `H1_relabK` and `H1_dance`.
  - (H2): `H2_Mfin` and `H2_pσ`.
  - (H3): `H3_final_matrix`.
- **(W)** `W_windows` (`TheoremW.lean`): three parts — the payments, the couplings on nested pairs, and `0` on non-nested pairs — for `h ≤ length ds` and `α ≥ 1`.
  - The induction (`windows_gen`) runs over an arbitrary remaining digit list.
  - It uses `twist_step` and `split_step` (`Moves.lean`). The twist computation (`core_coupling` in `Step.lean`) matches the sum over intermediate slots with the sum over \(\Delta_1 \subseteq \Delta\) that defines `starMul`.
  - The facts about the dancers are in `Labels.lean`: slot `2s+j` gets `D_s`, or `D_s ∪ {h}` when `j = 1`; `D` is a bijection onto the subsets; and `D_{s'} ⊆ D_s` implies `s' ≤ s`.
- **Theorem 4.4** `theorem_4_4`: `M s s' = if D(ds,s') ⊆ D(ds,s) then Mc … else 0`, over `ℚ`.
- **Theorem D** (`TheoremD.lean`): `theorem_D_i` through `theorem_D_iv`, combined in `theorem_D`. In (D-iii) the valuation is `padicValInt 2`, cast to `ℤ`.

**Unused hypotheses and generalizations:**
- `1 ≤ k` is used only for (D-iii).
- (D-i) passes `1 ≤ α` on to `Dance.proposition_4_3`, whose proof does not use it.
- (D-iv) and (H3) need no hypotheses on `k` or `α`.
- In the combined `theorem_D`, (D-iv) is stated only for rings in `Type`. The separate `theorem_D_iv` covers rings in every universe.

The Properties table lists the definitions (`Ids`, `Dset`, `finalMatrix`) and the six results ((H1), (H2), (H3), (W), Theorem 4.4, Theorem D), all marked proved.

# Summary of changes for run 8906e033-8563-4f3c-9669-333c1e8d84bc
I formalized and proved every statement of `C13_the_dance.md` in a new folder, `RequestProject/Dance/`, in namespace `Dance`. The folder builds with no warnings, no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all seven theorems lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C12 are unchanged. Each docstring names its part of C13, and `All.lean` is an index that lists the encodings.

Everything is over an arbitrary commutative ring `A`, and every module of the tower is `A`. I reused from C11 `Payment.Sys`, `slotLof`, `slotEmb`, `G`, `NΦ`, `flΦ`, `FΦ`, `pT`, `κT` and `theorem_A`, and from C12 `NΨ`, `flΨ`, `FΨ`, `pSp`, `κSp` and `theorem_B`, all unchanged.

**Encodings** (`Basic.lean`):
- **Counts:** `nLen ds` is `ds.length`. `mCount ds` (the number of `true` entries) is defined by recursion, and `mCount_eq_count` proves it equals `ds.count true`.
- **Tower `T(ds)`:** defined by recursion on `ds`. The index type `Idx ds` is `Unit`, `Idx rest × Fin 2` or `Idx rest × Fin 4`. The floor `fl ds` is `0`, `flΦ` or `flΨ`, and the operator `F A ds` is `0`, `FΦ` or `FΨ`. `SysT A ds S` is `Payment.Sys (fun _ => A) S`.
- **Relabelling:** `relabP e p' = p' ∘ e` and `relabK e κ' s u = κ' (e s) (e u)`. `splitIso r : Lex (Fin r × Fin 2) ≃o Fin (r * 2)` is `finProdFinEquiv ∘ ofLex`, and `splitIso_val` shows it sends `(s, j)` to `2s + j`.
- **Dance data:** `danceAux` follows the file's recursion exactly, on slots `Fin (slots ds r)`. `slots_eq` proves `slots ds r = r * 2^{m(ds)}`. `dance ds r p κ` is the same data read on `Fin (r * 2^{m(ds)})` through `Fin.castOrderIso`. `dance_nil`, `dance_false` and `dance_true` give the file's recursion equations up to that cast.
- **Final matrix and `σ`:** `Mfin`, `pσ α i` (the file's \(2^{\alpha-1}(i+f)\)), `κσ = 0` and `sigma A ds α i = G (fl ds) (F A ds) (pσ α i) κσ`.
- **Clocks:** `Clocks A ds r h : ModuleCat A` is defined by the recursion of (D1). It is a bundled module so that the recursion also carries the module structure.

**Results:**
- **(R1)** (`Relabel.lean`): `relabSys` sends \(x\,\iota_{s,i}\) to \(x\,\iota_{e s,i}\). `R1_intertwine` shows it intertwines the two payment systems, and `R1_coker` gives the equivalence of the cokernels of `c • G` for every `c`.
- **(D1)** `D1_scaled_dance` (`D1.lean`): induction on `ds`, using Theorem A for a digit `false`, and Theorem B followed by (R1) for a digit `true`.
- **(D2)** `D2_clocks` (`D2.lean`): `Clocks(ds,r,h)` is equivalent to the product over \(j < n\) of `(Fin (r·2^(n+m−1−j)) → A) ⧸ 2^(h+j)•⊤`. The proof counts \(2^{n+m}\) indices for the tower and uses `(X⧸c⊤) × (Y⧸c⊤) ≅ (X×Y)⧸c⊤`.
- **(D3)** `D3_final_matrix` (`D3.lean`): via `D3_intertwine`, which shows that on `T([])` the map `G` is `Matrix.toLin' (Mfin p κ)`.
- **Proposition 4.3** `proposition_4_3` and **(D4)** `D4_lower_triangular_even` (`Proposition.lean`).

**Where the statements differ from the file:**
- **Proposition 4.3 holds for every digit list `ds`**, not only the one belonging to a given λ; every λ has exactly one digit list.
- **`M` is read through a cast:** the final matrix lives on `Fin (1·2^{|I|})`, so the statement reads it on `Fin (2^{|I|})` with `Matrix.submatrix` along `Fin.cast`.
- **The hypothesis `1 ≤ α` is unused.** I kept it because the file states it.
- **(D4) is more general:** it holds for the final matrix of any data (`Mfin_lower_triangular_even`), not only for the dance data.

The Properties table lists the definitions (the tower, the dance data, `Mfin`/`σ`/`Clocks`) and the six results ((R1), (D1)–(D4), Proposition 4.3), all marked proved.

# Summary of changes for run 3f8eef5f-310b-46a8-8803-aac781049874
I formalized and proved every statement of `C12_split_move.md` in a new folder, `RequestProject/Split/`, in namespace `Split`. The folder builds with no warnings, no `sorry`, no new axioms and no `native_decide`. `#print axioms` on Theorem B, Corollaries B1 and B2, and (A1)–(A3) lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C11 are unchanged. Each docstring names its part of C12, and `All.lean` is an index that lists the encodings.

**Encodings** (`Basic.lean`, the Setting; everything is over an arbitrary commutative ring `A`). I reused `Payment.Sys`, `slotLof`, `slotEmb`, `Payment.G` (halved data), `Payment.pT` and `Payment.κT` without changing them.
- **Tensor model `V ⊗ Φ`:**
  - Index type `ι × Fin 2 × Fin 2`, with module `N i` at every index.
  - Floor `flVΦ fl (i,e,e') = 2 fl(i) + e + e'`.
  - `FVΦ F` is the sum of the `F_V` part and the `F^Φ` part, defined on generators with `DirectSum.toModule`.
- **Split model `Ψ`:**
  - Index type `ι × Fin 4` (`0 = A`, `1 = B`, `2 = C`, `3 = Dd`), with module `N i` at every index.
  - Floor `flΨ fl (i,j) = 2 fl(i) + ![0,1,1,2] j`.
  - `FΨ F` is given exactly by the four formulas of the Setting, on generators.
- **Change of basis:** `theta` (θ) and `thetaInv` are defined on generators as in the Setting and (A1). `thetaS S` and `thetaInvS S` apply them slot by slot.
- **Split data:** the slot type is `Lex (S × Fin 2)` (`0 = A`, `1 = C`, lexicographic order). `pSp` and `κSp` are the file's `p''` and `κ''`, with no division, and `κSp` is `0` on every pair not listed.
- **Scalars:** `c · G` is `c • G`, and `c M^S` is `c • ⊤`.

**Results:**
- **(A1):** `A1_theta_thetaInv` and `A1_thetaInv_theta` show the two maps are inverse. `thetaEquiv` is the resulting linear equivalence, and `A1_thetaEquiv_coe` shows its underlying map is θ.
- **(A2):** `A2_theta_comp_F`: `θ ∘ F^{VΦ} = F^Ψ ∘ θ`.
- **(A3):**
  - `thetaSEquiv` and `A3_thetaSEquiv_coe`: θ_S is a linear equivalence.
  - `A3_thetaS_comp_G`: `θ_S ∘ G_{VΦ} = G_Ψ ∘ θ_S` for all halved data.
  - `A3_coker`: `coker(c • G_{VΦ}) ≃ coker(c • G_Ψ)` for every `c`.
- **Theorem B** (`theorem_B`): for every `c : A`, there is an `A`-linear equivalence `Sys_Ψ ⧸ range (c • G_Ψ) ≃ (M^S ⧸ c•⊤) × (M^S ⧸ c•⊤) × (Sys N (Lex (S × Fin 2)) ⧸ range (c • 2 • G''))`. Existence is stated as `Nonempty (… ≃ₗ[A] …)`.
- **Corollary B1:** `corollary_B1` (for Ψ) and `corollary_B1_VΦ` (for `V ⊗ Φ`, via (A3)), both with `c = 1`.
- **Corollary B2:** `corollary_B2`, with `c = 2^h` and `2^(h+1) • G''`.

**How the proof follows the file's Proof:**
- `Decomp.lean`: I split `Sys_Ψ` as `A ⊕ B ⊕ C ⊕ Dd ≃ (M^S)^4`. In that splitting, `G_Ψ` is the block operator `(a,b,c,d) ↦ (D0 a + 2F b, a + D1 b, 2a + D1 c + 2F d, c + D2 d)`; these are the file's four displayed formulas.
- `SplitData.lean`: `M^{S×{A,C}} ≃ M^S × M^S`, and in that splitting `G''` is `(a,c) ↦ (F a + E0 a, −D1 a + F c + E1 c)`. `D0 ∘ D1 = −2 E0` comes from C11's coefficient identity, and `D1 ∘ D2 = −2 E1` is the same identity applied to the data shifted by one floor.
- `Block.lean`: an explicit change of coordinates (the inverse of φ, then a reordering of the factors) sends `range(c • G_Ψ)` to `c•⊤ × c•⊤ × range(c • 2 • G'')`, which gives the equivalence.

The statements are exactly those of the file, and no hypothesis is unused; in particular nothing is assumed about `F`. The Properties table has entries for the definitions (the two models, θ, the split data) and the eight results, all marked proved.

# Summary of changes for run ad645d58-d2e0-4908-abed-2451818cfed7
I formalized and proved every statement of `C11_payment_systems_twist.md` in a new folder, `RequestProject/Payment/`, in namespace `Payment`. The folder builds with no warnings, no `sorry`, no new axioms and no `native_decide`. `#print axioms` on Theorem A and Corollaries A1 and A2 lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C10 are unchanged. Each docstring names its part of C11, and `All.lean` is an index that lists the encodings.

**Encodings** (`Basic.lean`, the Setting; everything is over an arbitrary commutative ring `A`):
- **Graded family:** `ι` with `DecidableEq`, `fl : ι → ℕ`, a family `N : ι → Type*` of `A`-modules, and `F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)`. Nothing is assumed about `F`.
- **Slot type:** `S` with `Fintype` and `LinearOrder`.
- **Module of a system:** `Sys N S = ⨁ q : S × ι, N q.2`.
  - `x ι_{s,i}` is `slotLof A N S s i x`, which is `DirectSum.lof` at `(s, i)`.
  - `m ι_s` is `slotEmb A N S s m`.
- **Payment system:** `G fl F p κ` is defined on generators by `DirectSum.toModule`, exactly as in the Setting. It uses `(2 * p s' (fl i)) •` and the sum over `s ∈ Finset.univ.filter (s' < ·)`.
- **Double Φ:** index type `ι × Fin 2`, floor `flΦ fl (i,e) = 2 * fl i + e`, modules `NΦ N (i,e) = N i`. The operator `FΦ F` sends `x` at `(i,0)` to `x` at `(i,1)`, and `x` at `(i,1)` to `2 •` (`F x` placed with `e = 0`).
- **Twisted data:** `pT p` and `κT p κ` are the file's `p'` and `κ'`, with no division.
- **Scalars and quotients:** `c · G` is `c • G`, and `c·M^S` is `c • ⊤`.

**Results** (`TheoremA.lean`):
- `theorem_A`: for every `c : A`, there exists an `A`-linear equivalence `Sys (NΦ N) S ⧸ range (c • G_Φ) ≃ₗ[A] (Sys N S ⧸ c • ⊤) × (Sys N S ⧸ range (c • (2 : A) • G'))`. Existence is stated as `Nonempty (… ≃ₗ[A] …)`.
- `corollary_A1` (`c = 1`, without the trivial factor): `M_Φ^S ⧸ range G_Φ ≃ M^S ⧸ range (2 • G')`.
- `corollary_A2` (`c = 2^h`): `M_Φ^S ⧸ range (2^h • G_Φ) ≃ (M^S ⧸ 2^h • ⊤) × (M^S ⧸ range (2^(h+1) • G'))`.

**How the proof follows the file's Proof** (`Twist.lean`, `Block.lean`):
- Split `M_Φ^S` as `B_0 × B_1 ≃ M^S × M^S`.
- In that splitting, `G_Φ` has the block form `(a, b) ↦ (T_0 a + 2 F b, a + T_1 b)`. These are the file's two displayed formulas.
- The coefficient identity `T_0 ∘ T_1 = −2 · (payment/coupling part of G')` is where the formulas for `p'` and `κ'` are used, including the middle sum over `s' < s < u`.
- A row/column reduction then gives the isomorphism, using the shear `(y, z) ↦ (y − T_0 z, z)` and `(X × Y)/(P × Q) ≅ X/P × Y/Q`.

The statements are exactly those of the file, and no hypothesis is unused. The Properties table has entries for the definitions (`G`, the double, the twisted data) and the three results, all marked proved.

# Summary of changes for run 0855be32-aeec-4ea0-9723-c4cfedd5deba
I formalized and proved every statement of `C10_deficit_law.md` in a new folder, `RequestProject/Deficit/`, in namespace `Deficit`. The folder builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all 13 theorems lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C9 are unchanged.

**Files** (each docstring names its part of C10; `All.lean` is an index and lists the encodings):
- `Basic.lean`, the Setting:
  - `starMul f g Δ` is \((f\star g)(\Delta)=\sum_{\Delta_1\subseteq\Delta} f(\Delta_1)\,g(\Delta\setminus\Delta_1)\), summed over `Δ.powerset`. I called it `starMul` rather than `star` because `star` clashes with Mathlib's `star`.
  - `a I t Δ : ℤ` and `c I h Δ : ℚ` are defined by recursion on `t` and `h`, using exactly the recursions of the Setting. Indicators \([P]\) are written `if P then 1 else 0`.
  - `pi0 α i d` is \(2^\alpha(i+d)\).
  - `Mc I k α i D D'` is the closed-form entry: a rational number with the product over `Finset.Ico (oE D) (oE D' + 2^k)`. Powers of 2 with integer exponents use `zpow`.
- `Polynomials.lean`: (A1) `A1_support`, (A2) `A2_const`, (A3) `A3_deficit`.
  - (A3) is proved as in the paper: induction on Δ (strong induction over subsets), then on `t`. It goes through an odd-part form, \(a_t(\Delta)=2^{t-|\Delta|-\min\Delta}\cdot u\) with \(u\) odd. The cross terms are paired by splitting on whether \(\min\Delta\in\Delta_1\).
- `DeficitLaw.lean`:
  - **Lemma 4.5**: `lemma_4_5`, with `δ = Rulers.delta k`.
  - Its "in particular" sentences: `lemma_4_5_empty` and `lemma_4_5_nonempty`.
  - Its last sentence, that the valuation does not depend on the rest of `I`: `lemma_4_5_indep`.
  - (A4): `A4_subadditivity`, stated with `Rulers.minOr`.
  - (A5): `A5_q1` and `A5_q2`, proved by `decide`.
- `Rescaling.lean`: (B1) `B1_rescaling`.
- `ClosedForm.lean`:
  - (C1) `C1_window`, via Lemma 5.0 (`Rulers.lemma_5_0_sdiff`).
  - (C2) `C2_integrality_valuation`. It gives an integer `z ≠ 0` with `Mc = z`, and the valuation identity with `padicValRat 2` on the left and `Rulers.v2 (i + d)` inside the sum.

**Valuations:** `padicValInt 2` for the \(a_t\), `padicValRat 2` for `Mc`. As you asked, I reused `Rulers.oE`, `minOr`, `delta`, `v2` and Lemma 5.0.

**Where the statements differ from the file** (each noted in its docstring):
- **(A3) is stated in ℕ, as in the file, plus one extra conjunct**, `|Δ| + min Δ ≤ t`. It shows that the natural-number subtraction does not truncate.
- **Some results need fewer hypotheses:**
  - (A1), (A2) and (B1) hold for every `I`.
  - (A3) needs only `Δ ⊆ I`.
  - `a_k(∅) = 1` does not need `I ⊆ {0,…,k−1}`.
- **No hypothesis is unused:** every hypothesis of Lemma 4.5, (A4), (C1) and (C2) is used.

The Properties table has entries for the 4 definitions and the 11 results; all 11 results are marked proved.

# Summary of changes for run 813c96e8-edf2-4368-a81b-1b3eac9661d2
I formalized and proved every statement of `C9_integrality_and_cell_floor.md` in a new folder, `RequestProject/CellFloor/`, in namespace `CellFloor`. The folder builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` on all seven main theorems lists only `propext`, `Classical.choice` and `Quot.sound`. I only added files; C1–C8 are unchanged.

**Files** (each docstring names its part of C9; `All.lean` is an index and lists the encodings):
- `Basic.lean`, the Setting:
  - `cellClock` is \(z(p)=x_H(p)-P_rJ_H(p)+P_cJ_H(N-1-p)\).
  - `cellCost` is \(\hat c_H(p,q)-P_rJ_H(p)+P_cJ_H(q)\).
  - `IsCellArrow` is: \(p,q<N\) and `dancer I q ⊆ dancer I p`, loops included.
  - `penal V I k ℓ P` is \(V-PJ_H\), so it gives the `v` and `w` of Theorem B.
  - `xSharp`, `yhatSharp`, `costSharp` and `IsSharpArrow` are \(x^\sharp\), \(\hat y^\sharp\), \(\mathrm{cost}^\sharp\) and the arrows of Theorem C.
  - All of these are functions of positions, built on `TheoremF.xHseq`, `JHseq`, `dancer`, `Potential.yhat` and `Potential.cHat`.
- `Integrality.lean`, **Lemma 7.9**:
  - (I1) `lemma_7_9_I1`, by induction on \(|I|\). It uses (W3) of Theorem F0 and the fact that when the real fit is an integer, `ifit` equals it, which follows from (L).
  - (I2) `lemma_7_9_I2`. It uses Lemma 7.2 (`lemma_7_2_b3_b2`, `lemma_7_2_b1`), with the strict cuts supplied by Theorem F1 (Cut), and Lemma 0f and `JHseq_mono` from C7.
  - (I3) `lemma_7_9_I3`. It uses Lemmas 0b and 0f, Theorem F1 and the cut at `1`.
- `Floor.lean`:
  - **Theorem B**: `theorem_B_U1`, `theorem_B_U2` and `theorem_B_U3`, combined in `theorem_B`. (U3) includes equality on loops.
  - **Consequence of Theorem B**: `theorem_B_floor`, through `SmithBounds.theorem_U` with everything cast to ℝ.
  - **Theorem C**: `theorem_C` covers (U1)–(U3).
  - **Consequence of Theorem C**: `theorem_C_floor`.

**Encoding notes and hypotheses:**
- A house is given by `I k ℓ α` with `∀ t ∈ I, t < k`, `ℓ < 2^k` and `1 ≤ α`. \(N=2^{|I|}\), and the penalties are natural numbers. Each theorem carries only the house conditions its proof uses.
- `theorem_B_U1` and `theorem_B_U3` need no house condition.
- In (I3) and Theorem C, \(\ell=2^k-1\) is the hypothesis `hℓ' : ℓ = 2 ^ k - 1`. This implies `ℓ < 2^k`, so that is not a separate hypothesis. \(I\neq\emptyset\) is written `I.Nonempty`.
- `[p ≠ 0]` is written `if p ≠ 0 then 1 else 0`.
- **More general than the file:** the two consequence theorems do not assume a potential. They take one from `Potential.theorem_F`.

The Properties table has entries for the new definitions and the seven theorems, all marked proved.

# Summary of changes for run 13a49f40-8508-4a21-8c18-a85983d524cb
I formalized and proved every statement of `C8_theorem_F_potential.md` in a new folder, `RequestProject/Potential/`, in namespace `Potential`. The folder builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` on `theorem_F`, `corollary_F'`, `lemma_P`, `lemma_X`, `lemma_N` and `lemma_F` lists only `propext`, `Classical.choice` and `Quot.sound`. I only added new files; C1–C7 are unchanged.

**Files.** Each docstring names its part of the file. `All.lean` is an index and also lists the encodings.
- `Basic.lean`, the Setting:
  - `yhat` (\(\hat y_H\), defined as `AntitonicFit.ifit (2^#I) (TheoremF.xHseq I k ℓ α)`).
  - `cHat` (`Houses.cHatH` applied to `TheoremF.dancer I p` and `dancer I q`).
  - `IsArrow I p q` (`p, q < N` and `dancer I q ⊂ dancer I p`), with `IsArrow.lt` proving \(q<p\).
  - `IsPotential I k ℓ α V`: a structure whose fields `E`, `M`, `G` are exactly (E), (M), (G), with `V : ℕ → ℤ`.
  - `X1` (\(X_1=\hat y'+d\), with `d = TheoremF.dWalk`) and `vPrime` (\(v'\), built from `Houses.typ`, `kap`, `tau` and `TheoremF.JHseq`).
- `LemmaP.lean`, **Lemma P**:
  - (P1): `lemma_P1_low`, `lemma_P1_high`, `lemma_P1_cross`, and `lemma_P1_no_arrow` (no arrow with \(p<M\le q\)).
  - (P2) `lemma_P2`, (P3) `lemma_P3`, (P4) `lemma_P4`.
  - All four together: `lemma_P`.
  - The proofs use C6's (C1), (C2) and (C5), C7's Lemmas 0c and 0e, `dWalk_eq`, `JHseq_mono` and (Λ), as the file does.
- `Junction.lean`: **Lemma X** `lemma_X` and **Lemma N** `lemma_N`, using (W1) and (W3) of C7.
- `Flat.lean`, **Lemma F**: (F1)–(F4) are `lemma_F1` … `lemma_F4`, and `lemma_F` combines them. (F4) holds for every integer \(c_F\) with `lo ≤ c_F ≤ hi`.
- `TheoremF.lean`:
  - **Theorem F** `theorem_F`, by induction on \(|I|\): `V := 0` when \(I=\emptyset\); otherwise Lemma N, or Lemma F with \(c_F := lo\).
  - **Corollary F′** `corollary_F'`, with `W(D) := V(rank_I D)`.

**Encodings.**
- A house is given by its components `I k ℓ α`, with the hypotheses `∀ t ∈ I, t < k`, `ℓ < 2^k` and `1 ≤ α`. \(c=\max I\) is written `hc : c = I.max' hne`, \(I'\) is `I.erase c`, \(M\) is `2^#(I.erase c)`, and \(h\) is the natural number `k - c` cast to `ℤ`.
- `vPrime` at a position \(p\ge M\) is defined as \(\tau+V'(p-M)-[T=0]\kappa J'(p-M)\), so \(v'(M+p)\) is as in the file.
- In Lemma F:
  - \(f\) is given by its defining property `IsLeast {p | p < M ∧ X_1 p ≤ 0} f`.
  - The flat \(F\) is `f ≤ p ∧ p ≤ N-1-f`.
  - `lo` and `hi` are `loF` and `hiF`, including the file's case split on \(f=0\).
  - The potential in (F4) is `flatV`.
  - (F2)'s maximum and minimum are stated with `IsGreatest` and `IsLeast` on images of intervals.

**Where the statements differ from the file** (each noted in its docstring):
- **Lemma F does not take the hypothesis \(X_1(M-1)\le 0\) separately.** That hypothesis is equivalent to the existence of \(f\): `exists_flat_start` proves one direction and `X1_last_nonpos_of_flat` the other. So it is carried by the hypothesis on \(f\).
- **Some parts need fewer hypotheses:**
  - Lemma X needs no house condition and no \(c=\max I\).
  - (P2), (P3), (F2) and (F3) need no house condition.
  - (P1) does not use \(\alpha\ge1\), and (P4) does not use \(\ell<2^k\).
  - The combined `lemma_P` and `lemma_F` carry all the hypotheses.

The Properties table lists 2 definitions (`IsPotential`, `vPrime`) and 6 results (Lemma P, X, N, F, Theorem F, Corollary F′); all 6 results are marked proved.

# Summary of changes for run a15e0203-859b-4a76-8e32-14ded1f84d85
I formalized and proved every statement of `C7_theorem_F_walk_and_cut.md` in a new folder, `RequestProject/TheoremF/`, in namespace `TheoremF`. The whole project builds. The new folder has no `sorry`, no new axioms and no `native_decide`. `#print axioms` on the main theorems lists only `propext`, `Classical.choice` and `Quot.sound`. I only added new files; the C1–C6 folders are unchanged.

**Files** (each docstring names its part of the file; `All.lean` is an index and also describes the encodings):
- `Dancers.lean`, **Lemma 0**: `lemma_0a`, `lemma_0b`, `lemma_0c_existsUnique`, `lemma_0c_rank`, `lemma_0d`, `lemma_0e`.
- `Sequences.lean`: the definitions, plus **Lemma 0f** (`lemma_0f_antisymm`, `lemma_0f_J0`).
- `Walk.lean`: **(W0)** and **(W1)** of Theorem F0, plus the step that derives (W2)/(W3) for `H` from (Cut) for `H'`.
- `TheoremF.lean`:
  - **Theorem F1** (Theorem 7.8): `theorem_F1`, also split into `theorem_F1_Lambda` and `theorem_F1_Cut`.
  - **Theorem F0**: `theorem_F0` (all four parts), plus `theorem_F0_W2` and `theorem_F0_W3`.
  - F0 and F1 are proved together by induction on \(|I|\) (`F1_all`, `F1_empty`, `F1_step`), as in the file.

**Encodings**:
- **Dancers:** `dancer I p := I.filter (fun t => Houses.bit (#(I.filter (· < t))) p = 1)`, exactly as you specified.
- **Sequences:** `xHseq I k ℓ α : ℕ → ℤ` is \(x_H\) and `JHseq I k ℓ : ℕ → ℕ` is \(J_H\), both indexed by position. `dWalk I k ℓ α c p := Houses.d1 I k ℓ α c (dancer (I.erase c) p)` is \(d\).
- **Fits:** \(\hat y_H\) is `ifit (2^#I) x_H` and the real fit is `fit (2^#I) (toR x_H)`. These, and `concat`, `mirror` and `IsStrictCut`, are the C1 definitions. I also reused `Rulers.oE`, `GoldenMatching.rank`, and `Houses.xH`, `JH`, `typ`, `kap`, `sat`, `tau`, `d1`, together with Lemmas A0, C3, C4 and C6 and C1's Lemmas 7.2/7.3 and (A2)/(A3).
- **Houses:** a house is given by its components, with the hypotheses `∀ t ∈ I, t < k`, `ℓ < 2^k` and `1 ≤ α`. \(c=\max I\) is written `c = I.max' hne`, and \(I'\) is `I.erase c`.
- **"First position with \(J(b)=1\)":** written as `J b = 1 ∧ ∀ p < b, J p = 0`.

**Unused hypotheses and more general statements** (each noted in its docstring):
- (0a) holds for every `p`, not only `p < N`.
- The antisymmetry half of Lemma 0f needs no house condition; `J_H(0) = 0` needs only `ℓ < 2^k`.
- (W0) and (W1) do not need `α ≥ 1`, and (W1) needs no house condition at all.
- (W2) uses only `α ≥ 1`, which it needs to get (Cut) for `H'`.
- The combined `theorem_F0` carries all the house hypotheses.

**Where the proof differs from the paper:** for (Cut), I show directly that `fit(x_H)` drops strictly at `b`, in each of the paper's cases (a), (b) and (c). C1's consequence (D) then gives the cut, so Lemma 7.2(c) is not needed. Positivity before the boundary uses (Λ) for `H'` and the fact that `ifit < fit + 1`. The cut at `N − b` follows from (A3).

The Properties table lists the 4 definitions and the 10 results; all 10 results are marked proved.

# Summary of changes for run 194e2f27-03cb-4060-a76b-5c7ced6e0828
I formalized and proved every statement of `C6_houses_windows_penalties.md` in a new folder, `RequestProject/Houses/`, in namespace `Houses`. The whole project builds, and the new folder has no `sorry`, no new axioms and no `native_decide`. `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for every theorem. I did not change `AntitonicFit/`, `SmithBounds/`, `Rulers/`, `GoldenMatching/` or `Divisors/`.

**Files** (each docstring names its part of the file; `All.lean` is an index):
- `Basic.lean`: the definitions and the shared carry arithmetic.
- `LemmaA.lean`:
  - **Lemma A0**: `lemma_A0_antisymm`, `lemma_A0_upset`.
  - **Lemma A (7.5)**: `lemma_A`, plus `lemma_A_exactly_one_zero` for the «exactly one is zero» claim.
  - **Lemma A′**: `lemma_A'_cost`, stated with `GoldenMatching.cHat`, and `lemma_A'_clock`.
- `Windows.lean`: **Lemma B (7.6)**, `lemma_B1` to `lemma_B6`.
- `TopDigit.lean`: **Lemma C (7.7)**, `lemma_C1` to `lemma_C4`, `lemma_C5_not_mem`, `lemma_C5_mem`, `lemma_C6`, `lemma_C7`.

**Encodings** (also in the module docstrings):
- **House:** a house \((I,k,\ell,\alpha)\) is given by its components, with `I : Finset ℕ`. The conditions are the hypotheses `hI : ∀ t ∈ I, t < k` and `hℓ : ℓ < 2 ^ k`.
- **Reused names:** `Rulers.oE`, `kappa`, `next`, `h`, `gamma`, `ruler`, `v2` and `GoldenMatching.cHat`.
- **New definitions:**
  - `bit u x` is \(\lfloor x/2^u\rfloor \bmod 2\).
  - `r u x` is \(v_2(\lfloor x/2^u\rfloor+1)\), used both as \(r_k(\mu)\) and as \(r_u(\ell)\).
  - `RH I k ℓ α E` is \(R_H(E)\), defined as `Rulers.ruler k I α ℓ E`.
  - `JH k ℓ E` is \(J_H(E)\), `xH` is \(x_H\) and `cHatH` is \(\hat c_H\).
  - `typ`, `kap`, `sat` and `tau` are \(T_t,\kappa_t,\mathrm{sat}_t,\tau_t\).
  - `cin ℓ u E` is \(c_u(E)\).
  - `car I k ℓ t E` is the number of \(u\) in `Finset.Ico t (next k I t)` with \(c_{u+1}(E)=1\).
  - `d1` is \(d_1\) from (C6).
- **Part C:** \(c=\max I\) is written `hne : I.Nonempty`, `hc : c = I.max' hne`. Then \(I'\) is `I.erase c`, \(H'\) is `(I.erase c, c, ℓ % 2 ^ c, α)` and \(\gamma'\) is `Rulers.gamma c (I.erase c)`. In (C5), \(h\) is `k - c`.
- **Notation:** indicators \([P]\) are `if P then 1 else 0`. "\(d=1\)" in (B2)/(B3) is written `t ∈ E`. "Exactly one is zero" is `Xor'`.

**Where the statements are more general than the file** (each noted in its docstring): theorems only carry the hypotheses their proofs use, so unused ones were dropped.
- Lemma A0 needs neither house condition, and its up-set part does not need `E, F ⊆ I`.
- (B1) needs neither house condition.
- (B2)–(B4) do not need `ℓ < 2^k`.
- Both halves of (C5) do not need `ℓ < 2^k`.
- In Lemma A and Lemma A′, \(\ell\) is `μ % 2 ^ k` (or `m % 2 ^ k`), so `ℓ < 2^k` holds automatically.
- As the file says, nothing uses \(\alpha\ge1\).

**How the proofs go:**
- **Lemma A and (C1)/(C2):** these come from exact identities for \(\kappa\) at a bit \(c\), using C3's binary-digit facts and \(s_2(q+1)=s_2(q)+1-v_2(q+1)\).
- **Lemma B:** I proved \(\kappa(a,b)=\sum_u c_{u+1}\) from \(s_2(n)+\sum_u\lfloor n/2^{u+1}\rfloor=n\). Inside a window, the carry into bit \(t+j\) is 1 exactly when \(j\) is at most the length of the run of carries. The windows cover \([\min I,k)\) without overlap. Together these give (B2)–(B5).
- **(C3)/(C4):** these reduce to linear arithmetic in \(q=\lfloor \ell/2^c\rfloor<2^{k-c}\).
- **(C7):** this follows from (C6) and Lemma A0.

The Properties table lists the 20 theorems as proved, together with the main definitions.

# Summary of changes for run 83be8821-c12e-4824-809a-8b02a1b68e2d
I formalized and proved every statement of `C5_divisors_theorem_65.md` in a new folder, `RequestProject/Divisors/`, in namespace `Divisors`. The whole project builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every main theorem. I did not change `AntitonicFit/`, `SmithBounds/`, `Rulers/` or `GoldenMatching/`.

**Files** (each docstring names its part of the file; `All.lean` is an index):
- `CauchyBinet.lean`: Mathlib does not have the Cauchy–Binet formula, so I proved it here (`cauchy_binet`): for \(A\) of size \(r\times n\) and \(B\) of size \(n\times r\) over any commutative ring, \(\det(AB)=\sum_{|S|=r}\det A[\cdot,S]\,\det B[S,\cdot]\).
- `Basic.lean`, **Part A setting**: `minor`, `minorVals` and `dd`. It also has Cauchy–Binet for minors (`minor_mul`) and three facts from the setting:
  - `minorVals_nonempty`: if `det M ≠ 0`, the set of valuations is non-empty for every `r ≤ n`. The proof uses Laplace expansion.
  - `dd_zero`: \(dd_0 = 0\).
  - `dd_top`: \(dd_n = v_2(\det M)\).
- `Invariance.lean`: **Lemma A1** (`lemma_A1`).
- `Diagonal.lean`: **Lemma A2** (`lemma_A2`) and **Corollary A3**, split into `corollary_A3_sum`, `corollary_A3_increment` and `corollary_A3_convex`.
- `TheoremB.lean`: `dHat`, **Theorem B** (`theorem_B`), `theorem_B_without_M` and **Corollary B′** (`corollary_B'`).

**Encodings** (also given in the module docstrings):
- **Matrices:** `M : Matrix (Fin n) (Fin n) ℤ`.
- **Minors:** `minor M r A B` is the determinant of `M.submatrix (A.orderEmbOfFin _) (B.orderEmbOfFin _)`, so rows and columns are taken in increasing order. It is set to `0` unless `|A| = |B| = r`, a case that is never used.
- **`dd_r(M)`:** `minorVals M r` is the set of values `padicValInt 2 (minor M r A B)` over pairs with `|A| = |B| = r` and a non-zero minor. `dd M r` is its minimum, written `sInf`. By `minorVals_nonempty` this is a real minimum in the file's setting; the convention `sInf ∅ = 0` only matters outside it.
- **Part A data:** exponents are `e : Fin n → ℕ` with `Monotone e`, the units are odd `u`, and \(D\) is `diagonal fun i => u i * 2 ^ e i`. The sum \(e_0+\dots+e_{r-1}\) is the sum over `univ.filter (fun i : Fin n => (i : ℕ) < r)`. The increments and convexity in A3 are stated in `ℤ`.
- **Part B data:**
  - `x : ℕ → ℤ`, and \(\hat y\) is `AntitonicFit.ifit N x`.
  - \(U\) and \(Y\) are sums over `Finset.Ico (N - r) N`, as in C2.
  - `e : ℕ → ℤ` with `e i ≤ e j` whenever `i ≤ j < N`.
  - `dHat C e r = (∑ i ∈ range r, e i) - r * C`.
  - (M) is `∀ j, j + 1 < N → ŷ (j+1) ≤ ŷ j`.

**Notes on the statements:**
- **Lemma A1 and Corollary A3 are more general than in the file:** the hypothesis `det M ≠ 0` is not needed. Lemma A1 also holds for every `r`; for `r > n` both sides are `0`.
- **Hypothesis (M) is unused**, as the file predicts. `theorem_B` keeps it, under the name `_hM`, to match the file. `theorem_B_without_M` states the result without it, and `corollary_B'` proves that (F) and (U) alone make \(\hat y\) non-increasing.

**How the proofs go** (following the file):
- **Lemma A1:** Cauchy–Binet shows that every \(r\times r\) minor of \(PMQ\) is an integer combination of \(r\times r\) minors of \(M\). Then \(\mathrm{adj}(P)\,(PMQ)\,\mathrm{adj}(Q) = (\det P)(\det Q)\,M\), and multiplying by an odd integer does not change \(dd_r\).
- **Lemma A2:** a minor of a diagonal matrix is zero unless \(A = B\). The \(k\)-th element of an \(r\)-subset is at least \(k\), so for non-decreasing \(e\) the smallest sum is \(e_0+\dots+e_{r-1}\).
- **Theorem B:** \(\hat d\) is convex with \(\hat d(0)=0\), so `SmithBounds.lemma_6_4` together with (U) gives \(\hat d \le Y\), and (F) gives equality. Comparing increments gives \(e_i = C + \hat y_{N-1-i}\).

The Properties table lists the 11 results as proved, together with the definitions `minor`, `dd` and `dHat`.

# Summary of changes for run 339a7b11-8a73-4853-ab4f-fd76e2b73d7f
I formalized and proved every statement of `C4_golden_matching.md` in a new folder, `RequestProject/GoldenMatching/`, in namespace `GoldenMatching`. The whole project builds with no `sorry`, no new axioms and no `native_decide`. For each main theorem, `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. I did not change `AntitonicFit/`, `SmithBounds/` or `Rulers/`.

**Files** (each docstring names its part of the file; `All.lean` is an index):
- `Binary.lean`: **Theorem A** (`theorem_A`).
- `Dancers.lean`: **Theorem B** (`theorem_B`).
- `Complement.lean`: **Lemma C1**, split into four theorems (`lemma_C1_oE`, `lemma_C1_lt`, `lemma_C1_rank`, `lemma_C1_bijOn`), and **Lemma C2** (`lemma_C2`).
- `NaturalMinor.lean`: **Corollary D** (`corollary_D`).

**Encodings** (also given in the module docstrings):
- **Golden image:** `IsGoldenImage s p g` is the file's definition word for word: `g = p`, or some `j < s` has `p / 2^j = 2^(s−j) − 1` and `g = p % 2^j`.
- **Theorem A:** the rows are `Finset.Ico (2^s − r) (2^s)` and the columns are `Finset.range r`. A bijection is an equivalence between these two sets.
- **Dancers and `o_D`:** a dancer is any `D ∈ I.powerset`, and `o_D` is `Rulers.oE`. The hypothesis \(I \subseteq \{0,\dots,k-1\}\) is written `∀ t ∈ I, t < k`.
- **Rank, `L_r`, `F_r`:**
  - `rank I D` is `#{D' ⊆ I : oE D' < oE D}`.
  - `Lr I r` is `{D ⊆ I : 2^#I − r ≤ rank I D}`.
  - `Fr I r` is `{D ⊆ I : rank I D < r}`.
- **Golden arrow:** `IsGoldenArrow k I a b` means `b ⊆ a` and `Rulers.gamma k I (a \ b) = 0`.
- **"Exactly one":** stated as existence plus uniqueness (any two such bijections agree on every row), in both Theorem A and Theorem B.
- **Normalized cost, `x_D`, `U(r)`:**
  - `cHat` is \(\hat c(a,b) = R_\mu(a) - R_{\mu+K}(b) + \gamma(a\setminus b)\), with `R_μ = Rulers.ruler k I α μ`, `K = 2^k`, integer `α` and `μ : ℕ`.
  - `xVal` is \(x_D = R_\mu(D) - R_{\mu+K}(I\setminus D)\).
  - `U k I α μ r` is \(\sum_{D\in L_r} x_D\).
- **Corollary D:** `M` is a function from pairs of finite sets to `ℤ`. The minor is `Matrix.of fun i j => M (e i) (f j)`, and the result holds for every choice of `e : Fin r ≃ L_r` and `f : Fin r ≃ F_r`.

**Notes on the statements:**
- In Lemma C1, \(o_{I\setminus D} = o_I - o_D\) and \(\mathrm{rank}(I\setminus D) = N-1-\mathrm{rank}(D)\) are stated in `ℕ`. The subtraction never truncates, because `D ⊆ I` and `rank D < 2^#I` (proved).
- Three statements are slightly more general than in the file:
  - The bijection part of Lemma C1 holds for every `r`.
  - Lemma C2 needs no hypothesis on `I` or `r`.
  - In Corollary D, (S) is only assumed for pairs of dancers.

**How the proofs go** (following the file):
- **Theorem A:** induction on `s`, with the two cases \(r \le N/2\) (shift by \(N/2\)) and \(r = N/2+q\) (the middle rows are fixed).
- **Theorem B:** an increasing enumeration of `I` sends each dancer to a number \(p(D)\). This map preserves the order (via Mathlib's colexicographic order), so \(p(D) = \mathrm{rank}(D)\). Using C3's Lemma 5.1(b), it also turns golden arrows into golden images, so Theorem B is Theorem A carried over by \(p\).
- **Corollary D:** the golden bijection is the unique matching of least cost \(r\cdot C + U(r)\), by Lemma C2 and the uniqueness in Theorem B. The proof then concludes with `SmithBounds.corollary_B'` (with `p = 2`).

The Properties table lists the 8 results as proved, together with the definitions they use.

# Summary of changes for run b15574a9-78c4-4a84-b728-1b416e2ff975
I formalized and proved every statement of `C3_rulers_gold_clocks.md` in a new folder, `RequestProject/Rulers/`, in namespace `Rulers`. The whole project builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every main theorem. I did not change `AntitonicFit/` or `SmithBounds/`. As a quick sanity check I also evaluated the definitions on a few small families (`next`, `h`, `γ`, `δ`, `G`, and both sides of Propositions 5.3 and 5.4(c)). This was only an informal spot check, not a proof; the theorems are what is verified.

**Files** (each docstring names its part of the file; `All.lean` is an index):
- `Basic.lean`: the setting, plus both **Legendre sums** (`legendre_sum_shift`, `legendre_sum`).
- `Family.lean`: the family definitions, **Lemma 5.0** (`lemma_5_0_xi`, `lemma_5_0_sdiff`) and **Lemma 5.1** (a), (b) (`lemma_5_1_a`, `lemma_5_1_b`).
- `Bits.lean`: helper facts about binary digit counts.
- `CostForm.lean`: **Proposition 5.2** (`proposition_5_2`, the stated identity in `ℤ`) and **Proposition 5.4** (a), (b).
- `Clocks.lean`: **Proposition 5.3** (`proposition_5_3`, with \(\alpha = 1\)) and **Proposition 5.4 (c)**.

**Encodings** (also given in the module docstrings):
- **Digits and valuations:** `s2 x = (Nat.digits 2 x).count 1` and `v2 = padicValNat 2`.
- **κ, φ, o_E:** `kappa a b = s2 a + s2 b − s2 (a+b)` and `phi x = x + v2 x`, both in `ℤ`. `oE E = ∑ t ∈ E, 2^t`.
- **I:** `I : Finset ℕ`, with the hypothesis `hI : ∀ t ∈ I, t < k`. \(K = 2^k\) is written `2 ^ k`.
- **min:** `minOr k E` is `min E`, with the file's convention `min ∅ := k`.
- **next(t), h_t:** `next k I t = minOr k ((insert k I).filter (t < ·))`, i.e. \(\min\{u \in I\cup\{k\} : u > t\}\). Then `h k I t = next k I t − t`, `hSum` is \(h(E)\), and `G` is \(G(E)\) in `ℤ`.
- **λ:** `lam k I = 2^k + o_I − 1`, so \(\lambda + 1 = K + o_I\).
- **Deficit and gold:** `delta k Δ` and `gamma k I Δ` are defined as in the file, with `δ(∅) = γ(∅) = 0` by an explicit `if Δ = ∅`.
- **Rulers:** `ruler k I α μ E` is \(R_\mu(E)\) and `rulerSharp k I α E` is \(R^\sharp(E)\), with integer `α`.
- **ξ_D:** `xi k I D = lam + 1 − 2 o_D`, a natural number. Lemma 5.0 proves that this subtraction does not truncate and that \(\xi_D \ge 1\).
- **Raw clock:** `clock k I i D = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`. The subtraction `i + o_D − 1` is natural-number subtraction, which does not truncate when \((i,D) \ne (0,\emptyset)\), the only case used.
- **x_D, x^♯_D:** `xD k I m D` and `xSharp k I D`, with \(\alpha = 1\).
- **Sums:** \(\Sigma_{d=x}^{y-1}\) is a sum over `Finset.Ico x y`, and \(m = i-1\) is written `i - 1`.

**Notes on the statements:**
- In Propositions 5.2 and 5.4(b) I kept the hypothesis \(\alpha \ge 1\) because the file states it, but the proof does not use it: the identities hold for every integer \(\alpha\).
- Lemma 5.1(b) writes the tail as `I.filter (minOr k Δ ≤ ·)`.
- Proposition 5.4(a) is stated with the file's `if E = ∅ then 0 else k − min E`.

**How Proposition 5.3 is proved:** I reduced it to the carry count \(s_2(K-1-o_D+o_E) = k-|D|-G(E)\). This is proved by writing that number as \(o_F\) for an explicit set \(F\) of bit positions: \(\{0,\dots,t_1-1\}\), plus \(\{t+1,\dots,\mathrm{next}(t)-1\}\) for \(t \in D\), plus \(\{\mathrm{next}(t)\}\) for \(t \in E\). These pieces are pairwise disjoint, so \(s_2\) of the number is \(|F|\). Steps 2–3 of the file's proof then reduce to linear arithmetic.

The Properties table lists the 11 results as proved, together with the definitions they use.

# Summary of changes for run e0b97d3b-de3a-4859-8c1a-411333ea68b2
I formalized and proved every statement of `C2_smith_bounds.md` in the new folder `RequestProject/SmithBounds/`, in namespace `SmithBounds`. The whole project builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every main theorem. I did not touch `RequestProject/AntitonicFit/`.

**Files** (each docstring names its part of the file; `All.lean` is an index):
- `TropicalBound.lean`, **Part A**: `lemma_A1` and `lemma_A2`.
- `LeastTerm.lean`, **Part B**: `lemma_B` and `corollary_B'`.
- `Convexity.lean`, **Part C**: `lemma_C0_total` (\(Y(N)=U(N)\)), `lemma_C0` (the general form) and `lemma_6_4`. These are built on `AntitonicFit.ifit`, and Lemma C0 is proved from `AntitonicFit.consequence_L`.
- `TheoremU.lean`, **Part D**: `lemma_D0` and `theorem_U`.
- `Basic.lean`: the shared sum over the last \(r\) positions.

**Encodings** (also given in the module docstrings):
- **Minor `M[A,B]`:** `minor M e f = M.submatrix (e ·) (f ·)`. Here `e : Fin r ≃ A` lists the rows and `f : Fin r ≃ B` lists the columns, so these are the "fixed orders". Every result holds for every choice of `e` and `f`.
- **Matchings (Part A):** an `A→B` matching is an equivalence `β : A ≃ B` with `supp a (β a)`. Its cost is \(\sum_{a\in A} c(a,\beta a)\).
- **`U(r)`, `Y(r)`:** sums over `Finset.Ico (N - r) N` (the last \(r\) positions), of `x` and of `ifit N x` respectively.
- **Convexity:** `d : ℕ → ℤ` (only values at \(r \le N\) matter) is convex if \(d(r+1)-d(r) \le d(r+2)-d(r+1)\) whenever \(r+2 \le N\).
- **First position of a level set:** "`N − r` starts a level set of `fit(x)`" is written as `∃ q, IsLevelInterval N (fit N (toR x)) (N - r) q`.
- **`r`-matchings (Part D):** a set `Rows ⊆ {0,…,N−1}` with `|Rows| = r`, plus a map `β : ℕ → ℕ` that is injective on `Rows`, takes values `< N` there, and satisfies `arr a (β a)`.

**Where the statements differ slightly from the file** (all noted in the docstrings):
- **More general:**
  - In Part A the index type `n` need not be finite.
  - In Theorem U, condition (U3) is only assumed for arrows between positions `< N`, as the file says.
- **Unused hypotheses:**
  - In Lemma B, the hypothesis `p ≥ 2` is kept because you asked for it, but the proof does not need it.
  - In Corollary B′, the setting hypothesis \(p^{c(a,b)} \mid M\,a\,b\) is kept but is likewise not used.
- **Encoding of "exactly one matching of least cost `T`":** `β₀` is a matching of cost `T`, and every other matching costs more than `T`.

**A note on the proof of Lemma 6.4:** for each level set I used a shorter version of the paper's argument. Inside a level set the steps of \(Y\) are always \(q\) or \(q+1\), and \(Y = U\) at both ends of the level set (Lemma C0). Those two facts plus convexity are enough. The case split on \(r^* \le r_0+p-\rho\) is not needed, and neither is the order of the ceilings and floors inside the level set. This agrees with the file's note that putting the floors first only weakens the lemma.

The Properties table lists these results as proved, together with the definitions they use.

# Summary of changes for run 2b8cfa39-a66a-4a5d-9647-f3cb847d0e82
I formalized and proved in Lean 4 with Mathlib every statement of `C1_antitonic_fits.md`. All files are in `RequestProject/AntitonicFit/`, in namespace `AntitonicFit`. Everything builds with no `sorry`, no new axioms and no `native_decide`. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every main theorem.

**Encoding** (described in the module docstrings of `Basic.lean`, `Characterization.lean` and `IntegerFit.lean`):
- **Sequences:** a sequence of length `N` is a function `ℕ → ℝ`. Every notion only reads the positions below `N`, so equality of sequences is stated as `∀ j < N, …`.
- **Prefix, suffix, concatenation:** the prefix \(x_{<b}\) is the same function used with length `b`. The suffix \(x_{\ge b}\) is `shift b x = fun j => x (b + j)`, used with length `N - b`. The concatenation `[u, v]` is `concat M u v = fun j => if j < M then u j else v (j - M)`.
- **Mirror-negative and antisymmetry:** \(u^*\) is `mirror M u = fun j => -u (M-1-j)`, and `IsAntisymm N x` says `x (N-1-j) = -x j` for every `j < N`.
- **Level sets:** `levelSet N z j = {i < N : z i = z j}`. `IsLevelInterval N z p q` says that `[p, q]` is a level set. I also proved that for a non-increasing `z` every level set is such an interval.
- **`fit`:** defined as a non-increasing minimizer of \(\sum_j (x_j - z_j)^2\), chosen using the existence half of (0) and set to `0` at positions `≥ N`. It is not defined by an algorithm.
- **`ifit`:** integer sequences are `ℕ → ℤ`. On the level set `L` of `j` in `fit(x)`, with \(P = |L|\) and \(S = \sum_L x\), the value is \(\lceil S/P\rceil\) if the rank of `j` in `L` is below `S % P` (the non-negative remainder), and \(\lfloor S/P\rfloor\) otherwise. A lemma checks that the rank is `j − p` when `L = [p, q]`, which is exactly the rule in the file. Nothing claims `ifit` is non-increasing.

**Results** (each docstring names its part of the file):
- **(0):** `existsUnique_fit`.
- **Lemma 7.1:** `lemma_7_1`, the "iff" with the two level-set conditions.
- **(L):** `consequence_L`.
- **(D):** `consequence_D_cut` and `consequence_D_strict_iff`.
- **Lemma 7.2:** `lemma_7_2_a`, `lemma_7_2_b1`, `lemma_7_2_b2`, `lemma_7_2_b3` (plus `lemma_7_2_b3_b2`, which applies (b2)) and `lemma_7_2_c`. In (b1), the cut positions \(b_1 < \dots < b_s\) are a `Finset` `B`. "Constant on each interval between cuts" is written as \(\delta_{j+1} = \delta_j\) whenever `j+1 ∉ B`, which is equivalent.
- **Example `x = (3,4,3,4)`, `δ = (1,1,0,0)`:** `example_b2_hypothesis_needed` proves that `x` is cut at 2, the cut is not strict, and `ifit(x+δ) ≠ ifit(x)+δ` (they differ at position 1). I also proved \(\mathrm{fit}(x) = (7/2,7/2,7/2,7/2)\), \(\mathrm{ifit}(4,5,3,4) = (5,4,4,3)\), \(\mathrm{ifit}(x) = (4,4,3,3)\) and \(\mathrm{ifit}(x)+\delta = (5,5,3,3)\).
- **Antisymmetry:** `A1`, `A2`, `A3`. More generally, `fit_mirror` and `ifit_mirror` show that `fit` and `ifit` commute with mirror-negation for every sequence.
- **Lemma 7.3:** `lemma_7_3_Z2` (\(Z_2 = \mathrm{fit}(x_{\ge N'})\)), `lemma_7_3_fit` and `lemma_7_3_ifit`. The length \(2N'\) is written `2 * M`.
- **Other examples in the file** (in `Examples.lean`): `x = (−2,−2,0,−2,−1)` with its `fit` and `ifit` values, plus a proof that this `ifit` is not non-increasing; and the antisymmetric check `x = (2,−1,1,−2)`.

**Two statements are more general than in the file** (both noted in their docstrings):
- **(b2):** the hypotheses about the cuts \(b_i\), and about `δ` being constant between them, are dropped. The proof does not need them, because they follow from the remaining hypotheses.
- **(b3):** the first statement allows `δ` to take values in any type, not only integers.

`RequestProject/AntitonicFit/All.lean` imports everything and lists where each statement is. The Properties table lists these results, all marked proved.