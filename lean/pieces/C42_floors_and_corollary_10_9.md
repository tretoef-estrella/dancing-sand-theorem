# C42 — The floors of `inH`, `outH`, and Corollary 10.9 (paper v8 §10.4)

*Lean piece C42 of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/InvFloors/`, namespace `InvFloors`. Do not change any earlier file.*

C41 proved Lemma 10.8 with maps `InvBlock.inH l r`, `InvBlock.outH l r` that depend only on `l` and `r`. This piece says what they are: `inH` sends the final slot `j` to ONE basis vector of `T(l)`, in the slot `⌊j / 2^m⌋` of `T(l)^{⊕r}`, at the floor `o_D` (`D` the dancers of `j`); `outH` reads the slot `j` off ONE basis vector, in the same slot of `T(l)^{⊕r}`, at the floor `o_D + 2^k − 1`. Then Corollary 10.9: the entries of the inverse final matrix are coefficients of the formal inverse `Ξ^{−1}` at one floor, times constants of the word.

## Setting (reuse; do not redefine)

- C3 `Rulers.oE` (`oE E = Σ_{t ∈ E} 2^t`); C13 `Dance.slots`, `Dance.slots_eq`, `Dance.mCount`, `Dance.splitIso`; C14 `Windows.Dset` (the dancers of a final slot `s : ℕ`: `{t ∈ I(ds) : Nat.testBit s (mCount ds − 1 − rank t)}`).
- C18 `DPLattice` (`ι`, `wt`, `Fd`), `DPLattice.one`; C20 `Doubling.phi` (`phiWt (e, i) = 2 wt i + wtV e`); C23 `tensorV`; C29 `Filt.T` (`T_zero`, `T_odd`, `T_even`); C32 `Families.ds`.
- C40 `FormalOps.Bf` (`coef : ℕ → ℤ → A`, the coefficient of `F^{(m)}` at the TARGET floor), `FormalOps.fd`; C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`; C40c `FormalAct.sysAct`, `A1`, `A2` (`sysAct_mul`, `sysAct_one`); C41 `InvBlock.inH`, `outH`, `inj0`, `out1`, `relab`, `castLat`, `ri`, `V3`, `V5`; C40d `FormalProp.splitEquiv`.

`A` is a commutative ring with `[IsDomain A] [CharZero A] [OddUnits A]`. Write `ds := Families.ds l`, `k := ds.length`, `m := Dance.mCount ds`, `ns := Dance.slots ds r` (`= r * 2^m`, C13 `slots_eq`). The **floor** of a basis index `i` of `T A l` is `(l − wt i) / 2`; we state it as `(l : ℤ) − (T A l).wt i = 2 * (floor)`.

## Statements to prove

**Definitions (new).** `slotOf (l r : ℕ) : Fin (Dance.slots (Families.ds l) r) → Fin r`, `inIdx (l r : ℕ) : Fin (Dance.slots (Families.ds l) r) → (T A l).ι`, `outIdx (l r : ℕ) : Fin (Dance.slots (Families.ds l) r) → (T A l).ι`, by the same recursion along `l` as `inH`, `outH` (twist step: the index `(0, i)` for `inIdx`, `(1, i)` for `outIdx` in `Fin 2 × ι`; split step: through `vpack` and `FormalProp.splitEquiv`). Depending only on `l`, `r`.

- **(F1) `inH` is a basis injection.** For every `j`: `InvBlock.inH l r (Pi.single j 1) = Pi.single (slotOf l r j) (Pi.single (inIdx l r j) 1)`.
- **(F2) `outH` is a basis reading.** For every `w` and `j`: `InvBlock.outH l r w j = w (slotOf l r j) (outIdx l r j)`.
- **(F3) The slot.** `((slotOf l r j : Fin r) : ℕ) = (j : ℕ) / 2 ^ m`.
- **(F4) The coordinate floor.** `(l : ℤ) − (T A l).wt (inIdx l r j) = 2 * (Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ)`.
- **(F5) The source floor.** `(l : ℤ) − (T A l).wt (outIdx l r j) = 2 * ((Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) + 2 ^ k − 1)`.
- **(F6) The word bound.** `Rulers.oE (Windows.Dset (Families.ds l) j) + 2 ^ k − 1 ≤ l` (both floors lie in `[0, l]`).

**The constants of the word.** For `l X Y : ℕ`-indexed final slots `X Y : Fin (Dance.slots (Families.ds l) 1)` put `oX := oE (Dset ds X)`, `oY := oE (Dset ds Y)`, and, when `oX ≤ oY + 2^k − 1`, `L := oY + 2^k − 1 − oX` and
  `γ l X Y := InvBlock.outH l 1 (fun s => (T A l).Fd L (InvBlock.inH l 1 (Pi.single X 1) s)) Y`
(`F^{(L)}` applied to the coordinate vector of `X`, read at the source `Y`); `γ l X Y := 0` when `oX > oY + 2^k − 1`. It depends only on `l`.

- **(C109) Corollary 10.9.** Let `K` be a field with `[CharZero K] [OddUnits K]`, `l : ℕ`, `B ≥ l + 1`, `Ξ Y : Bf K` with `Agree (Ξ * Y) 1` and `Agree (Y * Ξ) 1`, and `Gk` with `DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Gk`. Then `IsUnit (finalM Gk).det`, and for all `X Y' : Fin (Dance.slots (Families.ds l) 1)`:
  - if `oX ≤ oY' + 2^k − 1`: `(finalM Gk)⁻¹ Y' X = 2 ^ k * γ l X Y' * Y.coef (oY' + 2^k − 1 − oX) ((oY' + 2^k − 1 : ℕ) : ℤ)`;
  - if `oX > oY' + 2^k − 1`: `(finalM Gk)⁻¹ Y' X = 0`.
(The paper's `γ_{YX}` is `γ l X Y'` here, and `y_L(o_Y + K − 1)` is `Y.coef L (o_Y + K − 1)`.)

## Proof sketch
- (F1)–(F3): induction along `l` with the recursions of `inH`, `outH`, `inIdx`, `outIdx`, `slotOf`. Twist step: `inj0 (Pi.single s (Pi.single i 1)) = Pi.single s (Pi.single (0, i) 1)` (`pack`), `out1 w s i = w s (1, i)`. Split step: `vpack` sends the slot `(s, a)` and the index `(e, i)` to the slot `s` and the index `(a, (e, i))`; `splitEquiv r j = (j / 2, j % 2)` (`finProdFinEquiv`), so the slot of `T(l)^{⊕r}` is `(j / 2^{m'}) / 2 = j / 2^{m'+1}` (`Nat.div_div_eq_div_mul`). `castLat` and `ri` do not move basis vectors.
- (F4)–(F6): induction with the weights `phiWt (e, i) = 2 wt i + wtV e` (`wtV 0 = 1`, `wtV 1 = −1`) and `tensorWt (a, i) = wtV a + wt i`, top `l = 2l' + 1` or `2l' + 2`. Twist step: floor `2f` for `(0, i)` and `2f + 1` for `(1, i)`; the new digit is not a dancer, `o` doubles and `2^k = 2 · 2^{k−1}`: coordinate `2 o' = o`, source `2 (o' + 2^{k−1} − 1) + 1 = o + 2^k − 1`. Split step: the `V`-coordinate `a` (the dancer bit `v` of the first split, the highest bit of `j mod 2^m`, `Windows.Dset` with rank 0) adds `a` to the floor; with `o = 2 o' + a`: coordinate `2 o' + a`, source `2 (o' + 2^{k−1} − 1) + 1 + a = o + 2^k − 1`. The C14 lemmas on `Ids`, `rank`, `Dset` of `d :: rest` give the bit bookkeeping. (F6) from the weight bound of C40c (N2) (`wt ≥ −l`, i.e. floor ≤ l) or directly from `l + 1 = 2^k + Σ_{t ∈ I} 2^t`.
- (C109): `Agree (Ξ * Y) 1`, `Agree (Y * Ξ) 1`, (A1) and (A2) make `sysAct (fun _ _ => Ξ)` a linear equivalence `e` with inverse `sysAct (fun _ _ => Y)`; C41 (V5) gives `IsUnit` and `(finalM Gk)⁻¹ = 2^k outH ∘ sysAct Y ∘ inH`. By (F1), `inH (Pi.single X 1)` is the basis vector at floor `oX`; `act Y = Σ_{L'} flD (Y.coef L') ∘ F^{(L')}` puts `F^{(L')}` of it at floor `oX + L'`, with the coefficient at that target floor; by (F2), (F5) `outH` at `Y'` reads the basis vector at floor `oY' + 2^k − 1`, so only `L' = oY' + 2^k − 1 − oX` survives (a basis vector of floor `g` has a non-zero component only at floor `g`), and none if `oX > oY' + 2^k − 1`.

## Checks done before sending
- Brute force `chkC42.py` (built on `chkC41.py`: independent lattice model of `T(λ)` over `ℚ` with the nested bases of `Φ` and `V ⊗ −`, the lift along the data dance, formal operators as tables with `MMAX = 10`). For `l ≤ 7`, `r = 1, 2, 3`: every final slot `j` is sent by `I` to one basis vector and read by `O` off one basis vector; the slot is `⌊j / 2^m⌋`; the coordinate floor is `o_D` and the source floor is `o_D + 2^k − 1` with `D` = the dancers of `j` by the rule of C14 `Dset`. Corollary 10.9 for `r = 1`, `Ξ = F + 2p(D)` with `p ≠ 0` (three random `p` per `l`) and `σ^{(α)}_i` (`α = 1, 2, 3`, `i = 1, 2, 5`), `l ≤ 7`: the formal inverse by the series `Σ_s (−π^{−1}F)^s π^{−1}` acts as the inverse on `T(l)`, and `(M^{−1})_{YX} = 2^k γ_{YX} y_L(o_Y + 2^k − 1)` entry by entry, with `0` when `L < 0`. **528 checks, 0 failures.** `logs/chkC42.log`.
- Controls (all five fire): `L` without the `− 1`; `y_L` read at the floor `o_X` instead of the target floor; the factor `2^{k−1}`; the source floor written `o_D + 2^k`; the slot written `j mod r`.
- Errors of my first runs, all in the test: the formal inverse divided by `π(f) = 0` at negative floors (floors `< 0` never act; the inverse is now built on floors `≥ 0`), and a random table too short for the dance's floors `2f + 2`. Repaired before sending; no statement changed.

## Notes
- §10.4: C41 (Lemma 10.8, certified or running), C42 (this piece), C43 (Lemmas 10.10, 10.11 and Theorem 10.12).
