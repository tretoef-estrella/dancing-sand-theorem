module

public import RequestProject.Dance.Basic
public import RequestProject.Dance.Relabel
public import RequestProject.Dance.D1
public import RequestProject.Dance.D2
public import RequestProject.Dance.D3
public import RequestProject.Dance.Proposition

/-!
# The dance (`C13_the_dance.md`)

Index of the formalization (namespace `Dance`).  Everything is over an arbitrary commutative ring
`A`, all modules of the tower being `A`.  Reused unchanged: from `C11_payment_systems_twist.md`
(`RequestProject/Payment/`) `Payment.Sys`, `Payment.slotLof`, `Payment.slotEmb`, `Payment.G`
(halved data), `Payment.NΦ`, `Payment.flΦ`, `Payment.FΦ`, `Payment.pT`, `Payment.κT`,
`Payment.theorem_A`; from `C12_split_move.md` (`RequestProject/Split/`) `Split.NΨ`, `Split.flΨ`,
`Split.FΨ`, `Split.pSp`, `Split.κSp`, `Split.theorem_B`.

## Encodings (`Basic.lean`, the *Setting*)

* `nLen ds = ds.length` (`n(ds)`), `mCount ds` = number of `true` entries (`m(ds)`, by recursion;
  `mCount_eq_count`).
* **Tower `T(ds)`**, by recursion on `ds : List Bool`: index type `Idx ds` (`Unit`,
  `Idx rest × Fin 2`, `Idx rest × Fin 4`), floor `fl ds` (`0`, `flΦ`, `flΨ`), operator `F A ds`
  (`0`, `FΦ`, `FΨ`), all modules `A`; `SysT A ds S = Payment.Sys (fun _ : Idx ds => A) S`.
* **Relabelling**: `relabP e p' = p' ∘ e`, `relabK e κ' s u = κ' (e s) (e u)` for `e : S ≃o S'`;
  `splitIso r : Lex (Fin r × Fin 2) ≃o Fin (r * 2)`, `(s, j) ↦ 2s + j` (`finProdFinEquiv ∘ ofLex`).
* **Dance data**: `danceAux ds r p κ` follows the recursion of the Setting on `Fin (slots ds r)`;
  `dance ds r p κ` is it read on `Fin (r * 2^{m(ds)})` through `Fin.castOrderIso (slots_eq ds r)`
  (`dance_nil`, `dance_false`, `dance_true` give the recursion equations up to this cast).
* **Final matrix** `Mfin p κ`, **operator `σ`**: `pσ α i`, `κσ = 0`, `sigma A ds α i`.
* **Clocks** `Clocks A ds r h : ModuleCat A`, by the recursion of (D1).
* `c · G` is `c • G`, `c · ⊤` is the pointwise scalar multiple `c • ⊤`.

## Results

* **(R1)** `R1_intertwine` (with the slotwise relabelling `relabSys`, `relabSys_slotLof`) and
  `R1_coker` (`Relabel.lean`).
* **(D1)** `D1_scaled_dance` (`D1.lean`).
* **(D2)** `D2_clocks` (`D2.lean`).
* **(D3)** `D3_final_matrix`, with `D3_intertwine` (`D3.lean`).
* **Proposition 4.3** `proposition_4_3` and **(D4)** `D4_lower_triangular_even`
  (`Proposition.lean`).
-/
