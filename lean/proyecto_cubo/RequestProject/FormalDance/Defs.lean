module

public import RequestProject.FormalOps.All
public import RequestProject.Dance.All

/-!
# `C40b_the_formal_dance_of_payment_systems.md`: Definitions (new)

Namespace `FormalDance`. Nothing listed in the Setting of the file is redefined: `Bf A` (with
its ring structure `Bf.instRing` and its `A`-action), `Bf.fd`, `Bf.dg`, `tw00`, `tw11`, `tw10`,
`tw01`, `vplus`, `vprime`, `flD`, `act` are C40's (`FormalOps`), `Payment.pT`, `Payment.κT` are
C11's, `Split.pSp`, `Split.κSp` are C12's, and `Dance.slots`, `Dance.splitIso`, `Dance.relabP`,
`Dance.relabK`, `Dance.danceAux`, `Dance.dance`, `Dance.Mfin`, `Dance.pσ`, `Dance.κσ`,
`Dance.mCount` are C13's.

## Encodings
* Matrices over `Bf A` are Mathlib's `Matrix n n (Bf A)` (`n` a `Fintype` with `DecidableEq` when
  products or `1` are needed), with Mathlib's ring structure (`Bf A` is not commutative) and the
  entrywise action of `A` (`(a • G) s s' = a • G s s'`).
* `Agree`, `MAgree`, `ext0`, `paySys`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `Clean`
  and `finalM` are written exactly as in the file. In `paySys` the index type carries a
  `LinearOrder` (its decidable equality is the one of the order).
* `DanceRel ds r G Gk` is defined by recursion on `ds : List Bool`, with exactly the three clauses
  of the file; the final matrix lives on `Fin (Dance.slots ds r)` (C13's slot count, which equals
  `r * 2 ^ Dance.mCount ds` by `Dance.slots_eq`). In the split clause the matrix `G''` on
  `Fin r × Fin 2` is read on `Fin (r * 2)` through `ofLex ∘ (Dance.splitIso r).symm`.
-/

@[expose] public section

noncomputable section

namespace FormalDance

open FormalOps

variable {A : Type*} [CommRing A]

/-- Definitions (new) 1 of `C40b_the_formal_dance_of_payment_systems.md`: agreement of formal
operators at the floors `f ≥ m`. -/
def Agree (x y : Bf A) : Prop := ∀ (m : ℕ) (f : ℤ), (m : ℤ) ≤ f → x.coef m f = y.coef m f

/-- Definitions (new) 1 of `C40b_the_formal_dance_of_payment_systems.md`: entrywise agreement of
matrices over `Bf A`. -/
def MAgree {n : Type*} (G H : Matrix n n (Bf A)) : Prop := ∀ s s', Agree (G s s') (H s s')

/-- Definitions (new) 2 of `C40b_the_formal_dance_of_payment_systems.md`: extension by zero,
`ext0 q f = q f.toNat` for `f ≥ 0` and `0` for `f < 0`. -/
def ext0 (q : ℕ → A) : ℤ → A := fun f => if 0 ≤ f then q f.toNat else 0

/-- Definitions (new) 3 of `C40b_the_formal_dance_of_payment_systems.md`: the payment system
`F + 2π(D) + 2K(D)` with halved data `p`, `κ`; `G[s, s']` maps the source slot `s'` to the
coordinate slot `s`. -/
def paySys {n : Type*} [LinearOrder n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    Matrix n n (Bf A) := fun s s' =>
  if s = s' then Bf.fd 1 + Bf.dg (ext0 (fun f => 2 * p s f))
  else if s' < s then Bf.dg (ext0 (fun f => 2 * κ s s' f)) else 0

/-- Definitions (new) 4 of `C40b_the_formal_dance_of_payment_systems.md`: the pivot block
`P = G^{10}` (entrywise `tw10`). -/
def twP {n : Type*} (G : Matrix n n (Bf A)) : Matrix n n (Bf A) := fun s s' => tw10 (G s s')

/-- Definitions (new) 4 of `C40b_the_formal_dance_of_payment_systems.md`: the block `C = G^{11}`
(entrywise `tw11`). -/
def twC {n : Type*} (G : Matrix n n (Bf A)) : Matrix n n (Bf A) := fun s s' => tw11 (G s s')

/-- Definitions (new) 4 of `C40b_the_formal_dance_of_payment_systems.md`: the block `B = G^{00}`
(entrywise `tw00`). -/
def twB {n : Type*} (G : Matrix n n (Bf A)) : Matrix n n (Bf A) := fun s s' => tw00 (G s s')

/-- Definitions (new) 4 of `C40b_the_formal_dance_of_payment_systems.md`: the block `Dd = G^{01}`
(entrywise `tw01`). -/
def twD {n : Type*} (G : Matrix n n (Bf A)) : Matrix n n (Bf A) := fun s s' => tw01 (G s s')

/-- Definitions (new) 5 of `C40b_the_formal_dance_of_payment_systems.md`: the V-split of a
system, the block `[[x, 0], [x', x⁺]]` in each entry. -/
def vsplit {n : Type*} (G : Matrix n n (Bf A)) : Matrix (n × Fin 2) (n × Fin 2) (Bf A) :=
  fun q q' =>
    if q.2 = 0 ∧ q'.2 = 0 then G q.1 q'.1
    else if q.2 = 1 ∧ q'.2 = 0 then vprime (G q.1 q'.1)
    else if q.2 = 1 ∧ q'.2 = 1 then vplus (G q.1 q'.1) else 0

/-- Definitions (new) 6 of `C40b_the_formal_dance_of_payment_systems.md`: a clean move, `P`
invertible up to agreement with inverse `Q`, and `Dd − B Q C` agrees with `2 G'`. -/
def CleanStep {n : Type*} [Fintype n] [DecidableEq n] (G G' : Matrix n n (Bf A)) : Prop :=
  ∃ Q : Matrix n n (Bf A), MAgree (twP G * Q) 1 ∧ MAgree (Q * twP G) 1 ∧
    MAgree (twD G - twB G * Q * twC G) ((2 : A) • G')

/-- Definitions (new) 7 of `C40b_the_formal_dance_of_payment_systems.md`: the formal dance, by
recursion on `ds` (`[]`: agreement; `false`: a twist move; `true`: a V-split, a twist move and the
relabelling `Dance.splitIso` of C13). -/
def DanceRel : (ds : List Bool) → (r : ℕ) → Matrix (Fin r) (Fin r) (Bf A) →
    Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A) → Prop
  | [], _, G, Gk => MAgree G Gk
  | false :: rest, r, G, Gk => ∃ G', CleanStep G G' ∧ DanceRel rest r G' Gk
  | true :: rest, r, G, Gk => ∃ G'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf A),
      CleanStep (vsplit G) G'' ∧
      DanceRel rest (r * 2) (fun j j' => G'' (ofLex ((Dance.splitIso r).symm j))
        (ofLex ((Dance.splitIso r).symm j'))) Gk

/-- Definitions (new) 7 of `C40b_the_formal_dance_of_payment_systems.md`: the dance `ds` of `G`
is clean. -/
def Clean (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A)) : Prop :=
  ∃ Gk, DanceRel ds r G Gk

/-- Definitions (new) 8 of `C40b_the_formal_dance_of_payment_systems.md`: the final matrix, the
coefficient of `F^{(0)}` at the floor `0` of each entry. -/
def finalM {m : Type*} (Gk : Matrix m m (Bf A)) : Matrix m m A := fun s s' => (Gk s s').coef 0 0

end FormalDance
