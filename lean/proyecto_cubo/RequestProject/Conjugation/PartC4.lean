module

public import RequestProject.Conjugation.PartC2
public import RequestProject.InvFloors.Digits

/-!
# `C45_conjugation_and_general_eta.md`: Part C, (C4) and (C5) — the dance and the final matrix

* `qSlot ds r j : Fin r` is the slot `⌊j / 2^m⌋` (`m = Dance.mCount ds`) of the start from which
  the final slot `j` comes.
* `wkRec` is the recursive description of the final weights (a twist move squares `u`; a split
  move multiplies the weight of the new `V`-slot `b` by `u ^ b` and relabels along
  `Dance.splitIso`); `wkRec_eq` proves that it equals the closed form of the file,
  `w_k j = w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j)`, for every `r`.
* (C4) `C4` (with the closed-form weights; `C4_rec` with `wkRec`).
* (C5) `finalM_cjSys` and the case `r = 1`, `w = 1`, `c = 1`: `C5_one`; collected in `C5`.
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset

variable {A : Type*} [CommRing A]

/-- (C4) of `C45_conjugation_and_general_eta.md` (auxiliary): `⌊j / 2^m⌋ < r` for a final slot
`j < slots ds r = r * 2^m`. -/
lemma qSlot_lt (ds : List Bool) (r : ℕ) (j : Fin (Dance.slots ds r)) :
    (j : ℕ) / 2 ^ Dance.mCount ds < r := by
  have hj : (j : ℕ) < r * 2 ^ Dance.mCount ds := Dance.slots_eq ds r ▸ j.2
  exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hj)

/-- (C4) of `C45_conjugation_and_general_eta.md`: the slot `q j = ⌊j / 2^m⌋` of the start
(`m = Dance.mCount ds`) from which the final slot `j` comes. -/
def qSlot (ds : List Bool) (r : ℕ) (j : Fin (Dance.slots ds r)) : Fin r :=
  ⟨(j : ℕ) / 2 ^ Dance.mCount ds, qSlot_lt ds r j⟩

/-- (C4) of `C45_conjugation_and_general_eta.md`: the recursive description of the final
weights `w_k` (equal to the closed form of the file by `wkRec_eq`). -/
def wkRec : (ds : List Bool) → (r : ℕ) → Aˣ → (Fin r → Aˣ) → Fin (Dance.slots ds r) → Aˣ
  | [], _, _, w => w
  | false :: rest, r, u, w => wkRec rest r (u ^ 2) w
  | true :: rest, r, u, w => wkRec rest (r * 2) (u ^ 2)
      (fun j => w (ofLex ((Dance.splitIso r).symm j)).1 *
        u ^ ((ofLex ((Dance.splitIso r).symm j)).2 : ℕ))

lemma splitIso_symm_val (r : ℕ) (i : Fin (r * 2)) :
    ((ofLex ((Dance.splitIso r).symm i)).1 : ℕ) = i / 2 ∧
      ((ofLex ((Dance.splitIso r).symm i)).2 : ℕ) = i % 2 := by
  set x := (Dance.splitIso r).symm i
  have hi : (i : ℕ) = 2 * (ofLex x).1 + (ofLex x).2 := by
    have h := Dance.splitIso_val r (ofLex x).1 (ofLex x).2
    rw [show toLex ((ofLex x).1, (ofLex x).2) = x from rfl, OrderIso.apply_symm_apply] at h
    exact h
  have h2 := (ofLex x).2.2
  omega

/-- (C4) of `C45_conjugation_and_general_eta.md`: the recursive weights are the closed form of
the file, `wkRec ds r u w j = w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j)` (for every
`r`). -/
theorem wkRec_eq (ds : List Bool) : ∀ (r : ℕ) (u : Aˣ) (w : Fin r → Aˣ) (j : Fin (Dance.slots ds r)),
    wkRec ds r u w j = w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j) := by
  induction ds with
  | nil =>
    intro r u w j
    have hq : qSlot [] r j = j := by ext; simp [qSlot, Dance.mCount]
    have hD : Windows.Dset [] (j : ℕ) = ∅ := by simp [Windows.Dset, Windows.Ids]
    rw [hq, hD]
    simp [wkRec, Rulers.oE]
  | cons d rest ih =>
    cases d
    · intro r u w j
      show wkRec rest r (u ^ 2) w j = _
      rw [ih, InvFloors.oE_Dset_cons_false, pow_mul]
      rfl
    · intro r u w j
      show wkRec rest (r * 2) (u ^ 2) _ j = _
      rw [ih, InvFloors.oE_Dset_cons_true, pow_add, pow_mul, ← mul_assoc]
      obtain ⟨h1, h2⟩ := splitIso_symm_val r (qSlot rest (r * 2) j)
      have hq : (ofLex ((Dance.splitIso r).symm (qSlot rest (r * 2) j))).1 =
          qSlot (true :: rest) r j := by
        ext
        rw [h1]
        simp only [qSlot, Dance.mCount, pow_succ, Nat.div_div_eq_div_mul]
      rw [hq, h2]
      rfl

lemma scal_c (c u : Aˣ) (k : ℕ) :
    c * u⁻¹ * (u ^ 2)⁻¹ ^ (2 ^ k - 1) = c * u⁻¹ ^ (2 ^ (k + 1) - 1) := by
  rw [← inv_pow, ← pow_mul, mul_assoc, ← pow_succ']
  congr 2
  have := Nat.one_le_two_pow (n := k)
  rw [pow_succ]
  omega

lemma scal_u (u : Aˣ) (k : ℕ) : (u ^ 2) ^ (2 ^ k) = u ^ (2 ^ (k + 1)) := by
  rw [← pow_mul, pow_succ, mul_comm]

/-- (C4) of `C45_conjugation_and_general_eta.md`, with the recursive weights `wkRec`. -/
theorem C4_rec (ds : List Bool) : ∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A))
    (c u : Aˣ) (w : Fin r → Aˣ), DanceRel ds r G Gk →
    DanceRel ds r (cjSys c u w G)
      (cjSys (c * u⁻¹ ^ (2 ^ ds.length - 1)) (u ^ 2 ^ ds.length) (wkRec ds r u w) Gk) := by
  induction ds with
  | nil =>
    intro r G Gk c u w h
    show MAgree (cjSys c u w G) (cjSys (c * u⁻¹ ^ (2 ^ 0 - 1)) (u ^ 2 ^ 0) w Gk)
    simpa using magree_cjSys c u w h
  | cons d rest ih =>
    cases d
    · rintro r G Gk c u w ⟨G', hc, hd⟩
      refine ⟨cjSys (c * u⁻¹) (u ^ 2) w G', cleanStep_cjSys c u w hc, ?_⟩
      have := ih r G' Gk (c * u⁻¹) (u ^ 2) w hd
      rw [scal_c, scal_u] at this
      exact this
    · rintro r G Gk c u w ⟨G'', hc, hd⟩
      refine ⟨cjSys (c * u⁻¹) (u ^ 2) (fun q => w q.1 * u ^ (q.2 : ℕ)) G'',
        cleanStep_vsplit_cjSys c u w hc, ?_⟩
      have := ih (r * 2) _ Gk (c * u⁻¹) (u ^ 2)
        (fun j => w (ofLex ((Dance.splitIso r).symm j)).1 *
          u ^ ((ofLex ((Dance.splitIso r).symm j)).2 : ℕ)) hd
      rw [scal_c, scal_u] at this
      exact this

/-- **(C4)** of `C45_conjugation_and_general_eta.md` (the dance): for every `ds`, `r`,
`G : Matrix (Fin r) (Fin r) (Bf A)`, `Gk` with `DanceRel ds r G Gk`, and units `c`, `u`,
`w : Fin r → Aˣ`:
`DanceRel ds r (cjSys c u w G) (cjSys (c * u⁻¹ ^ (2 ^ k − 1)) (u ^ 2 ^ k) w_k Gk)` with
`k = ds.length` and `w_k j = w (q j) * u ^ Rulers.oE (Windows.Dset ds j)`, where
`q j = qSlot ds r j` is the slot `⌊j / 2^m⌋` of the start. -/
theorem C4 (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A))
    (hG : DanceRel ds r G Gk) (c u : Aˣ) (w : Fin r → Aˣ) :
    DanceRel ds r (cjSys c u w G)
      (cjSys (c * u⁻¹ ^ (2 ^ ds.length - 1)) (u ^ 2 ^ ds.length)
        (fun j => w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j)) Gk) := by
  have h := C4_rec ds r G Gk c u w hG
  rwa [show wkRec ds r u w = fun j => w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j) from
    funext (wkRec_eq ds r u w)] at h

/-- (C5) of `C45_conjugation_and_general_eta.md`: the final matrix of a conjugated system,
`finalM (cjSys c u w G) s s' = (c * w s * (w s')⁻¹ : A) * finalM G s s'`. -/
theorem finalM_cjSys {n : Type*} (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) (s s' : n) :
    finalM (cjSys c u w G) s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) * finalM G s s' := by
  simp [finalM, cjSys_apply]

/-- (C5) of `C45_conjugation_and_general_eta.md`, the case `r = 1`, `w = 1`, `c = 1`: if
`DanceRel ds 1 (fun _ _ => x) Gk`, there is `Gk'` with `DanceRel ds 1 (fun _ _ => cj u x) Gk'`
and `finalM Gk' s s' = (u ^ o(D_s) * (u⁻¹) ^ o(D_{s'}) * (u⁻¹) ^ (2 ^ k − 1) : A) * finalM Gk s s'`
for all `s, s'` (`k = ds.length`, `D_s = Windows.Dset ds s`, `o = Rulers.oE`). -/
theorem C5_one {ds : List Bool} (u : Aˣ) (x : Bf A)
    {Gk : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf A)}
    (h : DanceRel ds 1 (fun _ _ => x) Gk) :
    ∃ Gk' : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf A),
      DanceRel ds 1 (fun _ _ => cj (u : A) x) Gk' ∧
      ∀ s s', finalM Gk' s s' =
        ((u : A) ^ Rulers.oE (Windows.Dset ds s) *
          ((u⁻¹ : Aˣ) : A) ^ Rulers.oE (Windows.Dset ds s') *
          ((u⁻¹ : Aˣ) : A) ^ (2 ^ ds.length - 1)) * finalM Gk s s' := by
  have h4 := C4 ds 1 _ Gk h 1 u (fun _ => 1)
  have hx : cjSys (1 : Aˣ) u (fun _ => (1 : Aˣ)) (fun _ _ => x : Matrix (Fin 1) (Fin 1) (Bf A)) =
      fun _ _ => cj (u : A) x := by
    funext s s'; simp [cjSys_apply]
  rw [hx] at h4
  refine ⟨_, h4, fun s s' => ?_⟩
  rw [finalM_cjSys]
  congr 1
  simp only [one_mul, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- **(C5)** of `C45_conjugation_and_general_eta.md` (the final matrix), collected. -/
theorem C5 :
    (∀ {n : Type*} (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) (s s' : n),
      finalM (cjSys c u w G) s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) * finalM G s s') ∧
    (∀ (ds : List Bool) (u : Aˣ) (x : Bf A)
      (Gk : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf A)),
      DanceRel ds 1 (fun _ _ => x) Gk →
      ∃ Gk' : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf A),
        DanceRel ds 1 (fun _ _ => cj (u : A) x) Gk' ∧
        ∀ s s', finalM Gk' s s' =
          ((u : A) ^ Rulers.oE (Windows.Dset ds s) *
            ((u⁻¹ : Aˣ) : A) ^ Rulers.oE (Windows.Dset ds s') *
            ((u⁻¹ : Aˣ) : A) ^ (2 ^ ds.length - 1)) * finalM Gk s s') :=
  ⟨fun c u w G s s' => finalM_cjSys c u w G s s', fun _ u x _ h => C5_one u x h⟩

end Conjugation
