module

public import RequestProject.FormalDance.PartL2

/-!
# `C40b_the_formal_dance_of_payment_systems.md`: Part L, (L3)–(L6) — relabelling, the formal
# dance of a payment system, uniqueness, scaling

* (L3) `L3`;
* (L4) `L4_dance`, `finalM_paySys`, `L4_sigma`, `L4_sigma_clean` (collected in `L4`);
* (L5) `L5`;
* (L6) `L6`.
-/

@[expose] public section

noncomputable section

namespace FormalDance

open FormalOps Finset Split Dance

variable {A : Type*} [CommRing A]

/-! ### (L3) -/

/-- **(L3)** of `C40b_the_formal_dance_of_payment_systems.md` (relabelling): for an order
isomorphism `e : n ≃o n'`, `paySys (relabP e p') (relabK e κ') = fun s s' => paySys p' κ' (e s) (e s')`. -/
theorem L3 {n n' : Type*} [LinearOrder n] [LinearOrder n'] (e : n ≃o n') (p' : n' → ℕ → A)
    (κ' : n' → n' → ℕ → A) :
    paySys (relabP e p') (relabK e κ') = fun s s' => paySys p' κ' (e s) (e s') := by
  funext s s'
  simp only [paySys, relabP, relabK, e.injective.eq_iff, e.lt_iff_lt]

/-! ### (L4) -/

/-- (L4) of `C40b_the_formal_dance_of_payment_systems.md` (Lemma 10.6(b)): the formal dance of a
payment system is the data dance,
`DanceRel ds r (paySys p κ) (paySys (danceAux ds r p κ).1 (danceAux ds r p κ).2)`. -/
theorem L4_dance (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    DanceRel ds r (paySys p κ) (paySys (danceAux ds r p κ).1 (danceAux ds r p κ).2) := by
  induction ds generalizing r with
  | nil => exact MAgree.refl _
  | cons d rest ih =>
    cases d
    · exact ⟨_, (L1 p κ).2.2, ih r _ _⟩
    · refine ⟨_, (L2 p κ).2.2, ?_⟩
      have := ih (r * 2) (relabP (splitIso r).symm (pSp p)) (relabK (splitIso r).symm (κSp p κ))
      rw [L3] at this
      exact this

/-- (L4) of `C40b_the_formal_dance_of_payment_systems.md`: the final matrix of a payment system
is C13's `Mfin`, `finalM (paySys p' κ') = Mfin p' κ'`. -/
theorem finalM_paySys {R : ℕ} (p' : Fin R → ℕ → A) (κ' : Fin R → Fin R → ℕ → A) :
    finalM (paySys p' κ') = Mfin p' κ' := by
  funext s s'
  simp only [finalM, paySys, Mfin]
  split_ifs <;> simp [ext0]

/-- (L4) of `C40b_the_formal_dance_of_payment_systems.md`, the corollary for `σ`: the witness
`Gk := paySys (danceAux ds 1 (pσ α i) κσ).1 (danceAux ds 1 (pσ α i) κσ).2` satisfies
`DanceRel ds 1 (paySys (pσ α i) κσ) Gk` and, for all `t t' : Fin (1 * 2 ^ mCount ds)`,
`finalM Gk (Fin.cast (slots_eq ds 1).symm t) (Fin.cast (slots_eq ds 1).symm t') =
Mfin (dance ds 1 (pσ α i) κσ).1 (dance ds 1 (pσ α i) κσ).2 t t'`. -/
theorem L4_sigma (ds : List Bool) (α i : ℕ) :
    DanceRel ds 1 (paySys (pσ (A := A) α i) κσ)
      (paySys (danceAux ds 1 (pσ (A := A) α i) κσ).1 (danceAux ds 1 (pσ α i) κσ).2) ∧
    ∀ t t' : Fin (1 * 2 ^ mCount ds),
      finalM (paySys (danceAux ds 1 (pσ (A := A) α i) κσ).1 (danceAux ds 1 (pσ α i) κσ).2)
          (Fin.cast (slots_eq ds 1).symm t) (Fin.cast (slots_eq ds 1).symm t') =
        Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ α i) κσ).2 t t' := by
  refine ⟨L4_dance ds 1 _ _, fun t t' => ?_⟩
  rw [finalM_paySys]
  simp only [Mfin, dance, relabP, relabK, Fin.castOrderIso_apply, Fin.cast_inj, Fin.cast_lt_cast]

/-- (L4) of `C40b_the_formal_dance_of_payment_systems.md`, the corollary for `σ` in the form of
the file: `Clean ds 1 (paySys (pσ α i) κσ)`, with a witness `Gk` whose final matrix read through
`Fin.cast (slots_eq ds 1).symm` is `Mfin (dance ds 1 (pσ α i) κσ)` (by C14, the matrix
`M^{(α)}(l, c)` of Theorem 4.4). -/
theorem L4_sigma_clean (ds : List Bool) (α i : ℕ) :
    Clean ds 1 (paySys (pσ (A := A) α i) κσ) ∧
    ∃ Gk, DanceRel ds 1 (paySys (pσ (A := A) α i) κσ) Gk ∧
      ∀ t t' : Fin (1 * 2 ^ mCount ds),
        finalM Gk (Fin.cast (slots_eq ds 1).symm t) (Fin.cast (slots_eq ds 1).symm t') =
          Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ α i) κσ).2 t t' :=
  ⟨⟨_, (L4_sigma ds α i).1⟩, _, L4_sigma ds α i⟩

/-- **(L4)** of `C40b_the_formal_dance_of_payment_systems.md` (Lemma 10.6(b)), collected: the
formal dance of every payment system is the data dance, and the final matrix of a payment system
is `Mfin`. -/
theorem L4 :
    (∀ (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A),
      DanceRel ds r (paySys p κ) (paySys (danceAux ds r p κ).1 (danceAux ds r p κ).2)) ∧
    (∀ (R : ℕ) (p' : Fin R → ℕ → A) (κ' : Fin R → Fin R → ℕ → A),
      finalM (paySys p' κ') = Mfin p' κ') :=
  ⟨L4_dance, fun _ => finalM_paySys⟩

/-! ### (L5) -/

lemma cleanStep_unique {n : Type*} [Fintype n] [DecidableEq n]
    (h2 : ∀ a : A, 2 * a = 0 → a = 0) {G H G' H' : Matrix n n (Bf A)} (hGH : MAgree G H)
    (hG : CleanStep G G') (hH : CleanStep H H') : MAgree G' H' := by
  obtain ⟨Q, hPQ, hQP, hS⟩ := hG
  obtain ⟨Q', hPQ', hQP', hS'⟩ := hH
  have hP := hGH.twP
  have hQ : MAgree Q Q' := by
    have e1 : MAgree Q (Q * (twP H * Q')) := by
      have := (MAgree.refl Q).mul hPQ'.symm
      rwa [mul_one] at this
    have e2 : MAgree (Q * twP H * Q') (Q * twP G * Q') :=
      ((MAgree.refl Q).mul hP.symm).mul (MAgree.refl Q')
    have e3 : MAgree (Q * twP G * Q') Q' := by
      have := hQP.mul (MAgree.refl Q')
      rwa [one_mul] at this
    rw [← mul_assoc] at e1
    exact e1.trans (e2.trans e3)
  have hD : MAgree (twD G - twB G * Q * twC G) (twD H - twB H * Q' * twC H) :=
    hGH.twD.sub ((hGH.twB.mul hQ).mul hGH.twC)
  have h22 : MAgree ((2 : A) • G') ((2 : A) • H') := hS.symm.trans (hD.trans hS')
  intro s s' m f hf
  have := h22 s s' m f hf
  simp only [Matrix.smul_apply, Bf.coef_smul] at this
  exact sub_eq_zero.mp (h2 _ (by rw [mul_sub, this, sub_self]))

lemma danceRel_unique (h2 : ∀ a : A, 2 * a = 0 → a = 0) (ds : List Bool) :
    ∀ (r : ℕ) (G H : Matrix (Fin r) (Fin r) (Bf A)) Gk Gk', MAgree G H →
      DanceRel ds r G Gk → DanceRel ds r H Gk' → MAgree Gk Gk' := by
  induction ds with
  | nil => intro r G H Gk Gk' hGH hG hH; exact hG.symm.trans (hGH.trans hH)
  | cons d rest ih =>
    cases d
    · rintro r G H Gk Gk' hGH ⟨G1, c1, d1⟩ ⟨H1, c2, d2⟩
      exact ih r G1 H1 Gk Gk' (cleanStep_unique h2 hGH c1 c2) d1 d2
    · rintro r G H Gk Gk' hGH ⟨G1, c1, d1⟩ ⟨H1, c2, d2⟩
      have hh := cleanStep_unique h2 hGH.vsplit c1 c2
      exact ih (r * 2) _ _ Gk Gk' (fun j j' => hh _ _) d1 d2

/-- **(L5)** of `C40b_the_formal_dance_of_payment_systems.md` (uniqueness): if `A` has no
`2`-torsion, two results `Gk`, `Gk'` of the formal dance `ds` of the same `G` agree, hence have
the same final matrix. -/
theorem L5 (h2 : ∀ a : A, 2 * a = 0 → a = 0) {ds : List Bool} {r : ℕ}
    {G : Matrix (Fin r) (Fin r) (Bf A)} {Gk Gk' : Matrix (Fin (slots ds r)) (Fin (slots ds r)) (Bf A)}
    (hk : DanceRel ds r G Gk) (hk' : DanceRel ds r G Gk') :
    MAgree Gk Gk' ∧ finalM Gk = finalM Gk' := by
  have h := danceRel_unique h2 ds r G G Gk Gk' (MAgree.refl G) hk hk'
  exact ⟨h, funext fun s => funext fun s' => h s s' 0 0 le_rfl⟩

/-! ### (L6) -/

section Smul

variable (u : A)

lemma tw00_smul (x : Bf A) : tw00 (u • x) = u • tw00 x := by ext q f; simp; ring
lemma tw11_smul (x : Bf A) : tw11 (u • x) = u • tw11 x := by ext q f; simp; ring
lemma tw10_smul (x : Bf A) : tw10 (u • x) = u • tw10 x := by ext q f; simp; ring
lemma tw01_smul (x : Bf A) : tw01 (u • x) = u • tw01 x := by
  ext q f; rcases q with _ | q <;> simp; ring
lemma vplus_smul (x : Bf A) : vplus (u • x) = u • vplus x := by ext q f; simp
lemma vprime_smul (x : Bf A) : vprime (u • x) = u • vprime x := by ext q f; simp

variable {n : Type*} (G : Matrix n n (Bf A))

lemma twP_smul : twP (u • G) = u • twP G := by funext s s'; exact tw10_smul u _
lemma twC_smul : twC (u • G) = u • twC G := by funext s s'; exact tw11_smul u _
lemma twB_smul : twB (u • G) = u • twB G := by funext s s'; exact tw00_smul u _
lemma twD_smul : twD (u • G) = u • twD G := by funext s s'; exact tw01_smul u _

lemma vsplit_smul : vsplit (u • G) = u • vsplit G := by
  funext q q'
  simp only [vsplit, Matrix.smul_apply]
  split_ifs
  · rfl
  · exact vprime_smul u _
  · exact vplus_smul u _
  · exact (smul_zero u).symm

end Smul

lemma cleanStep_smul {n : Type*} [Fintype n] [DecidableEq n] {u : A} (hu : IsUnit u)
    {G G' : Matrix n n (Bf A)} (h : CleanStep G G') : CleanStep (u • G) (u • G') := by
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨Q, hPQ, hQP, hS⟩ := h
  have hvv : ((v⁻¹ : Aˣ) : A) * (v : A) = 1 := Units.inv_mul v
  have hvv' : (v : A) * ((v⁻¹ : Aˣ) : A) = 1 := Units.mul_inv v
  refine ⟨((v⁻¹ : Aˣ) : A) • Q, ?_, ?_, ?_⟩
  · rw [twP_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hvv', one_smul]; exact hPQ
  · rw [twP_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hvv, one_smul]; exact hQP
  · have : twD (((v : A)) • G) - twB ((v : A) • G) * (((v⁻¹ : Aˣ) : A) • Q) * twC ((v : A) • G) =
        (v : A) • (twD G - twB G * Q * twC G) := by
      rw [twD_smul, twB_smul, twC_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
      congr 2
      linear_combination (v : A) * hvv'
    rw [this, smul_comm (2 : A) (v : A) G']
    exact hS.smul _

/-- **(L6)** of `C40b_the_formal_dance_of_payment_systems.md` (Lemma 10.6(b), last sentence,
scaling): if `u` is a unit and `DanceRel ds r G Gk`, then `DanceRel ds r (u • G) (u • Gk)`, and
`finalM (u • Gk) = u • finalM Gk`. -/
theorem L6 {u : A} (hu : IsUnit u) {ds : List Bool} {r : ℕ} {G : Matrix (Fin r) (Fin r) (Bf A)}
    {Gk : Matrix (Fin (slots ds r)) (Fin (slots ds r)) (Bf A)} (h : DanceRel ds r G Gk) :
    DanceRel ds r (u • G) (u • Gk) ∧ finalM (u • Gk) = u • finalM Gk := by
  refine ⟨?_, rfl⟩
  induction ds generalizing r with
  | nil => exact MAgree.smul u h
  | cons d rest ih =>
    cases d
    · obtain ⟨G', c, d⟩ := h
      exact ⟨u • G', cleanStep_smul hu c, ih d⟩
    · obtain ⟨G'', c, d⟩ := h
      refine ⟨u • G'', ?_, ih d⟩
      rw [vsplit_smul]
      exact cleanStep_smul hu c

end FormalDance
