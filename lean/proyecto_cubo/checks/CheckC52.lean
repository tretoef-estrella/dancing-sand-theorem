import RequestProject.OddParts.All

/-! Auditor's check file for Lean piece C52: the odd parts (Grepy Escribano, 10 Oct 2026).
Restated by hand from `C52_odd_parts.md`; definitions checked by `rfl` where possible;
then `#print axioms`. -/

open CubeLaplacian OddParts

-- definitions by rfl
example (p : ℕ) (T : Type) [AddCommGroup T] (y : T) :
    (y ∈ Sylp p T) = (∃ k : ℕ, (p ^ k : ℕ) • y = 0) := rfl
example (n : ℕ) (S : Finset (Fin n)) (g : G n) :
    chi n S g = (-1) ^ (∑ i ∈ S, (g i).val) := rfl
example (n : ℕ) (f : G n → ℤ) (S : Finset (Fin n)) :
    fourier n f S = ∑ g, chi n S g * f g := rfl
example (n : ℕ) (v : Finset (Fin n) → ℤ) (g : G n) :
    ifourier n v g = ∑ S, chi n S g * v S := rfl
example (n : ℕ) (v : Finset (Fin n) → ℤ) (S : Finset (Fin n)) :
    diagD n v S = 2 * S.card * v S := rfl
example (n : ℕ) : EvenS n = {S : Finset (Fin n) // Even S.card} := rfl
example (n : ℕ) (v : EvenS n → ℤ) (S : EvenS n) :
    diagDBar n v S = 2 * S.1.card * v S := rfl

-- (Q0)
example (T : Type) [AddCommGroup T] : Sylp 2 T = Syl2 T := Q0 T
-- (Q1)
example {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (g : B →+ A) (m : ℕ)
    (hgf : ∀ a, g (f a) = m • a) (hfg : ∀ b, f (g b) = m • b) (p : ℕ) (hp : p.Prime)
    (hpm : ¬ p ∣ m) : Nonempty (Sylp p A ≃+ Sylp p B) := Q1 f g m hgf hfg p hp hpm
-- (Q2)
example (A B : Type) [AddCommGroup A] [AddCommGroup B] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylp p (A × B) ≃+ Sylp p A × Sylp p B) ∧ Sylp p ℤ = ⊥ := Q2 A B p hp
-- (X)
example (n : ℕ) (S : Finset (Fin n)) :
    (∀ g h : G n, chi n S (g + h) = chi n S g * chi n S h) ∧ chi n S 0 = 1 ∧
      ∀ i : Fin n, chi n S (e n i) = if i ∈ S then -1 else 1 := X n S
-- (F1), (F2), (F3)
example (n : ℕ) (f : G n → ℤ) : fourier n (L n f) = diagD n (fourier n f) := F1 n f
example (n : ℕ) (v : Finset (Fin n) → ℤ) : L n (ifourier n v) = ifourier n (diagD n v) := F2 n v
example (n : ℕ) :
    (∀ f, ifourier n (fourier n f) = (2 ^ n : ℕ) • f) ∧
      (∀ v, fourier n (ifourier n v) = (2 ^ n : ℕ) • v) := F3 n
-- (B0) Bai's odd part, subset form
example (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (K n) ≃+
      Sylp p ((S : {S : Finset (Fin n) // S.Nonempty}) → ZMod (2 * S.1.card))) := B0 n p hp hp2
-- (B1) Bai's form
example (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (K n) ≃+
      Sylp p ((j : Fin n) → Fin (n.choose (j + 1)) → ZMod (j + 1))) := B1 n p hp hp2
-- (X0)
example (n : ℕ) (S : EvenS n) (g : G n) : chiBar n S (Fold.mk n g) = chi n S.1 g := X0 n S g
-- (C1), (C2), (C3)
example (n : ℕ) (u : Fold.Gbar n → ℤ) :
    fourierBar n (Fold.lapBar ℤ n u) = diagDBar n (fourierBar n u) := C1 n u
example (n : ℕ) (v : EvenS n → ℤ) :
    Fold.lapBar ℤ n (ifourierBar n v) = ifourierBar n (diagDBar n v) := C2 n v
example (n : ℕ) (hn : 1 ≤ n) :
    (∀ u, ifourierBar n (fourierBar n u) = (2 ^ (n - 1) : ℕ) • u) ∧
      (∀ v, fourierBar n (ifourierBar n v) = (2 ^ (n - 1) : ℕ) • v) := C3 n hn
-- (C4) the folded cube, subset form
example (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (Fold.KBar n) ≃+
      Sylp p ((S : {S : EvenS n // S.1.Nonempty}) → ZMod (2 * S.1.1.card))) := C4 n hn p hp hp2
-- (C5) Corollary 1.4 in the paper's form
example (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (Fold.KBar n) ≃+
      Sylp p ((t : Fin (n / 2)) → Fin (n.choose (2 * (t + 1))) →
        ZMod (2 * (2 * (t + 1))))) := C5 n hn p hp hp2

#print axioms OddParts.Q0
#print axioms OddParts.Q1
#print axioms OddParts.Q2
#print axioms OddParts.X
#print axioms OddParts.F1
#print axioms OddParts.F2
#print axioms OddParts.F3
#print axioms OddParts.B0
#print axioms OddParts.B1
#print axioms OddParts.X0
#print axioms OddParts.C1
#print axioms OddParts.C2
#print axioms OddParts.C3
#print axioms OddParts.C4
#print axioms OddParts.C5
