module

public import RequestProject.Podium.Defs

/-!
# The carry bound (`C35_the_podium_arithmetic.md`, *Part K*, Lemma 9.5) and the carry shift
(*Part M*, (M3))

Encodings as in `Podium/Defs.lean` and C3: `κ(a, b)` is `Rulers.kappa a b` (in `ℤ`), `φ(x)` is
`Rulers.phi x` (in `ℤ`), `v_2` is `Rulers.v2`.  In (M3) the bracket `[2^q ≤ m mod 2^q + o]` is
`if 2 ^ q ≤ m % 2 ^ q + o then 1 else 0`.

The proof of (K) counts the carries of `a + B` with Kummer's theorem (`padicValNat_choose` of
Mathlib): `κ(a, B) = v_2 (binom(a + B, a))` is the number of `i ≥ 1` with
`2^i ≤ a mod 2^i + B mod 2^i`.
-/

@[expose] public section

namespace Podium

open Finset Rulers

/-- `s_2(x)` is the sum of the binary digits of `x`. -/
lemma s2_eq_digits_sum (x : ℕ) : s2 x = (Nat.digits 2 x).sum := by
  have key : ∀ l : List ℕ, (∀ d ∈ l, d < 2) → l.count 1 = l.sum := by
    intro l
    induction l with
    | nil => simp
    | cons d l ih =>
      intro hl
      have hd := hl d (by simp)
      rw [List.count_cons, List.sum_cons, ih fun e he => hl e (by simp [he])]
      interval_cases d <;> simp [add_comm]
  exact key _ fun d hd => Nat.digits_lt_base (by norm_num) hd

/-- `v_2(n!) = n − s_2(n)` (Legendre), in `ℤ`. -/
lemma v2_factorial (n : ℕ) : (padicValNat 2 n.factorial : ℤ) = n - s2 n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [show 2 - 1 = 1 from rfl, one_mul] at h
  rw [h, s2_eq_digits_sum, Nat.cast_sub (Nat.digit_sum_le 2 n)]

/-- Kummer: `κ(a, b) = v_2 (binom(a + b, a))`. -/
lemma kappa_eq_v2_choose (a b : ℕ) : kappa a b = padicValNat 2 ((a + b).choose a) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial b a
  rw [add_comm b a] at h
  have hc : (a + b).choose a ≠ 0 := (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul hc (Nat.factorial_ne_zero _)] at hv
  have hv' : ((padicValNat 2 ((a + b).choose a) : ℕ) : ℤ) + padicValNat 2 b.factorial +
      padicValNat 2 a.factorial = padicValNat 2 (a + b).factorial := by exact_mod_cast hv
  rw [v2_factorial, v2_factorial, v2_factorial] at hv'
  rw [kappa]
  rw [Nat.cast_add] at hv'
  linarith

/-- Kummer's carry count: `κ(a, b)` is the number of `i ∈ [1, a + b]` with a carry into bit `i`,
`2^i ≤ a mod 2^i + b mod 2^i`. -/
lemma kappa_eq_card_carries (a b : ℕ) :
    kappa a b = ((Ico 1 (a + b + 1)).filter
      (fun i => 2 ^ i ≤ a % 2 ^ i + b % 2 ^ i)).card := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [kappa_eq_v2_choose, padicValNat_choose (Nat.le_add_right a b)
    (Nat.lt_succ_of_le (Nat.log_le_self 2 _)), Nat.add_sub_cancel_left]

/-- The core of **Lemma 9.5** (the case `q = 0`): for `B ≥ 1` there is `z` with
`B ≤ z ≤ a + B` and `φ(B) + κ(a, B) ≤ φ(z)`. -/
lemma K_core (a B : ℕ) (hB : 1 ≤ B) :
    ∃ z, B ≤ z ∧ z ≤ a + B ∧ (B : ℤ) + v2 B + kappa a B ≤ (z : ℤ) + v2 z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := (Ico 1 (a + B + 1)).filter (fun i => 2 ^ i ≤ a % 2 ^ i + B % 2 ^ i) with hC
  have hk := kappa_eq_card_carries a B
  rw [← hC] at hk
  by_cases hne : C.Nonempty
  · set p := C.max' hne
    have hpC : p ∈ C := max'_mem _ _
    have hcarry : 2 ^ p ≤ a % 2 ^ p + B % 2 ^ p := (mem_filter.1 hpC).2
    -- every carry is above `v_2(B)`
    have hsub : C ⊆ Ioc (v2 B) p := by
      intro i hi
      refine mem_Ioc.2 ⟨?_, le_max' _ _ hi⟩
      by_contra hle
      push_neg at hle
      have hdvd : 2 ^ i ∣ B := (pow_dvd_pow 2 hle).trans pow_padicValNat_dvd
      have h1 := (mem_filter.1 hi).2
      rw [Nat.mod_eq_zero_of_dvd hdvd] at h1
      have := Nat.mod_lt a (show 0 < 2 ^ i by positivity)
      omega
    have hcard : (C.card : ℤ) ≤ p - v2 B := by
      have h1 := card_le_card hsub
      have := card_pos.2 hne
      rw [Nat.card_Ioc] at h1
      omega
    -- the clearing of `a + B` at bit `p`
    set z := a + B - (a + B) % 2 ^ p with hz
    have hpos : 0 < 2 ^ p := by positivity
    have hmodsum : (a + B) % 2 ^ p = a % 2 ^ p + B % 2 ^ p - 2 ^ p := by
      rw [Nat.add_mod]
      have h1 := Nat.mod_lt a hpos
      have h2 := Nat.mod_lt B hpos
      rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt (by omega)]
    have ha := Nat.mod_le a (2 ^ p)
    have hb := Nat.mod_lt B hpos
    have hzB : B + 1 ≤ z := by omega
    have hdvd : 2 ^ p ∣ z := Nat.dvd_sub_mod (a + B)
    have hvz : p ≤ v2 z := (padicValNat_dvd_iff_le (by omega)).1 hdvd
    refine ⟨z, by omega, by omega, ?_⟩
    have : ((B + 1 : ℕ) : ℤ) ≤ z := by exact_mod_cast hzB
    have : (p : ℤ) ≤ v2 z := by exact_mod_cast hvz
    push_cast at *
    linarith
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hk
    exact ⟨B, le_refl _, by omega, by rw [hk]; simp⟩

/-- **(K)** of `C35_the_podium_arithmetic.md` (Lemma 9.5, «Lemma K»): for `a : ℕ`, `B ≥ 1` and
`q : ℕ` there is `y` with `1 ≤ y ≤ 2^q (a + B)` and `φ(2^q B) + κ(a, B) ≤ φ(y)`.
(As in the file, `a = 0` is allowed.) -/
theorem K (a B q : ℕ) (hB : 1 ≤ B) :
    ∃ y, 1 ≤ y ∧ y ≤ 2 ^ q * (a + B) ∧ phi (2 ^ q * B) + kappa a B ≤ phi y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hBz, hza, hz⟩ := K_core a B hB
  have hq : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  refine ⟨2 ^ q * z, le_trans hB (le_trans hBz (Nat.le_mul_of_pos_left z hq)),
    Nat.mul_le_mul_left _ hza, ?_⟩
  have hv : ∀ x, 1 ≤ x → v2 (2 ^ q * x) = q + v2 x := fun x hx => by
    rw [v2, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]; rfl
  rw [phi, phi, hv B hB, hv z (by omega)]
  have h1 : (1 : ℤ) ≤ 2 ^ q := by exact_mod_cast hq
  have h2 : (B : ℤ) ≤ z := by exact_mod_cast hBz
  have h3 : 0 ≤ ((2 : ℤ) ^ q - 1) * (z - B) := mul_nonneg (by linarith) (by linarith)
  push_cast
  nlinarith

/-- **(M3)** of `C35_the_podium_arithmetic.md` (Proposition 9.6, step (K)): for `2^q ∣ Y` and
`o < 2^q`, `κ(m, Y + o) − κ(m, o) = κ(⌊m / 2^q⌋ + [2^q ≤ (m mod 2^q) + o], Y / 2^q)`. -/
theorem M3 (Y o m q : ℕ) (hY : 2 ^ q ∣ Y) (ho : o < 2 ^ q) :
    kappa m (Y + o) - kappa m o =
      kappa (m / 2 ^ q + (if 2 ^ q ≤ m % 2 ^ q + o then 1 else 0)) (Y / 2 ^ q) := by
  obtain ⟨Y', rfl⟩ := hY
  have hpos : 0 < 2 ^ q := by positivity
  rw [Nat.mul_div_cancel_left _ hpos]
  have hm := Nat.mod_add_div m (2 ^ q)
  have hml := Nat.mod_lt m hpos
  set ml := m % 2 ^ q
  set mh := m / 2 ^ q
  obtain ⟨r, c, hr, hrc, hcdef⟩ : ∃ r c, r < 2 ^ q ∧ ml + o = r + 2 ^ q * c ∧
      c = (if 2 ^ q ≤ ml + o then 1 else 0) := by
    split_ifs with h
    · exact ⟨ml + o - 2 ^ q, 1, by omega, by omega, rfl⟩
    · exact ⟨ml + o, 0, by omega, by omega, rfl⟩
  rw [← hcdef]
  have e1 : s2 (2 ^ q * Y' + o) = s2 o + s2 Y' := by
    rw [add_comm]; exact s2_add_two_pow_mul q o Y' ho
  have e2 : s2 m = s2 ml + s2 mh := by
    rw [← s2_add_two_pow_mul q ml mh hml, hm]
  have e3 : m + (2 ^ q * Y' + o) = r + 2 ^ q * (mh + c + Y') := by
    rw [mul_add, mul_add]; omega
  have e4 : m + o = r + 2 ^ q * (mh + c) := by
    rw [mul_add]; omega
  simp only [kappa]
  rw [e1, e2, e3, e4, s2_add_two_pow_mul q r _ hr, s2_add_two_pow_mul q r _ hr]
  push_cast
  ring

end Podium
