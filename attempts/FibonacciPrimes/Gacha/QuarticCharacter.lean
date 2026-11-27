import Gacha.DicksonTests
import Gacha.FourBoundary

namespace MathGacha

open Polynomial

/-- In any commutative ring the shifted fourth Dickson polynomial is a sum of two squares. -/
theorem dicksonFourShiftEval {R : Type*} [CommRing R] (z : R) :
    (dickson 1 (1 : R) 4).eval z + 3 = (z^2-2)^2 + 1 := by
  norm_num [dickson, eval_add, eval_sub, eval_mul]
  ring

/-- With a chosen square root of minus one and square discriminant five,
the fourth Dickson test reduces to a single quadratic character. -/
theorem fourthDicksonRootIffSquare {K : Type*} [Field K] (i : K) (hi : i^2 = -1)
    (h5 : (5 : K) ≠ 0) (hs5 : IsSquare (5 : K)) :
    (∃ z : K, (dickson 1 1 4).eval z = -3) ↔ IsSquare (2+i) := by
  have hprod : (2+i)*(2-i)=5 := by linear_combination -hi
  have hne : 2-i ≠ 0 := fun he => h5 (by rw [← hprod, he, mul_zero])
  constructor
  · rintro ⟨z,hz⟩
    have hs := dicksonFourShiftEval z
    rw [hz] at hs
    have hsq : (z^2-2)^2=i^2 := by rw [hi]; linear_combination -hs
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with he | he
    · exact ⟨z, by linear_combination -he⟩
    · have hm : IsSquare (2-i) := ⟨z,by linear_combination -he⟩
      have hh := hs5.div hm
      rwa [← hprod,mul_div_cancel_right₀ _ hne] at hh
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hh : z^2-2=i := by linear_combination -hz
    have hs := dicksonFourShiftEval z
    rw [hh,hi] at hs
    linear_combination hs

/-- Quadratic reciprocity supplies both Fibonacci characteristic roots in this residue class. -/
theorem fiveSquareAtFourModFive {q : ℕ} (hq : q.Prime) (hmod : q%5=4) :
    IsSquare (5 : ZMod q) := by
  have : Fact q.Prime := ⟨hq⟩
  by_contra hn
  have hn' : ¬ IsSquare ((5 : ℕ) : ZMod q) := by exact_mod_cast hn
  have hneg := (legendreSym.eq_neg_one_iff' q).mpr hn'
  have hr := (legendreSym_five_eq_neg_one_iff (q:=q) (by omega)).mp hneg
  omega

/-- The quartic test at 4p+1, with p≡2 (mod 5) and both p and 4p+1 prime. -/
theorem fourNeighborDvdIffSquare {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hshape : q=4*p+1) (hpmod : p%5=2)
    (i : ZMod q) (hi : i^2 = -1) :
    q ∣ Nat.fib p ↔ IsSquare (2+i) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq5 : 5 < q := by omega
  have hn : neighborIndex q = 4*p := by
    have h : ¬ (q%5=2 ∨ q%5=3) := by omega
    simp only [neighborIndex, if_neg h]
    omega
  have hd : p ∣ neighborIndex q := hn ▸ dvd_mul_left p 4
  rw [primeDivisorIffDickson hp hq hq5, and_iff_right hd, hn, Nat.mul_div_cancel _ hp.pos]
  have h5 : (5 : ZMod q) ≠ 0 := by
    intro hz
    exact hq5.not_ge (Nat.le_of_dvd (by decide : 0<5) ((ZMod.natCast_eq_zero_iff 5 q).mp hz))
  have hs5 := fiveSquareAtFourModFive hq (by omega : q%5=4)
  exact fourthDicksonRootIffSquare i hi h5 hs5

/-- A split quadratic factor of the fifth cyclotomic polynomial would give
a nontrivial fifth root of unity in a field of size four modulo five. -/
theorem nonsquareFifthRootDiscriminant {q : ℕ} [Fact q.Prime] (hq5 : 5 < q) (hqmod : q%5=4)
    (a : ZMod q) (ha : a^2=a+1) : ¬ IsSquare (a^2-4) := by
  rintro ⟨d,hd⟩
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hz
    have h := Nat.le_of_dvd (by decide : 0<2) ((ZMod.natCast_eq_zero_iff 2 q).mp hz)
    omega
  let x := (d-a)/2
  have hx : x*2=d-a := div_mul_cancel₀ _ htwo
  have hquad : x^2+a*x+1=0 := by
    apply mul_right_cancel₀ (mul_ne_zero htwo htwo)
    linear_combination (2*x+d+a)*hx - hd
  have hcycl : x^4+x^3+x^2+x+1=0 := by
    linear_combination (x^2+(1-a)*x+1)*hquad + x^2*ha
  have hpow : x^5=1 := by linear_combination (x-1)*hcycl
  have hx0 : x ≠ 0 := by intro h; simp [h] at hpow
  have horder := orderOf_dvd_of_pow_eq_one hpow
  have horder' := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx0)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp horder with he | he
  · have hx1 := orderOf_eq_one_iff.mp he
    rw [hx1] at hcycl
    have hz : (5 : ZMod q)=0 := by linear_combination hcycl
    exact hq5.not_ge (Nat.le_of_dvd (by decide : 0<5) ((ZMod.natCast_eq_zero_iff 5 q).mp hz))
  · rw [he] at horder'
    omega

/-- Lehmer's character comparison for a prime in the 29 mod 40 branch. -/
theorem nonsquareFibRootIffSquareDiscriminant {q : ℕ} [Fact q.Prime] (hq5 : 5 < q)
    (hqmod : q%40=29) (a : ZMod q) (ha : a^2=a+1) :
    ¬ IsSquare a ↔ IsSquare (2*a-1) := by
  let s := 2*a-1
  have hs : s^2=5 := by dsimp [s]; linear_combination 4*ha
  have hs0 : s ≠ 0 := by
    intro hz
    have h5 : (5 : ZMod q)=0 := by simpa [hz] using hs.symm
    exact hq5.not_ge (Nat.le_of_dvd (by decide : 0<5) ((ZMod.natCast_eq_zero_iff 5 q).mp h5))
  have hn : ¬ IsSquare (a*s) := by
    intro hprod
    apply nonsquareFifthRootDiscriminant hq5 (by omega) a ha
    have hneg : IsSquare (-1 : ZMod q) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    have hsq : IsSquare ((a-1)^2) := ⟨a-1, pow_two _⟩
    have he : a^2-4 = (-1)*(a-1)^2*(a*s) := by
      dsimp [s]
      linear_combination (2*a^2-3*a+4)*ha
    rw [he]
    exact (hneg.mul hsq).mul hprod
  have hchars := (quadraticChar_neg_one_iff_not_isSquare (F:=ZMod q)).mpr hn
  rw [map_mul] at hchars
  change ¬ IsSquare a ↔ IsSquare s
  rw [← quadraticChar_neg_one_iff_not_isSquare, ← quadraticChar_one_iff_isSquare hs0]
  let A : ℤ := quadraticChar (ZMod q) a
  let S : ℤ := quadraticChar (ZMod q) s
  change A*S = -1 at hchars
  change A = -1 ↔ S = 1
  have hS : S=1 ∨ S= -1 := quadraticChar_dichotomy hs0
  rcases hS with h | h <;> rw [h] at hchars ⊢ <;> simp only [mul_one, mul_neg_one] at hchars <;> omega

/-- In the 29 modulo 40 branch the character test becomes one modular exponentiation. -/
theorem fibRootNonsquareIffFivePow {p q : ℕ} [Fact q.Prime] (hq5 : 5 < q)
    (hshape : q=4*p+1) (hmod : q%40=29) (a : ZMod q) (ha : a^2=a+1) :
    ¬ IsSquare a ↔ (5 : ZMod q)^p=1 := by
  rw [nonsquareFibRootIffSquareDiscriminant hq5 hmod a ha]
  let s := 2*a-1
  have hs : s^2=5 := by dsimp [s]; linear_combination 4*ha
  have hs0 : s ≠ 0 := by
    intro hz
    have h5 : (5 : ZMod q)=0 := by simpa [hz] using hs.symm
    exact hq5.not_ge (Nat.le_of_dvd (by decide : 0<5) ((ZMod.natCast_eq_zero_iff 5 q).mp h5))
  change IsSquare s ↔ _
  have hc : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  rw [FiniteField.isSquare_iff hc hs0, ZMod.card, show q/2=2*p by omega, pow_mul, hs]

/-- A primality, congruence, and single-base power test for the second possible factor. -/
theorem fourBoundaryIffFivePow {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hshape : q=4*p+1) :
    q ∣ Nat.fib p ↔ q.Prime ∧ p%5=2 ∧ (5 : ZMod q)^p=1 := by
  rw [fourBoundaryCriterion hp hp5 hshape]
  constructor
  · rintro ⟨hq, hmod, a, ha, hn⟩
    have : Fact q.Prime := ⟨hq⟩
    have hodd := hp.odd_of_ne_two (by omega)
    obtain ⟨m,hm⟩ := hodd
    exact ⟨hq,hmod,(fibRootNonsquareIffFivePow (by omega) hshape (by omega) a ha).mp hn⟩
  · rintro ⟨hq, hmod, hpow⟩
    have : Fact q.Prime := ⟨hq⟩
    have hodd := hp.odd_of_ne_two (by omega)
    obtain ⟨m,hm⟩ := hodd
    have hs5 := fiveSquareAtFourModFive hq (by omega : q%5=4)
    obtain ⟨s, hs⟩ := hs5
    have htwo : (2 : ZMod q) ≠ 0 := by
      intro hz
      have h := Nat.le_of_dvd (by decide : 0<2) ((ZMod.natCast_eq_zero_iff 2 q).mp hz)
      omega
    obtain ⟨a, _, ha, _⟩ := fibRootsFromDiscriminant htwo (show s^2=5 by rw [pow_two, ← hs])
    exact ⟨hq,hmod,a,ha,(fibRootNonsquareIffFivePow (by omega) hshape (by omega) a ha).mpr hpow⟩

end MathGacha
