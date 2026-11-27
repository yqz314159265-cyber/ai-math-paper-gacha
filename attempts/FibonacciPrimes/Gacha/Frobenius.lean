import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination

namespace MathGacha

/-- The numerator of Binet's formula makes sense over a ring, including in positive characteristic. -/
theorem fibPowerDifference {K : Type*} [CommRing K] {a b : K}
    (ha : a ^ 2 = a + 1) (hb : b ^ 2 = b + 1) (n : ℕ) :
    (a - b) * (Nat.fib n : K) = a ^ n - b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    rw [Nat.fib_add_two, Nat.cast_add, mul_add, ih0, ih1, pow_add a n 2, pow_add b n 2,
      ha, hb, pow_succ, pow_succ]
    ring

/-- A square root of the discriminant produces the two characteristic roots. -/
theorem fibRootsFromDiscriminant {K : Type*} [Field K] {s : K}
    (htwo : (2 : K) ≠ 0) (hs : s ^ 2 = 5) :
    ∃ a b : K, a ^ 2 = a + 1 ∧ b ^ 2 = b + 1 ∧ a + b = 1 ∧ a - b = s := by
  let a := (1+s)/2
  let b := (1-s)/2
  have hA : a * 2 = 1 + s := div_mul_cancel₀ _ htwo
  have hB : b * 2 = 1 - s := div_mul_cancel₀ _ htwo
  have h4 := mul_ne_zero htwo htwo
  have ha : a ^ 2 = a + 1 := by
    apply mul_right_cancel₀ h4
    linear_combination (2*a+1+s-2) * hA + hs
  have hb : b ^ 2 = b + 1 := by
    apply mul_right_cancel₀ h4
    linear_combination (2*b+1-s-2) * hB + hs
  have hab : a + b = 1 := by
    apply mul_right_cancel₀ htwo
    linear_combination hA + hB
  have hdiff : a - b = s := by
    apply mul_right_cancel₀ htwo
    linear_combination hA - hB
  exact ⟨a, b, ha, hb, hab, hdiff⟩

/-- In the algebraic closure of the prime field, Frobenius either fixes or interchanges the
two distinct roots of X²-X-1. Taking their powers gives a Fibonacci zero at q-1 or q+1. -/
theorem fibFrobeniusZero {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h5 : q ≠ 5) :
    q ∣ Nat.fib (q - 1) ∨ q ∣ Nat.fib (q + 1) := by
  have : Fact q.Prime := ⟨hq⟩
  let K := AlgebraicClosure (ZMod q)
  have cast_ne {k : ℕ} (hk : k.Prime) (hne : q ≠ k) : (k : K) ≠ 0 := by
    intro hz
    exact hne ((Nat.dvd_prime_two_le hk hq.two_le).mp
      ((CharP.cast_eq_zero_iff K q k).mp hz))
  have htwo : (2 : K) ≠ 0 := cast_ne Nat.prime_two h2
  have hfive : (5 : K) ≠ 0 := cast_ne (by decide : Nat.Prime 5) h5
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (5 : K) (show 0 < 2 by decide)
  obtain ⟨a, b, ha, hb, hab, hdiff⟩ := fibRootsFromDiscriminant htwo hs
  have hs0 : s ≠ 0 := by intro hz; apply hfive; simpa [hz] using hs.symm
  have hne : a - b ≠ 0 := hdiff ▸ hs0
  have hf : (a ^ q) ^ 2 = a ^ q + 1 := by
    have h := congrArg (fun x : K => x ^ q) ha
    simpa only [← pow_mul, Nat.mul_comm 2 q, add_pow_char, one_pow] using h
  have hprod : a * b = -1 := by linear_combination a * hab - ha
  have hor : a ^ q = a ∨ a ^ q = b := by
    have hz : (a ^ q - a) * (a ^ q - b) = 0 := by
      linear_combination hf - (a ^ q) * hab + hprod
    exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp
  have hsum : a ^ q + b ^ q = 1 := by
    rw [← add_pow_char, hab, one_pow]
  have bridge (t : ℕ) (ht : a ^ t = b ^ t) : q ∣ Nat.fib t := by
    apply (CharP.cast_eq_zero_iff K q _).mp
    exact (mul_eq_zero.mp (by simpa [ht] using fibPowerDifference ha hb t)).resolve_left hne
  have hzeroA : a ≠ 0 := by intro h; simp [h] at ha
  have hzeroB : b ≠ 0 := by intro h; simp [h] at hb
  rcases hor with hfix | hswap
  · left
    have hfixB : b ^ q = b := by linear_combination hsum - hab - hfix
    have one_less (y : K) (hy : y ≠ 0) (h : y ^ q = y) : y ^ (q-1) = 1 := by
      have hy2 : y ^ (q - 1) * y = 1 * y := by
        rw [← pow_succ, Nat.sub_add_cancel hq.one_lt.le, h, one_mul]
      exact mul_right_cancel₀ hy hy2
    exact bridge _ ((one_less a hzeroA hfix).trans (one_less b hzeroB hfixB).symm)
  · right
    have hswapB : b ^ q = a := by linear_combination hsum - hab - hswap
    apply bridge
    rw [pow_succ, pow_succ, hswap, hswapB, mul_comm]

end MathGacha
