import Gacha.LinearSieve

open ArithmeticFunction ArithmeticFunction.vonMangoldt Filter

namespace MathGacha

/-- Logarithmic weight on prime indices whose least Fibonacci factor exceeds K times the index. -/
noncomputable def largeLeastFactorWeight (K n : ℕ) : ℝ :=
  if n.Prime ∧ K*n < (Nat.fib n).minFac then Real.log n / n else 0

/-- Each fixed moving sieve leaves a set of prime indices of divergent logarithmic weight. -/
theorem not_summable_largeLeastFactorWeight (K : ℕ) : ¬ Summable (largeLeastFactorWeight K) := by
  classical
  have hc := linearFormsModulusCoprime K
  have : NeZero (linearFormsModulus K) :=
    ⟨by intro hz; simp [hz] at hc⟩
  let a : ZMod (linearFormsModulus K) := 3
  have hu : IsUnit a := (ZMod.isUnit_iff_coprime 3 _).mpr hc
  intro hw
  apply not_summable_residueClass_prime_div (a := a) hu
  apply Summable.of_norm_bounded_eventually_nat hw
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have pos : 0 ≤ Real.log n / (n : ℝ) :=
    div_nonneg hlog (Nat.cast_nonneg _)
  by_cases hp : n.Prime
  · by_cases heq : (n : ZMod (linearFormsModulus K)) = a
    · have hm := (ZMod.natCast_eq_natCast_iff n 3 _).mp heq
      have h := leastFactorBoundOnClass hp (by omega) hm
      simp [largeLeastFactorWeight, hp, h, residueClass, Set.indicator, heq, vonMangoldt_apply_prime hp,
        Real.norm_eq_abs, abs_of_nonneg hlog]
    · simp [largeLeastFactorWeight, hp, residueClass, Set.indicator, heq]
      split <;> simp_all
  · simp [largeLeastFactorWeight, hp]
end MathGacha
