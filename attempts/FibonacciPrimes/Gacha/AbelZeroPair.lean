import Gacha.AbelZeroSlope
import Gacha.AbelMovingOne

open Filter Topology

namespace MathGacha

/-- Fixed-slope plus pair weights vanish in the Abel normalization. -/
theorem tendsto_linearPrimePair_plus_zero {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => (x - 1) * linearPrimePairTsum k true x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  classical
  have hEq (x : ℝ) : linearPrimePairTsum k true x = candidatePrimeTsum (plusPair k) x := by
    dsimp [linearPrimePairTsum, candidatePrimeTsum]
    apply tsum_congr
    intro n
    by_cases hn : n.Prime ∧ (k * n + 1).Prime <;>
      simp [linearPrimePairTerm, candidatePrimeTerm, plusPair, hn]
  simpa [hEq] using tendsto_plusPair_abel_zero hk

/-- Fixed-slope minus pair weights vanish in the Abel normalization. -/
theorem tendsto_linearPrimePair_minus_zero {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => (x - 1) * linearPrimePairTsum k false x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  classical
  have hEq (x : ℝ) : linearPrimePairTsum k false x = candidatePrimeTsum (minusPair k) x := by
    dsimp [linearPrimePairTsum, candidatePrimeTsum]
    apply tsum_congr
    intro n
    by_cases hn : n.Prime ∧ (k * n - 1).Prime <;>
      simp [linearPrimePairTerm, candidatePrimeTerm, minusPair, hn]
  simpa [hEq] using tendsto_minusPair_abel_zero hk


/-- The finite linear sieve has unconditional Abel-normalized limit one. -/
theorem fullLinearSieveAbelLimit (K : ℕ) :
    Tendsto (fun x : ℝ => (x - 1) * sievedTsum K x)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  apply tendsto_scaled_sievedTsum K
  intro k hk s
  have hkpos : 0 < k := by
    have hk' := (Finset.mem_Icc.mp hk).1
    omega
  cases s with
  | false => exact tendsto_linearPrimePair_minus_zero hkpos
  | true => exact tendsto_linearPrimePair_plus_zero hkpos

/-- The complementary bad Fibonacci-index weight vanishes unconditionally. -/
theorem fullBadFibIndexAbelLimit (K : ℕ) :
    Tendsto (fun x : ℝ => (x - 1) * badFibIndexTsum K x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  apply tendsto_scaled_badFibIndexTsum K
  intro k hk s
  have hkpos : 0 < k := by
    have hk' := (Finset.mem_Icc.mp hk).1
    omega
  cases s with
  | false => exact tendsto_linearPrimePair_minus_zero hkpos
  | true => exact tendsto_linearPrimePair_plus_zero hkpos
end MathGacha
