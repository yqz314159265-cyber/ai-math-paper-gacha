import Gacha.PairCountBridge
import Mathlib.NumberTheory.Chebyshev

namespace MathGacha

theorem squarePrefix_le_twoPow {X : ℕ} (hX : 6≤X) : (X+1)^2≤2^X := by
  induction X, hX using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    calc
      (n+1+1)^2 ≤ 2*(n+1)^2 := by nlinarith
      _ ≤ 2*2^n := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

theorem primeCountingLowerSix {X : ℕ} (hX : 6≤X) :
    (Real.log 2/2) * (X:ℝ)/Real.log X ≤ (X.primeCounting:ℝ) := by
  have hp := Chebyshev.pi_ge X
  have hpow : ((X:ℝ)+1)^2 ≤ (2:ℝ)^X := by exact_mod_cast squarePrefix_le_twoPow hX
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow,Real.log_pow] at hlog
  apply le_trans _ hp
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1≤X by omega)))
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith only [hlog]

/-- A quantitative estimate for the two-slope sieve yields an actual prime
index greater than any prescribed B. All endpoint losses are explicit. -/
theorem existsLargeGoodFibIndexOfBound {X y K B : ℕ} (hX : 6≤X)
    (hgap : ((smallFactorIndices X y K).card:ℝ) + (max B (max y 5)+1 : ℕ) <
      (Real.log 2/2)*(X:ℝ)/Real.log X) :
    ∃ p≤X, max B (max y 5)<p ∧ p.Prime ∧ K*p<(Nat.fib p).minFac := by
  let M := max B (max y 5)
  let P := (Finset.range (X+1)).filter Nat.Prime
  have hc : P.card=X.primeCounting := (Nat.count_eq_card_filter_range (p:=Nat.Prime) (X+1)).symm
  by_contra hh
  have hsub : P ⊆ smallFactorIndices X y K ∪ Finset.range (M+1) := by
    intro p hp
    obtain ⟨hpX,hpP⟩ := Finset.mem_filter.mp hp
    by_cases hMp : M<p
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      have hyM : y≤M := le_trans (le_max_left ..) (le_max_right ..)
      have h5M : 5≤M := le_trans (le_max_right ..) (le_max_right ..)
      refine ⟨hpX,h5M.trans_lt hMp,hyM.trans_lt hMp,hpP,?_⟩
      by_contra! hlt
      exact hh ⟨p,by have h := Finset.mem_range.mp hpX; omega,hMp,hpP,hlt⟩
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  have hsize := (Finset.card_le_card hsub).trans (Finset.card_union_le ..)
  rw [hc,Finset.card_range] at hsize
  have hc' : (X.primeCounting:ℝ)≤((smallFactorIndices X y K).card:ℝ)+(M+1:ℕ) := by exact_mod_cast hsize
  exact (not_lt_of_ge ((primeCountingLowerSix hX).trans hc')) hgap

end MathGacha
