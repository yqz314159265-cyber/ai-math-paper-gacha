import Gacha.EffectiveSieve
import Gacha.Certificates

namespace MathGacha

/-- Lucas certificate for the computed witness when K=35. -/
theorem effectiveWitnessPrime : Nat.Prime 1010824870255201 := by
  apply lucasList 1010824870255201 43
    [2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7, 7, 11, 13, 17, 19, 23, 29, 31] (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

/-- This finite lower bound does not require writing down the Fibonacci number. -/
theorem effectiveWitnessLeastFactor :
    35378870458932035 < (Nat.fib 1010824870255201).minFac := by
  exact leastFactorInOneClass (K:=35) (by decide) effectiveWitnessPrime (by decide) (by decide +kernel)

end MathGacha
