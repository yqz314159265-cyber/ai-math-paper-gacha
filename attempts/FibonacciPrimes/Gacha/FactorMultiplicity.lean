import Gacha.FactorRank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.GoldenRatio

open scoped ArithmeticFunction.Omega

namespace MathGacha

/-- A moving least-factor threshold controls the number of prime factors,
counted with multiplicity, by the complete factorization. -/
theorem minFactorPower_le {N L : ℕ} (hN : N≠0) (hL : L≤N.minFac) :
    L^(Ω N)≤N := by
  have hlist (l : List ℕ) (hall : ∀ q∈l, L≤q) : L^l.length≤l.prod := by
    induction l with
    | nil => simp
    | cons q l ih =>
      rw [List.length_cons,List.prod_cons,pow_succ']
      exact Nat.mul_le_mul (hall q (by simp)) (ih (fun r hr => hall r (by simp [hr])))
  rw [ArithmeticFunction.cardFactors_apply]
  exact (hlist N.primeFactorsList (fun q hq =>
    hL.trans (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hq).one_lt
      (Nat.dvd_of_mem_primeFactorsList hq)))).trans_eq (Nat.prod_primeFactorsList hN)

theorem fib_le_goldenRatio_pow (n : ℕ) : (Nat.fib n:ℝ) ≤ Real.goldenRatio^n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Real.goldenRatio_mul_fib_succ_add_fib n
    rw [← h]
    exact (le_mul_of_one_le_left (by positivity) Real.one_lt_goldenRatio.le).trans
      (le_add_of_nonneg_right (by positivity))

theorem fibMultiplicityLogBound {p L : ℕ} (hp : 5≤p) (hpos : 0<L)
    (hL : L≤(Nat.fib p).minFac) :
    ((Ω (Nat.fib p)):ℝ)*Real.log L ≤ (p:ℝ)*Real.log Real.goldenRatio := by
  have hF := Nat.le_fib_self hp
  have hpow := minFactorPower_le (by omega : Nat.fib p≠0) hL
  have hreal : (L:ℝ)^(Ω (Nat.fib p))≤Real.goldenRatio^p :=
    (show (L:ℝ)^(Ω (Nat.fib p))≤(Nat.fib p:ℝ) by exact_mod_cast hpow).trans (fib_le_goldenRatio_pow p)
  have h := Real.log_le_log (pow_pos (by exact_mod_cast hpos) _) hreal
  simpa only [Real.log_pow] using h

/-- All prime indices beyond five satisfy the explicit multiplicity bound,
including those outside any additional sieve. -/
theorem primeIndexMultiplicityBound {p : ℕ} (hp : p.Prime) (hp5 : 5<p) :
    ((Ω (Nat.fib p)):ℝ) ≤ (p:ℝ)*Real.log Real.goldenRatio / Real.log (2*p-1:ℕ) := by
  have hf := Nat.le_fib_self (show 5≤p by omega)
  have hq := Nat.minFac_prime (by omega : Nat.fib p≠1)
  have hbound := fibLeastFactorLinearBound hp hp5 hq (Nat.minFac_dvd _)
  have hlog : 0<Real.log (2*p-1:ℕ) := Real.log_pos (by exact_mod_cast (show 1<2*p-1 by omega))
  rw [le_div_iff₀ hlog]
  exact fibMultiplicityLogBound (by omega) (by omega) (by omega)

end MathGacha
