import Gacha.Reduction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Real

open ArithmeticFunction

namespace MathGacha

/-- Twice the von Mangoldt weight strictly exceeds the logarithm exactly at primes. -/
theorem wholeTermPrimeThreshold {n : ℕ} (hn : 1 < n) :
    n.Prime ↔ Real.log n < 2 * vonMangoldt n := by
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  constructor
  · intro hp
    rw [vonMangoldt_apply_prime hp]
    linarith
  · contrapose!
    intro hnp
    rw [vonMangoldt_apply]
    split
    · have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
      have hmin : 0 < (n.minFac : ℝ) := by exact_mod_cast Nat.minFac_pos n
      have hlog := Real.log_le_log (by positivity : (0:ℝ) < (n.minFac : ℝ) ^ 2)
        (by exact_mod_cast hsq : (n.minFac : ℝ) ^ 2 ≤ (n : ℝ))
      simpa using hlog
    · linarith

/-- The original problem in terms of the arithmetic weight of the whole Fibonacci number. -/
theorem originalIffUnboundedMangoldtThreshold :
    Original ↔ ∀ B : ℕ, ∃ p > max B 5, p.Prime ∧
      Real.log (Nat.fib p) < 2 * vonMangoldt (Nat.fib p) := by
  rw [originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p, hB, hp, hv⟩ := h (max B 5)
    exact ⟨p, hB, hp, (wholeTermPrimeThreshold hv.one_lt).mp hv⟩
  · intro h B
    obtain ⟨p, hB, hp, hv⟩ := h B
    have hle := Nat.le_fib_self (by omega : 5 ≤ p)
    exact ⟨p, by omega, hp, (wholeTermPrimeThreshold (by omega)).mpr hv⟩

/-- Dividing the positive excess by log n gives mass one to a prime and zero to each composite. -/
noncomputable def primeMass (n : ℕ) : ℝ :=
  max (2 * vonMangoldt n - Real.log n) 0 / Real.log n

theorem primeMass_eq_indicator {n : ℕ} (hn : 1 < n) :
    primeMass n = if n.Prime then 1 else 0 := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  unfold primeMass
  by_cases h : n.Prime
  · rw [if_pos h, vonMangoldt_apply_prime h]
    have hh : 2 * Real.log n - Real.log n = Real.log n := by ring
    simp [hh, max_eq_left hl.le, hl.ne']
  · have hle := not_lt.mp (fun hlt => h ((wholeTermPrimeThreshold hn).mpr hlt))
    rw [if_neg h, max_eq_right (sub_nonpos.mpr hle), zero_div]

/-- Sum the whole-term masses only at prime indices greater than five. -/
noncomputable def fibPrimeMass (p : ℕ) : ℝ :=
  if 5 < p ∧ p.Prime then primeMass (Nat.fib p) else 0

theorem originalIffNotSummableFibPrimeMass : Original ↔ ¬ Summable fibPrimeMass := by
  classical
  let s : Set ℕ := {p | 5 < p ∧ p.Prime ∧ (Nat.fib p).Prime}
  have hw : fibPrimeMass = s.indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hg : 5 < p ∧ p.Prime
    · have hf := Nat.le_fib_self (by omega : 5 ≤ p)
      by_cases hv : (Nat.fib p).Prime <;>
        simp [s, fibPrimeMass, hg, primeMass_eq_indicator (by omega : 1 < Nat.fib p),
          hv, Set.indicator]
    · simp [s, fibPrimeMass, hg, Set.indicator, ← and_assoc]
  have hfin : s.Finite ↔ Summable fibPrimeMass := by
    rw [hw, ← summable_subtype_iff_indicator]
    constructor
    · intro hs
      have := hs.fintype
      exact (hasSum_fintype _).summable
    · intro hs
      have ht : Finite s := Finite.of_summable_const (by norm_num : (0:ℝ)<1) hs
      exact Set.finite_coe_iff.mp ht
  rw [← hfin]
  change Original ↔ s.Infinite
  rw [Set.infinite_iff_exists_gt, originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p, hp, hpr, hf⟩ := h (max B 5)
    exact ⟨p, ⟨by omega, hpr, hf⟩, by omega⟩
  · intro h B
    obtain ⟨p, ⟨_, hp, hf⟩, hB⟩ := h B
    exact ⟨p, hB, hp, hf⟩

end MathGacha
