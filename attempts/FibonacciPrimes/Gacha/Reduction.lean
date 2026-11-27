import Gacha.Index
import Gacha.Statement
import Mathlib.Order.Interval.Finset.Nat

namespace MathGacha

/-- The original assertion is equivalent to finding prime values at arbitrarily large prime indices. -/
theorem originalIffUnboundedPrimeIndices :
    Original ↔ ∀ B : ℕ, ∃ p > B, Nat.Prime p ∧ Nat.Prime (Nat.fib p) := by
  unfold Original
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h B
    obtain ⟨v, ⟨⟨p, rfl⟩, hp⟩, hv⟩ := h (Nat.fib (max B 4))
    have ht : max B 4 < p := by
      by_contra! hle
      exact (Nat.not_lt_of_ge (Nat.fib_mono hle)) hv
    refine ⟨p, by omega, ?_, hp⟩
    exact (fib_prime_index_prime_or_four hp).resolve_right (by omega)
  · intro h B
    obtain ⟨p, hB, _, hp⟩ := h (max B 5)
    exact ⟨Nat.fib p, ⟨⟨p, rfl⟩, hp⟩, lt_of_lt_of_le (by omega) (Nat.le_fib_self (by omega))⟩

/-- The cutoff needed for a complete primality sieve depends on the chosen index. -/
theorem originalIffSieveToSquareRoot :
    Original ↔ ∀ B : ℕ, ∃ p > max B 4, p.Prime ∧
      ∀ d : ℕ, 2 ≤ d → d ≤ (Nat.fib p).sqrt → ¬ d ∣ Nat.fib p := by
  rw [originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p, hlarge, hp, hf⟩ := h (max B 4)
    exact ⟨p, hlarge, hp, (Nat.prime_def_le_sqrt.mp hf).2⟩
  · intro h B
    obtain ⟨p, hlarge, hp, hs⟩ := h B
    have hg := Nat.le_fib_self (show 5 ≤ p by omega)
    exact ⟨p, by omega, hp, Nat.prime_def_le_sqrt.mpr ⟨by omega, hs⟩⟩

end MathGacha
