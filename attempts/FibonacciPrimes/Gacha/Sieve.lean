import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite

namespace MathGacha

/-- Fibonacci numbers at distinct prime indices are coprime. -/
theorem fib_prime_indices_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : Nat.Coprime (Nat.fib p) (Nat.fib q) := by
  change Nat.gcd (Nat.fib p) (Nat.fib q) = 1
  rw [← Nat.fib_gcd, ((Nat.coprime_primes hp hq).mpr hne).gcd_eq_one, Nat.fib_one]

/-- Every fixed finite set of nontrivial factors disappears at all sufficiently large prime indices. -/
theorem finite_factors_avoid_fib_prime_indices (s : Finset ℕ) :
    ∃ B : ℕ, ∀ p : ℕ, B < p → p.Prime → ∀ r ∈ s, 1 < r → ¬ r ∣ Nat.fib p := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert r s _ ih =>
    obtain ⟨B, hB⟩ := ih
    by_cases hex : ∃ t : ℕ, t.Prime ∧ r ∣ Nat.fib t
    · obtain ⟨t, ht, hrt⟩ := hex
      refine ⟨max B t, ?_⟩
      intro p hlarge hp d hd hdlarge hdvd
      rcases Finset.mem_insert.mp hd with rfl | hold
      · have hc := fib_prime_indices_coprime hp ht (by omega)
        have h1 : d ∣ 1 := hc.gcd_eq_one ▸ Nat.dvd_gcd hdvd hrt
        exact (Nat.not_lt_of_ge (Nat.le_of_dvd Nat.one_pos h1)) hdlarge
      · exact hB p (by omega) hp d hold hdlarge hdvd
    · refine ⟨B, ?_⟩
      intro p hlarge hp d hd hdlarge hdvd
      rcases Finset.mem_insert.mp hd with rfl | hold
      · exact hex ⟨p, hp, hdvd⟩
      · exact hB p hlarge hp d hold hdlarge hdvd

/-- One can force a large prime factor while also forcing a large prime index. -/
theorem arbitrarilyLargePrimeFactors (bound : ℕ) :
    ∃ p q : ℕ, bound < p ∧ p.Prime ∧ bound < q ∧ q.Prime ∧ q ∣ Nat.fib p := by
  obtain ⟨B, hB⟩ := finite_factors_avoid_fib_prime_indices (Finset.range (bound + 1))
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (max (max B bound) 5 + 1)
  have hgrowth := Nat.le_fib_self (show 5 ≤ p by omega)
  obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd (show Nat.fib p ≠ 1 by omega)
  refine ⟨p, q, by omega, hp, ?_, hq, hd⟩
  by_contra! hsmall
  exact hB p (by omega) hp q (Finset.mem_range.mpr (by omega)) hq.one_lt hd

end MathGacha
