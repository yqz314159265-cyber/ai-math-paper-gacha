import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace MathGacha

/-- Every divisor index between 3 and n-1 gives a proper, nontrivial Fibonacci divisor. -/
theorem fib_prime_excludes_proper_divisor (n d : ℕ)
    (hd : 3 ≤ d) (hdn : d < n) (hdiv : d ∣ n) : ¬ (Nat.fib n).Prime := by
  intro hp
  have hbig : 1 < Nat.fib d := lt_of_lt_of_le (by decide : 1 < Nat.fib 3) (Nat.fib_mono hd)
  have heq := (Nat.dvd_prime_two_le hp hbig).mp (Nat.fib_dvd d n hdiv)
  exact ((Nat.fib_lt_fib (by omega : 2 ≤ d)).2 hdn).ne heq

/-- A prime Fibonacci value has a prime index, except at index four. -/
theorem fib_prime_index_prime_or_four {n : ℕ} (hp : (Nat.fib n).Prime) :
    n.Prime ∨ n = 4 := by
  by_cases hs : n ≤ 4
  · interval_cases n <;> norm_num [Nat.fib_add_two] at *
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  exfalso
  obtain ⟨d, hdvd, hd, hlt⟩ := (Nat.not_prime_iff_exists_dvd_lt (by omega : 2 ≤ n)).mp hprime
  by_cases hd2 : d = 2
  · subst d
    obtain ⟨q, hq⟩ := hdvd
    exact fib_prime_excludes_proper_divisor n q (by omega) (by omega)
      ⟨2, by omega⟩ hp
  · exact fib_prime_excludes_proper_divisor n d (by omega) hlt hdvd hp

/-- A prime index can yield a composite value. -/
theorem index_nineteen_prime : Nat.Prime 19 := by decide

theorem fib_nineteen_factorization : Nat.fib 19 = 37 * 113 := by decide

theorem fib_nineteen_not_prime : ¬ (Nat.fib 19).Prime := by
  rw [fib_nineteen_factorization]
  norm_num

end MathGacha
