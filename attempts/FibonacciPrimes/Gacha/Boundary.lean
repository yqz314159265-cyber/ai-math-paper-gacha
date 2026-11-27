import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace MathGacha

theorem fib_prime_indices_through_30 (n : Nat) (h : n ≤ 30) :
    Nat.Prime (Nat.fib n) ↔ n ∈ [3, 4, 5, 7, 11, 13, 17, 23, 29] := by
  interval_cases n <;> norm_num [Nat.fib]

theorem fib_four_is_prime : Nat.Prime (Nat.fib 4) := by
  norm_num [Nat.fib]

theorem fib_three_is_two : Nat.fib 3 = 2 := by
  norm_num [Nat.fib]

end MathGacha
