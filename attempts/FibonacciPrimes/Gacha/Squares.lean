import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.SumTwoSquares

namespace MathGacha

/-- A sum of two coprime squares gives a square root of -1 modulo each odd-index term. -/
theorem minusOneSquareAtOddIndex (k : ℕ) : IsSquare (-1 : ZMod (Nat.fib (2 * k + 1))) :=
  ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime (Nat.fib_two_mul_add_one k)
    (Nat.fib_coprime_fib_succ k).symm

/-- A prime factor of an odd-index term is either 2 or congruent to 1 modulo 4. -/
theorem primeFactorAtOddIndex (k q : ℕ) (hq : q.Prime) (h : q ∣ Nat.fib (2 * k + 1)) :
    q = 2 ∨ q % 4 = 1 := by
  have hpos : 0 < Nat.fib (2 * k + 1) := Nat.fib_pos.mpr (by omega)
  have hn := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
    (hq.mem_primeFactors h hpos.ne') (minusOneSquareAtOddIndex k)
  rcases hq.eq_two_or_odd with htwo | hodd
  · exact Or.inl htwo
  · exact Or.inr (by omega)

end MathGacha
