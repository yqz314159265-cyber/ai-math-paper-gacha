import Gacha.FactorRank
import Mathlib.Data.Nat.Squarefree

namespace MathGacha

/-- A repeated prime factor at a prime index recurs at one of its own two neighbors. -/
theorem primeSquareFibFactorAtNeighbor {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hsq : q ^ 2 ∣ Nat.fib p) :
    q ^ 2 ∣ Nat.fib (q - 1) ∨ q ^ 2 ∣ Nat.fib (q + 1) := by
  have hqfib : q ∣ Nat.fib p := dvd_trans (by simp) hsq
  rcases fibPrimeFactorCongruence hp hp5 hq hqfib with hm | hpq
  · left
    exact dvd_trans hsq (Nat.fib_dvd p (q - 1) hm)
  · right
    exact dvd_trans hsq (Nat.fib_dvd p (q + 1) hpq)

/-- If no prime has a repeated square factor at either neighboring index, every
Fibonacci number at a prime index above five is squarefree. -/
theorem fibAtPrimeSquarefreeOfNoNeighborSquare {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hno : ∀ q, q.Prime →
      ¬ (q ^ 2 ∣ Nat.fib (q - 1) ∨ q ^ 2 ∣ Nat.fib (q + 1))) :
    Squarefree (Nat.fib p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hdiv
  have hneighbor := primeSquareFibFactorAtNeighbor hp hp5 hq (by simpa [pow_two] using hdiv)
  exact hno q hq hneighbor

end MathGacha
