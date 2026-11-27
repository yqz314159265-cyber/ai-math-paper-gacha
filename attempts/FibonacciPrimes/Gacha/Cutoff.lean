import Gacha.LinearSieve

namespace MathGacha

/-- The modulus in the Dirichlet construction grows at least exponentially with the sieve multiplier. -/
theorem modulusExponentialLowerBound (K : ℕ) : 8 ^ K ≤ linearFormsModulus K := by
  have h := Finset.prod_le_prod' (s := Finset.Icc 1 K)
    (f := fun _ : ℕ => 8) (g := fun k : ℕ => (3*k+1)*(3*k-1)) (by
      intro k hk
      have hkpos := (Finset.mem_Icc.mp hk).1
      exact Nat.mul_le_mul (show 4 ≤ 3*k+1 by omega) (show 2 ≤ 3*k-1 by omega))
  simpa [linearFormsModulus] using h

/-- An explicit threshold beyond which a polynomial cutoff is smaller than the Fibonacci value. -/
theorem fourthPowerBelowFib {n : ℕ} (hn : 50 ≤ n) : n ^ 4 ≤ Nat.fib n := by
  have h : ∀ m : ℕ, (m+50)^4 ≤ Nat.fib (m+50) := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => decide
    | one => decide
    | more k h0 _ =>
      have poly : (k+52)^4 ≤ 2*(k+50)^4 := by ring_nf; omega
      have hf := Nat.fib_le_fib_succ (n := k+50)
      have hrec := Nat.fib_add_two (n := k+50)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hrec hf
      change (k+52)^4 ≤ Nat.fib (k+52)
      omega
  simpa [Nat.sub_add_cancel hn] using h (n-50)

/-- Every sufficiently large witness in this constructed residue class still has Kp
below the square-root test threshold. This identifies the limit of this particular construction. -/
theorem dirichletCutoffBelowSquareRoot {K p : ℕ} (hp : 50 ≤ p)
    (h : p ≡ 3 [MOD linearFormsModulus K]) : K*p < (Nat.fib p).sqrt := by
  have hm := Nat.le_of_dvd (show 0 < p-3 by omega) h.symm.dvd'
  have hl := modulusExponentialLowerBound K
  have hkpow : K < 8 ^ K := Nat.lt_pow_self (by decide : 1 < 8)
  have hkk : K < p := by omega
  have hp2 : p*p ≤ (Nat.fib p).sqrt := by
    apply Nat.le_sqrt'.mpr
    convert fourthPowerBelowFib hp using 1
    ring
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hkk (by omega)) hp2

end MathGacha
