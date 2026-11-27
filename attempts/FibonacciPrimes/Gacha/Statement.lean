/-
Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.
The proposition is copied from FibonacciPrimes.fib_primes_infinite.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace MathGacha

/-- The proposition of the pinned upstream declaration. -/
def Original : Prop :=
  {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime}.Infinite

end MathGacha
