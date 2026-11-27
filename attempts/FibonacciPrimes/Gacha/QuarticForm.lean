import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

namespace MathGacha

open jacobiSym

/-- Reciprocity swaps an odd denominator with a numerator congruent to one mod four. -/
theorem jacobiSwapOneModFour {m n : ℕ} (hm : m % 4 = 1) (hn : Odd n) :
    jacobiSym (m : ℤ) n = jacobiSym (n : ℤ) m :=
  jacobiSym.quadratic_reciprocity_one_mod_four hm hn

/-- If `q ≡ 5b² (mod n)` and `b` is coprime to odd `n`, reciprocity moves
`J(q|n)` to `J(n|5)`. -/
theorem jacobiResidueFiveSquare {q n b : ℕ} (hn : Odd n)
    (hcop : Int.gcd (b : ℤ) n = 1)
    (hmod : (q : ℤ) % n = (5 * (b : ℤ) ^ 2) % n) :
    jacobiSym (q : ℤ) n = jacobiSym (n : ℤ) 5 := by
  rw [jacobiSym.mod_left' hmod]
  rw [show (5 * (b : ℤ) ^ 2 : ℤ) = (5 : ℤ) * (b : ℤ) ^ 2 by ring]
  rw [jacobiSym.mul_left, jacobiSym.sq_one' hcop, mul_one]
  exact jacobiSym.quadratic_reciprocity_one_mod_four (by norm_num) hn

/-- For `q ≡ 5 (mod 8)`, `b=2v`, `v` odd, and `q ≡ a² (mod v)` with
`a` coprime to `v`, the Jacobi symbol `(b|q)` is `-1`. -/
theorem jacobiTwoMulOdd_isNegOne {q a v : ℕ} (hq4 : q % 4 = 1) (hq8 : q % 8 = 5)
    (hv : Odd v) (hcop : Int.gcd (a : ℤ) v = 1)
    (hmod : q % v = a ^ 2 % v) :
    jacobiSym ((2 * v : ℕ) : ℤ) q = -1 := by
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hrecip : jacobiSym (v : ℤ) q = jacobiSym (q : ℤ) v :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hv).symm
  have hres : (q : ℤ) % v = ((a : ℤ) ^ 2) % v := by exact_mod_cast hmod
  have hsq : jacobiSym (q : ℤ) v = 1 := by
    rw [jacobiSym.mod_left' hres, jacobiSym.sq_one' hcop]
  have htwo : jacobiSym (2 : ℤ) q = -1 := by
    rw [jacobiSym.at_two hqodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hq2 : q % 2 = 1 := by omega
    simp [hq8, hq2]
  rw [show ((2 * v : ℕ) : ℤ) = (2 : ℤ) * (v : ℤ) by norm_num, jacobiSym.mul_left,
    htwo, hrecip, hsq]
  norm_num

/-- A sum-of-squares representation gives `q ≡ 5b² (mod a+2b)`. -/
theorem sumSquares_mod_fiveSquare {q a b n : ℕ} (hq : q = a ^ 2 + b ^ 2)
    (hn : n = a + 2 * b) :
    (q : ℤ) % n = (5 * (b : ℤ) ^ 2) % n := by
  have hqz : (q : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hq
  have hnz : (n : ℤ) = (a : ℤ) + 2 * (b : ℤ) := by exact_mod_cast hn
  change (q : ℤ) ≡ 5 * (b : ℤ) ^ 2 [ZMOD n]
  rw [Int.modEq_iff_dvd]
  refine ⟨2 * (b : ℤ) - a, ?_⟩
  rw [hnz, hqz]
  ring

/-- The ordinary Jacobi-symbol identity for the `a+2b` factor and `b=2v` factor. -/
theorem jacobiSumSquaresFactorIdentity {q a b n v : ℕ}
    (hq : q = a ^ 2 + b ^ 2) (hn : n = a + 2 * b)
    (hnOdd : Odd n) (hcopbn : Int.gcd (b : ℤ) n = 1)
    (hb : b = 2 * v) (hv : Odd v) (hcopav : Int.gcd (a : ℤ) v = 1)
    (hmodav : q % v = a ^ 2 % v) (hq8 : q % 8 = 5) :
    jacobiSym (n : ℤ) q * jacobiSym (b : ℤ) q =
      jacobiSym (n : ℤ) 5 * (-1) := by
  have hq4 : q % 4 = 1 := by omega
  have hJsum : jacobiSym (n : ℤ) q = jacobiSym (n : ℤ) 5 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hnOdd hq4]
    exact jacobiResidueFiveSquare hnOdd hcopbn (sumSquares_mod_fiveSquare hq hn)
  have hJb : jacobiSym (b : ℤ) q = -1 := by
    simpa [hb] using jacobiTwoMulOdd_isNegOne hq4 hq8 hv hcopav hmodav
  rw [hJsum, hJb]

theorem jacobiAtFive (m : ℕ) :
    jacobiSym (m : ℤ) 5 =
      if m % 5 = 0 then 0 else if m % 5 = 1 ∨ m % 5 = 4 then 1 else -1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [← jacobiSym.legendreSym.to_jacobiSym 5 (m : ℤ)]
  rw [legendreSym.mod, ← Int.natCast_mod]
  interval_cases h : m % 5 <;> norm_num [legendreSym, quadraticCharFun]

theorem jacobiFive_of_sumSquares_mod_four {a b n : ℕ} (hn : n = a + 2 * b)
    (hmod : (a ^ 2 + b ^ 2) % 5 = 4) :
    jacobiSym (n : ℤ) 5 = if 5 ∣ b then -1 else 1 := by
  rw [jacobiAtFive]
  have hNmod : n % 5 = ((a % 5) + 2 * (b % 5)) % 5 := by rw [hn]; omega
  rw [hNmod]
  have ha5 : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hb5 : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases ha : a % 5 <;> interval_cases hb : b % 5 <;>
    norm_num [Nat.add_mod, Nat.pow_mod, Nat.mul_mod, ha, hb] at hmod <;>
    norm_num [hNmod, ha, hb, Nat.dvd_iff_mod_eq_zero]

/-- The quadratic character of `(a+2b)/b` is the product of the two
Legendre/Jacobi factors. -/
theorem quadraticChar_two_add_div_eq_jacobi_product {q a b n : ℕ}
    [Fact q.Prime] (hn : n = a + 2 * b)
    (hb0 : (b : ZMod q) ≠ 0) :
    quadraticChar (ZMod q) (2 + (a : ZMod q) / (b : ZMod q)) =
      jacobiSym (n : ℤ) q * jacobiSym (b : ℤ) q := by
  have heq : (2 : ZMod q) + (a : ZMod q) / b =
      (n : ZMod q) / (b : ZMod q) := by
    rw [hn]
    field_simp
    push_cast
    ring
  rw [heq]
  have hratio : (n : ZMod q) / (b : ZMod q) * (b : ZMod q) ^ 2 =
      (n : ZMod q) * (b : ZMod q) := by
    field_simp
  have hc := congrArg (quadraticChar (ZMod q)) hratio
  rw [map_mul, quadraticChar_sq_one' hb0, mul_one] at hc
  rw [hc, map_mul]
  rw [← jacobiSym.legendreSym.to_jacobiSym q (n : ℤ),
      ← jacobiSym.legendreSym.to_jacobiSym q (b : ℤ)]
  simp [legendreSym]

/-- In the `q ≡ 29 (mod 40)` sum-of-two-squares setup, the quadratic
residuacity of `2+a/b` is exactly the divisibility condition `5 ∣ b`.
The coprimality hypotheses are exposed so the arithmetic representation can
be supplied independently. -/
theorem isSquare_two_add_div_iff_five_dvd {q a b n v : ℕ}
    [Fact q.Prime]
    (hq : q = a ^ 2 + b ^ 2) (hn : n = a + 2 * b)
    (hnOdd : Odd n) (hcopbn : Int.gcd (b : ℤ) n = 1)
    (hb : b = 2 * v) (hv : Odd v)
    (hcopav : Int.gcd (a : ℤ) v = 1)
    (hmodav : q % v = a ^ 2 % v) (hq8 : q % 8 = 5)
    (hmod5 : (a ^ 2 + b ^ 2) % 5 = 4)
    (hb0 : (b : ZMod q) ≠ 0) :
    IsSquare (2 + (a : ZMod q) / (b : ZMod q)) ↔ 5 ∣ b := by
  let x : ZMod q := 2 + (a : ZMod q) / (b : ZMod q)
  have hchar : quadraticChar (ZMod q) x = if 5 ∣ b then 1 else -1 := by
    dsimp [x]
    rw [quadraticChar_two_add_div_eq_jacobi_product hn hb0]
    rw [jacobiSumSquaresFactorIdentity hq hn hnOdd hcopbn hb hv hcopav hmodav hq8]
    rw [jacobiFive_of_sumSquares_mod_four hn hmod5]
    split_ifs <;> norm_num
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, quadraticChar_zero] at hchar
    split_ifs at hchar
    all_goals norm_num at hchar
  change IsSquare x ↔ 5 ∣ b
  rw [← quadraticChar_one_iff_isSquare hx, hchar]
  simp

end MathGacha
