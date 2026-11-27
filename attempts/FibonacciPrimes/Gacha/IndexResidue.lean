import Gacha.FactorRank
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace MathGacha

/-- At a prime index distinct from 2 and 5, the Fibonacci residue is the Euler
criterion power of 5. -/
theorem fib_prime_index_eq_pow_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (Nat.fib p : ZMod p) = (5 : ZMod p) ^ ((p - 1) / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨a, b, ha, hb, _, hs, hs0⟩ := fibRootsAtPrime hp2 hp5
  let s := a - b
  let e := (p - 1) / 2
  have hpodd := hp.odd_of_ne_two hp2
  have hpEq : p = 2 * e + 1 := by
    rcases hpodd with ⟨k, hk⟩
    dsimp [e]
    omega
  have hpow : s ^ p = s * (5 : K) ^ e := by
    calc
      s ^ p = s ^ (2 * e + 1) := congrArg (fun n : ℕ => s ^ n) hpEq
      _ = s * (5 : K) ^ e := by rw [pow_succ, pow_mul, show s^2 = 5 from hs]; ring
  have hbinet := fibPowerDifference ha hb p
  have hK : (Nat.fib p : K) = (5 : K) ^ e := by
    apply mul_left_cancel₀ hs0
    calc
      (a-b) * (Nat.fib p : K) = a ^ p - b ^ p := hbinet
      _ = (a - b) ^ p := by rw [sub_pow_char]
      _ = s ^ p := rfl
      _ = s * (5 : K) ^ e := hpow
  apply (algebraMap (ZMod p) K).injective
  simpa only [e, map_natCast, map_pow, map_ofNat] using hK


/-- The sign of the Fibonacci residue is the quadratic character of 5. -/
theorem fib_prime_index_eq_legendre {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (Nat.fib p : ZMod p) = (legendreSym p 5 : ZMod p) := by
  rw [fib_prime_index_eq_pow_five hp hp2 hp5, legendreSym.eq_pow p 5]
  have hExp : p / 2 = (p - 1) / 2 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  rw [hExp]
  norm_num

/-- Thus the prime-index Fibonacci residue is exactly `1` or `-1`, with the choice
specified by the Legendre symbol of 5. -/
theorem fib_prime_index_eq_one_or_neg_one {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (Nat.fib p : ZMod p) = 1 ∨ (Nat.fib p : ZMod p) = -1 := by
  have hfive : (5 : ZMod p) ≠ 0 := by
    intro hz
    exact hp5 ((Nat.dvd_prime_two_le (by decide : Nat.Prime 5) hp.two_le).mp
      ((CharP.cast_eq_zero_iff (ZMod p) p 5).mp hz))
  rcases legendreSym.eq_one_or_neg_one p (a := 5) (by exact_mod_cast hfive) with h | h
  · left
    rw [fib_prime_index_eq_legendre hp hp2 hp5, h]
    norm_num
  · right
    rw [fib_prime_index_eq_legendre hp hp2 hp5, h]
    norm_num

/-- If the quadratic-character sign of `F_p` is negative, some prime factor of `F_p`
lies in the `-1` residue class modulo `p`. -/
theorem exists_prime_factor_eq_neg_one_mod {p : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hlarge : 5 < p)
    (hsign : legendreSym p 5 = -1) :
    ∃ q, q.Prime ∧ q ∣ Nat.fib p ∧ p ∣ q + 1 := by
  let F := Nat.fib p
  have hFpos : 0 < F := Nat.fib_pos.mpr (by omega)
  have hFne : F ≠ 0 := hFpos.ne'
  have hfib : (F : ZMod p) = -1 := by
    dsimp [F]
    rw [fib_prime_index_eq_legendre hp (by omega) (by omega), hsign]
    norm_num
  by_contra hnone
  have hno : ∀ q, q.Prime → q ∣ F → ¬ p ∣ q + 1 := by
    intro q hq hqdiv hplus
    exact hnone ⟨q, hq, hqdiv, hplus⟩
  have hall (q : ℕ) (hqmem : q ∈ F.primeFactorsList) :
      (q : ZMod p) = 1 := by
    have hq : q.Prime := Nat.prime_of_mem_primeFactorsList hqmem
    have hqdiv : q ∣ F := Nat.dvd_of_mem_primeFactorsList hqmem
    have hq2 : 2 ≤ q := hq.two_le
    rcases fibPrimeFactorCongruence hp hlarge hq hqdiv with hminus | hplus
    · have hmod : 1 ≡ q [MOD p] :=
        (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).2 hminus
      simpa using (ZMod.natCast_eq_natCast_iff q 1 p).2 hmod.symm
    · exact False.elim <| hno q hq hqdiv hplus
  have hprod (l : List ℕ) (hl : ∀ q ∈ l, (q : ZMod p) = 1) :
      ((l.prod : ℕ) : ZMod p) = 1 := by
    induction l with
    | nil => simp
    | cons q l ih =>
      have hq := hl q (by simp)
      have htail : ∀ r ∈ l, (r : ZMod p) = 1 := by
        intro r hr
        exact hl r (by simp [hr])
      rw [List.prod_cons, Nat.cast_mul, hq, ih htail]
      simp
  have hprodF := hprod F.primeFactorsList hall
  rw [Nat.prod_primeFactorsList hFne] at hprodF
  have hne : (1 : ZMod p) ≠ -1 := by
    intro hz
    have hz2 : (2 : ZMod p) = 0 := by linear_combination hz
    have hdiv2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz2
    have hpEq : p = 2 := (Nat.dvd_prime_two_le Nat.prime_two hp.two_le).mp hdiv2
    omega
  exact hne (hprodF.symm.trans hfib)

/-- Explicit evaluation of the character of five at any odd prime. -/
theorem legendreSym_five_eq_neg_one_iff {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    legendreSym q 5 = -1 ↔ q % 5 = 2 ∨ q % 5 = 3 := by
  have : Fact (5 : ℕ).Prime := ⟨by decide⟩
  have small (r : ℕ) (hr : r < 5) : legendreSym 5 r = -1 ↔ r = 2 ∨ r = 3 := by
    interval_cases r <;> norm_num
  have hrec : legendreSym q 5 = legendreSym 5 q := by
    exact_mod_cast legendreSym.quadratic_reciprocity_one_mod_four (p:=5) (q:=q) (by decide) hq
  rw [hrec, legendreSym.mod]
  simpa only [Int.natCast_mod] using small (q%5) (by omega)

end MathGacha
