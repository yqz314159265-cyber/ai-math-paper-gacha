import Gacha.DicksonSieve
import Gacha.Squares

namespace MathGacha

open Polynomial

/-- Coprimality with the Frobenius polynomial tests all base-field roots at once. -/
theorem coprimeFrobeniusIffNoRoot {q : ℕ} [Fact q.Prime] (P : (ZMod q)[X]) :
    IsCoprime P (X^q - X) ↔ ∀ z : ZMod q, P.eval z ≠ 0 := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (ZMod q) (AlgebraicClosure (ZMod q)) P (X^q - X)]
  let f := algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
  have hmap (z : ZMod q) : aeval (f z) P = f (P.eval z) := by
    exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _
  constructor
  · intro h z hz
    have hzq : (f z)^q = f z := by rw [← map_pow, ZMod.pow_card]
    rcases h (f z) with hn | hn
    · exact hn (by rw [hmap, hz, map_zero])
    · exact hn (by simp [hzq])
  · intro h x
    by_cases hx : x^q=x
    · obtain ⟨z,hz⟩ := (finiteField_image_iff_frobenius_fixed q x).mpr hx
      left
      change f z = x at hz
      rw [← hz,hmap]
      exact (map_ne_zero f).mpr (h z)
    · right
      simpa [sub_ne_zero] using hx

/-- Testing one polynomial pair replaces a search through all elements of the prime field. -/
theorem avoidsDicksonIffCoprime {q k : ℕ} [Fact q.Prime] :
    ¬ hasDicksonRoot q k ↔
      IsCoprime (Polynomial.dickson 1 (1 : ZMod q) k + 3) (X^q - X) := by
  rw [coprimeFrobeniusIffNoRoot]
  simp only [hasDicksonRoot, not_exists, eval_add, eval_ofNat]
  apply forall_congr'
  intro z
  exact not_congr eq_neg_iff_add_eq_zero

/-- A Fibonacci-free polynomial coprimality criterion for the original infinitude question. -/
theorem originalIffCoprimeFrobeniusTests :
    Original ↔ ∀ B : ℕ, ∃ p > max B 5, p.Prime ∧ ∀ q : ℕ, q.Prime → 5 < q →
      q ≤ 2^(p/2) → p ∣ neighborIndex q →
      IsCoprime (Polynomial.dickson 1 (1 : ZMod q) (neighborIndex q / p) + 3) (X^q - X) := by
  rw [originalIffAvoidsDicksonRoots]
  constructor
  · intro h B
    obtain ⟨p,hB,hp,hs⟩ := h B
    refine ⟨p,hB,hp,?_⟩
    intro q hq hlarge hsmall hd
    have : Fact q.Prime := ⟨hq⟩
    exact avoidsDicksonIffCoprime.mp (hs q hq hlarge hsmall hd)
  · intro h B
    obtain ⟨p,hB,hp,hs⟩ := h B
    refine ⟨p,hB,hp,?_⟩
    intro q hq hlarge hsmall hd
    have : Fact q.Prime := ⟨hq⟩
    exact avoidsDicksonIffCoprime.mpr (hs q hq hlarge hsmall hd)

/-- The sign of the neighbor and the possible residues of the multiplier are linked. -/
theorem divisorMultiplierResidues {p q k : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hq5 : 5 < q) (hd : q ∣ Nat.fib p) (hk : k*p=neighborIndex q) :
    (q=k*p+1 ∧ k%4=0 ∧ ((k*p)%5=0 ∨ (k*p)%5=3)) ∨
    (q+1=k*p ∧ k%4=2 ∧ ((k*p)%5=3 ∨ (k*p)%5=4)) := by
  obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
  have hpodd : p=2*m+1 := by omega
  have hfour := (primeFactorAtOddIndex m q hq (hpodd ▸ hd)).resolve_left (by omega)
  have hfiv : q%5 ≠ 0 := by
    intro hz
    have he := (Nat.dvd_prime_two_le hq (by decide : 2 ≤ 5)).mp (Nat.dvd_of_mod_eq_zero hz)
    omega
  have hmod (v : ℕ) (hv : v=0 ∨ v=2) (he : (k*p)%4 = v) : k%4=v := by
    rw [Nat.mul_mod] at he
    have hpmod : p%4=1 ∨ p%4=3 := by omega
    rcases hpmod with h | h <;> rcases hv with rfl | rfl <;> rw [h] at he <;> omega
  unfold neighborIndex at hk
  split at hk
  next hn =>
    right
    exact ⟨by omega, hmod 2 (Or.inr rfl) (by omega), by omega⟩
  next hn =>
    left
    exact ⟨by omega, hmod 0 (Or.inl rfl) (by omega), by omega⟩

/-- Multipliers congruent to ten modulo twenty never produce a prime divisor. -/
theorem noFactorAtTenModTwenty {p q k : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hq5 : 5 < q) (hk : k*p=neighborIndex q) (hclass : k%20=10) :
    ¬ q ∣ Nat.fib p := by
  intro hd
  have hz : (k*p)%5=0 := by rw [Nat.mul_mod, show k%5=0 by omega]; simp
  rcases divisorMultiplierResidues hp hp5 hq hq5 hd hk with h | h <;> omega

end MathGacha
