import Gacha.IndexResidue

namespace MathGacha

/-- At q=2p−1 prime, the sign of F_q controls whether the full term F_p is divisible by q. -/
theorem fibHalfNeighborSquare {p q : ℕ} (hp : Odd p) (hq : q.Prime) (h5 : q ≠ 5)
    (he : q + 1 = 2 * p) :
    2 * (Nat.fib p : ZMod q)^2 = 1 + (Nat.fib q : ZMod q) := by
  have : Fact q.Prime := ⟨hq⟩
  let K := AlgebraicClosure (ZMod q)
  obtain ⟨a, b, ha, hb, hsum, hsq, hne⟩ := fibRootsAtPrime (q:=q) (by omega) h5
  have h5K : (5 : K) ≠ 0 := hsq ▸ pow_ne_zero 2 hne
  have hprod : a*b = -1 := by linear_combination a * hsum - ha
  have habpow : a^p * b^p = -1 := by rw [← mul_pow, hprod, hp.neg_one_pow]
  have hsumq : a^q + b^q = 1 := by rw [← add_pow_char, hsum, one_pow]
  have hsquare : (5:K) * (Nat.fib p : K)^2 = a^(q+1) + b^(q+1) + 2 := by
    rw [← hsq, ← mul_pow, fibPowerDifference ha hb]
    rw [he, pow_mul, pow_mul]
    have heq (x : K) : (x ^ 2)^p = (x^p)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [heq a, heq b]
    linear_combination -2 * habpow
  have hsplit : 2*(a^(q+1)+b^(q+1)) = 1 + (5:K)*(Nat.fib q : K) := by
    have hdiff := fibPowerDifference ha hb q
    have hones : (a^q+b^q)*(a+b)=1 := by rw [hsumq, hsum, one_mul]
    rw [pow_succ, pow_succ, ← hsq, pow_two, mul_assoc, hdiff, ← hones]
    ring
  have hk : 2 * (Nat.fib p : K)^2 = 1 + (Nat.fib q : K) := by
    apply mul_left_cancel₀ h5K
    linear_combination 2 * hsquare + hsplit
  apply (algebraMap (ZMod q) K).injective
  simpa only [map_mul, map_pow, map_natCast, map_add, map_one, map_ofNat] using hk

/-- At the lower endpoint q=2p−1, divisibility is equivalent to the negative quadratic sign. -/
theorem boundaryDvdIffNegative {p q : ℕ} [Fact q.Prime] (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (he : q + 1 = 2*p) :
    q ∣ Nat.fib p ↔ legendreSym q 5 = -1 := by
  have hs := fibHalfNeighborSquare (hp.odd_of_ne_two (by omega)) hq (by omega) he
  rw [fib_prime_index_eq_legendre hq (by omega) (by omega)] at hs
  have nonzero (a : ℕ) (ha : 0 < a) (hlt : a < q) : (a : ZMod q) ≠ 0 := by
    intro hz
    exact hlt.not_ge (Nat.le_of_dvd ha ((ZMod.natCast_eq_zero_iff _ _).mp hz))
  have h2 : (2 : ZMod q) ≠ 0 := nonzero 2 (by decide) (by omega)
  have h5 : ((5 : ℤ) : ZMod q) ≠ 0 := by exact_mod_cast nonzero 5 (by decide) (by omega)
  constructor
  · intro hd
    rcases legendreSym.eq_one_or_neg_one q (a:=5) h5 with h | h
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, h] at hs
      exact (h2 (by push_cast at hs; linear_combination -hs)).elim
    · exact h
  · intro h
    rw [h] at hs
    have hz : 2 * (Nat.fib p : ZMod q)^2 = 0 := by simpa using hs
    exact (ZMod.natCast_eq_zero_iff _ _).mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hz).resolve_left h2))

/-- A divisor at the lower endpoint must itself be prime. -/
theorem primeOfBoundaryDvd {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (he : q+1 = 2*p) (hd : q ∣ Nat.fib p) : q.Prime := by
  have hmin := Nat.minFac_prime (by omega : q ≠ 1)
  have hdiv := (Nat.minFac_dvd q).trans hd
  have hlow := fibLeastFactorLinearBound hp hp5 hmin hdiv
  have hle := Nat.minFac_le (by omega : 0 < q)
  have hEq : q.minFac = q := by omega
  rwa [hEq] at hmin

/-- From index eight onward a factor of size 2p−1 is proper. -/
theorem fibAboveBoundary {p : ℕ} (h : 8 ≤ p) : 2 * p - 1 < Nat.fib p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => decide
  | succ k ih =>
    have hrec := Nat.fib_add_two (n := 7+k)
    have hmono : Nat.fib 3 ≤ Nat.fib (7+k) := Nat.fib_mono (by omega)
    have hl : Nat.fib 3 = 2 := by decide
    rw [show 7+k+2=8+(k+1) by omega, show 7+k+1=8+k by omega] at hrec
    omega

/-- Exact criterion for a divisor at the smallest possible size. -/
theorem boundaryDvdIff {p : ℕ} (hp : p.Prime) (h : 5 < p) :
    2*p-1 ∣ Nat.fib p ↔ (2*p-1).Prime ∧ (p % 5 = 2 ∨ p % 5 = 4) := by
  let q := 2*p-1
  have he : q+1=2*p := by dsimp [q]; omega
  change q ∣ Nat.fib p ↔ q.Prime ∧ _
  have aux (hq : q.Prime) : q ∣ Nat.fib p ↔ (p % 5 = 2 ∨ p % 5 = 4) := by
    have : Fact q.Prime := ⟨hq⟩
    rw [boundaryDvdIffNegative hp h hq he, legendreSym_five_eq_neg_one_iff (by omega)]
    omega
  constructor
  · intro hd
    have hq := primeOfBoundaryDvd hp h he hd
    exact ⟨hq, (aux hq).mp hd⟩
  · rintro ⟨hq, hr⟩
    exact (aux hq).mpr hr

/-- The lower bound for the least prime divisor is attained in exactly these two residue classes. -/
theorem leastFactorAtBoundaryIff {p : ℕ} (hp : p.Prime) (h : 5 < p) :
    (Nat.fib p).minFac = 2*p-1 ↔ (2*p-1).Prime ∧ (p % 5 = 2 ∨ p % 5 = 4) := by
  rw [← boundaryDvdIff hp h]
  constructor
  · intro he
    rw [← he]
    exact Nat.minFac_dvd _
  · intro hd
    have hl := Nat.le_fib_self (show 5 ≤ p by omega)
    have hlo := fibLeastFactorLinearBound hp h (Nat.minFac_prime (by omega : Nat.fib p ≠ 1))
      (Nat.minFac_dvd _)
    exact Nat.le_antisymm (Nat.minFac_le_of_dvd (by omega) hd) (by omega)

/-- Drobot's composite-index test, with the prime index and the composite term distinguished. -/
theorem compositeAtBoundary {p : ℕ} (hp : p.Prime) (h : 7 < p)
    (hq : (2*p-1).Prime) (hr : p % 5 = 2 ∨ p % 5 = 4) : ¬ (Nat.fib p).Prime := by
  intro hf
  have hd := (boundaryDvdIff hp (by omega)).mpr ⟨hq, hr⟩
  have he := (Nat.dvd_prime_two_le hf hq.two_le).mp hd
  have hlt := fibAboveBoundary (p:=p) (by omega)
  omega

end MathGacha
