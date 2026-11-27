import Gacha.Frobenius

namespace MathGacha

/-- A nontrivial common divisor at a prime index forces divisibility of the other index. -/
theorem indexDividesFromCommonFactor {p q t : ℕ} (hp : p.Prime) (hq : 1 < q)
    (hf : q ∣ Nat.fib p) (ht : q ∣ Nat.fib t) : p ∣ t := by
  by_contra hnot
  have hc := (hp.coprime_iff_not_dvd.mpr hnot).gcd_eq_one
  have hd := Nat.dvd_gcd hf ht
  rw [← Nat.fib_gcd, hc, Nat.fib_one] at hd
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd Nat.one_pos hd)) hq

/-- Every prime divisor of a prime-index term beyond index 5 lies in one of two progressions. -/
theorem fibPrimeFactorCongruence {p q : ℕ} (hp : p.Prime) (hlarge : 5 < p)
    (hq : q.Prime) (hf : q ∣ Nat.fib p) : p ∣ q - 1 ∨ p ∣ q + 1 := by
  have h2 : q ≠ 2 := by
    rintro rfl
    have hd := indexDividesFromCommonFactor hp (by decide : 1 < 2) hf
      (by decide : 2 ∣ Nat.fib 3)
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  have h5 : q ≠ 5 := by
    rintro rfl
    have hd := indexDividesFromCommonFactor hp (by decide : 1 < 5) hf
      (by decide : 5 ∣ Nat.fib 5)
    have := Nat.le_of_dvd (by decide : 0 < 5) hd
    omega
  exact (fibFrobeniusZero hq h2 h5).imp (indexDividesFromCommonFactor hp hq.one_lt hf)
    (indexDividesFromCommonFactor hp hq.one_lt hf)

/-- Oddness removes the first multiple of p in both progressions. -/
theorem fibLeastFactorLinearBound {p q : ℕ} (hp : p.Prime) (hlarge : 5 < p)
    (hq : q.Prime) (hf : q ∣ Nat.fib p) : 2 * p ≤ q + 1 := by
  have hoddp := hp.eq_two_or_odd.resolve_left (by omega)
  have hoddq := hq.eq_two_or_odd
  rcases fibPrimeFactorCongruence hp hlarge hq hf with ⟨k, hk⟩ | ⟨k, hk⟩
  all_goals
    have hk2 : 2 ≤ k := by
      by_contra! h
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp at hk <;> (have := hq.two_le; omega)
    have hmul := Nat.mul_le_mul_left p hk2
    rw [Nat.mul_comm p 2] at hmul
    omega

/-- To test a moving cutoff Kp it suffices to test the two progressions kp ± 1. -/
theorem divisorProgressionUpTo {p q K : ℕ} (hp : p.Prime) (hlarge : 5 < p)
    (hq : q.Prime) (hf : q ∣ Nat.fib p) (hbound : q ≤ K * p) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ (q = k * p + 1 ∨ q = k * p - 1) := by
  have hq2 := hq.two_le
  rcases fibPrimeFactorCongruence hp hlarge hq hf with ⟨k, hk⟩ | ⟨k, hk⟩
  all_goals
    rw [Nat.mul_comm p k] at hk
    have hpos : 1 ≤ k := by
      by_contra! h
      have he : k = 0 := by omega
      simp [he] at hk <;> omega
    have hkK : k ≤ K := by
      by_contra! h
      have hmul := Nat.mul_le_mul_right p (show K+1 ≤ k by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    exact ⟨k, hpos, hkK, by omega⟩

/-- A finite list of composite linear forms excludes all factors in an entire moving interval. -/
theorem noSmallFactorFromCompositeForms {p K : ℕ} (hp : p.Prime) (hlarge : 5 < p)
    (hforms : ∀ k : ℕ, 1 ≤ k → k ≤ K → ¬ (k * p + 1).Prime ∧ ¬ (k * p - 1).Prime)
    {q : ℕ} (hq : q.Prime) (hf : q ∣ Nat.fib p) : K * p < q := by
  by_contra! h
  obtain ⟨k, hpos, hk, rfl | rfl⟩ := divisorProgressionUpTo hp hlarge hq hf h
  · exact (hforms k hpos hk).1 hq
  · exact (hforms k hpos hk).2 hq

end MathGacha
