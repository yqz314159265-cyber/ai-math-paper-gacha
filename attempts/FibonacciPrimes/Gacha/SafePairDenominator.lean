import Gacha.PrimePairQuant
import Gacha.SquarefreePairMass

open Finset

namespace MathGacha

theorem safe_card_divisors_sqfree {d : ℕ} (hd : Squarefree d) :
    d.divisors.card = 2 ^ d.primeFactors.card := by
  have hdne : d ≠ 0 := hd.ne_zero
  rw [Nat.card_divisors hdne]
  calc
    (∏ p ∈ d.primeFactors, (d.factorization p + 1)) =
        ∏ _p ∈ d.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpos := hprime.factorization_pos_of_dvd hdne
        (Nat.dvd_of_mem_primeFactors hp)
      have hle := (Nat.squarefree_iff_factorization_le_one hdne).mp hd p
      omega
    _ = 2 ^ d.primeFactors.card := by simp [Finset.prod_const]

theorem safe_selberg_term_lower {s : BoundingSieve} {d : ℕ}
    (hd : d ∣ s.prodPrimes) (hsf : Squarefree d)
    (hnu : ∀ r ∈ d.primeFactors, s.nu r = 2 / (r : ℝ))
    (hprime : ∀ r ∈ d.primeFactors, 3 ≤ r) :
    s.selbergTerms d ≥ (2 : ℝ) ^ d.primeFactors.card / d := by
  have hnuD : s.nu d = ∏ r ∈ d.primeFactors, (2 : ℝ) / r := by
    rw [← s.prod_primeFactors_nu hd]
    apply Finset.prod_congr rfl
    intro r hr
    exact hnu r hr
  have hterm : s.selbergTerms d =
      ∏ r ∈ d.primeFactors, (2 : ℝ) / (r - 2 : ℝ) := by
    rw [s.selbergTerms_apply, hnuD, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r hr
    have hrR : (2 : ℝ) < r := by exact_mod_cast (by have := hprime r hr; omega)
    have hr0 : (r : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hden : (r : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
    rw [hnu r hr]
    field_simp [hr0, hden]
  rw [hterm]
  have hprod :
      (∏ r ∈ d.primeFactors, (2 : ℝ) / r) ≤
        ∏ r ∈ d.primeFactors, (2 : ℝ) / (r - 2 : ℝ) := by
    apply Finset.prod_le_prod
    · intro r hr
      positivity
    · intro r hr
      have hrR : (2 : ℝ) < r := by exact_mod_cast (by have := hprime r hr; omega)
      have hrpos : (0 : ℝ) < r := by linarith
      have hrsub : (0 : ℝ) < (r : ℝ) - 2 := by linarith
      rw [div_le_div_iff₀ hrpos hrsub]
      nlinarith
  calc
    _ ≥ ∏ r ∈ d.primeFactors, (2 : ℝ) / r := hprod
    _ = (2 : ℝ) ^ d.primeFactors.card / d := by
      rw [Finset.prod_div_distrib, Finset.prod_const]
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]

/-- Squarefree pairs contribute at most the finite Selberg denominator when
all local densities are `2/r` on primes that occur in such a pair. -/
theorem squarefreePairMass_le_pairSelbergDen (s : BoundingSieve)
    (A : Finset ℕ) (Y : ℕ)
    (hpos : ∀ a ∈ A, 0 < a)
    (hdiv : ∀ a ∈ A, ∀ b ∈ A, Squarefree (a*b) → a*b ∣ s.prodPrimes)
    (hbound : ∀ a ∈ A, ∀ b ∈ A, Squarefree (a*b) → a*b ≤ Y)
    (hlocal : ∀ a ∈ A, ∀ b ∈ A, ∀ _hab : Squarefree (a*b),
      ∀ r ∈ (a*b).primeFactors, s.nu r = 2 / (r : ℝ) ∧ 3 ≤ r) :
    squarefreePairMass A ≤ pairSelbergDen s Y := by
  classical
  let pairs := A ×ˢ A
  let goodPairs := pairs.filter (fun p : ℕ × ℕ => Squarefree (p.1*p.2))
  have hmass : squarefreePairMass A =
      ∑ p ∈ goodPairs, (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹ := by
    unfold squarefreePairMass
    rw [← Finset.sum_product']
    rw [← Finset.sum_filter]
  have hmaps (p : ℕ × ℕ) (hp : p ∈ goodPairs) :
      p.1*p.2 ∈ Nat.divisors s.prodPrimes := by
    have hp' := (Finset.mem_filter.mp hp).1
    have hmem := Finset.mem_product.mp hp'
    have hsf := (Finset.mem_filter.mp hp).2
    exact Nat.mem_divisors.mpr ⟨hdiv p.1 hmem.1 p.2 hmem.2 hsf,
      s.prodPrimes_ne_zero⟩
  have hfiber :
      (∑ d ∈ Nat.divisors s.prodPrimes,
        ∑ p ∈ goodPairs with p.1*p.2 = d,
          (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) =
        ∑ p ∈ goodPairs, (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹ :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun p => (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹)
  rw [hmass, ← hfiber]
  unfold pairSelbergDen
  apply Finset.sum_le_sum
  intro d hd
  let F := goodPairs.filter (fun p : ℕ × ℕ => p.1*p.2 = d)
  by_cases hF : F.Nonempty
  · obtain ⟨p, hp⟩ := hF
    have hpF := Finset.mem_filter.mp hp
    have hpSrc := Finset.mem_filter.mp hpF.1
    have hpMem := Finset.mem_product.mp hpSrc.1
    have hsf := hpSrc.2
    have hprod : p.1*p.2 = d := hpF.2
    have hdivd : d ∣ s.prodPrimes := by
      rw [← hprod]
      exact hdiv p.1 hpMem.1 p.2 hpMem.2 hsf
    have hsq : Squarefree d := by simpa [hprod] using hsf
    have hcut : d ≤ Y := by
      rw [← hprod]
      exact hbound p.1 hpMem.1 p.2 hpMem.2 hsf
    rw [if_pos hcut]
    have hfsum :
        (∑ p ∈ goodPairs with p.1*p.2 = d,
          (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) =
        (F.card : ℝ) * (d : ℝ)⁻¹ := by
      unfold F
      rw [Finset.sum_filter]
      calc
        (∑ q ∈ goodPairs,
            if q.1*q.2 = d then (q.1 : ℝ)⁻¹ * (q.2 : ℝ)⁻¹ else 0) =
          ∑ q ∈ goodPairs,
            if q.1*q.2 = d then (d : ℝ)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              split_ifs with heq
              · have heqR : (q.1 : ℝ) * (q.2 : ℝ) = (d : ℝ) := by exact_mod_cast heq
                have hq1 : (q.1 : ℝ) ≠ 0 := by
                  exact_mod_cast (Nat.ne_of_gt (hpos q.1
                    (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1))
                have hq2 : (q.2 : ℝ) ≠ 0 := by
                  exact_mod_cast (Nat.ne_of_gt (hpos q.2
                    (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2))
                rw [← heqR]
                field_simp
              · rfl
        _ = (F.card : ℝ) * (d : ℝ)⁻¹ := by
              rw [← Finset.sum_filter]
              change (∑ q ∈ F, (d : ℝ)⁻¹) = _
              simp [Finset.sum_const]
    have hFcard : F.card ≤ d.divisors.card := by
      apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => q.1)
      · intro q hq
        have hq1 := (Finset.mem_filter.mp hq).1
        have hqsrc := Finset.mem_filter.mp hq1
        have hqprod : q.1*q.2 = d := (Finset.mem_filter.mp hq).2
        apply Nat.mem_divisors.mpr
        refine ⟨?_, hsq.ne_zero⟩
        exact ⟨q.2, by rw [← hqprod]⟩
      · intro q hq q' hq' hfirst
        have hqprod := (Finset.mem_filter.mp hq).2
        have hq'prod := (Finset.mem_filter.mp hq').2
        have hqsrc := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
        have hqpos : 0 < q.1 := hpos q.1
          (Finset.mem_product.mp hqsrc.1).1
        have hq'fst : q'.1 = q.1 := hfirst.symm
        rw [hq'fst] at hq'prod
        apply Prod.ext
        · exact hfirst
        · exact Nat.eq_of_mul_eq_mul_left hqpos (hqprod.trans hq'prod.symm)
    have hfactor : (F.card : ℝ) ≤ (2 : ℝ)^d.primeFactors.card := by
      rw [safe_card_divisors_sqfree hsq] at hFcard
      exact_mod_cast hFcard
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast (Nat.pos_of_ne_zero hsq.ne_zero)
    have hFiberLe :
        (∑ p ∈ goodPairs with p.1*p.2 = d,
          (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) ≤
        (2 : ℝ)^d.primeFactors.card / d := by
      rw [hfsum]
      exact (div_le_div_of_nonneg_right hfactor hdpos.le)
    have hnuD : ∀ r ∈ d.primeFactors, s.nu r = 2 / (r : ℝ) := by
      intro r hr
      have hr' : r ∈ (p.1*p.2).primeFactors := by simpa [hprod] using hr
      exact (hlocal p.1 hpMem.1 p.2 hpMem.2 hsf r hr').1
    have hlargeD : ∀ r ∈ d.primeFactors, 3 ≤ r := by
      intro r hr
      have hr' : r ∈ (p.1*p.2).primeFactors := by simpa [hprod] using hr
      exact (hlocal p.1 hpMem.1 p.2 hpMem.2 hsf r hr').2
    exact hFiberLe.trans (safe_selberg_term_lower hdivd hsq hnuD hlargeD)
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have hzero : (∑ p ∈ goodPairs with p.1*p.2 = d,
        (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) = 0 := by
      simp [F, hFempty]
    rw [hzero]
    by_cases hcut : d ≤ Y
    · rw [if_pos hcut]
      have hddiv : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd).1
      exact le_of_lt (s.selbergTerms_pos hddiv)
    · rw [if_neg hcut]

end MathGacha
