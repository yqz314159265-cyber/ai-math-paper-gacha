import Gacha.SquarefreePairMass

open Finset

namespace MathGacha

/-- Divisibility by `d` removes at least a factor `d` of a finite coprime
harmonic sum. -/
theorem coprimeDivisorReciprocal_le (U k d : ℕ) (hd : 0 < d) :
    (∑ a ∈ (Finset.Icc 1 U).filter (fun a => a.Coprime k),
      divisorReciprocal d a) ≤
      (∑ a ∈ (Finset.Icc 1 U).filter (fun a => a.Coprime k), (a : ℝ)⁻¹) / d := by
  classical
  let A := (Finset.Icc 1 U).filter (fun a => a.Coprime k)
  by_cases hdk : d.Coprime k
  · let B := (Finset.Icc 1 U).filter (fun q => q.Coprime k ∧ d*q ≤ U)
    have hA : (∑ a ∈ A, divisorReciprocal d a) =
        ∑ a ∈ A.filter (fun a => d ∣ a), (a : ℝ)⁻¹ := by
      simp [divisorReciprocal, Finset.sum_filter]
    have hbij : (∑ a ∈ A.filter (fun a => d ∣ a), (a : ℝ)⁻¹) =
        ∑ q ∈ B, (d*q : ℝ)⁻¹ := by
      symm
      refine Finset.sum_bij (fun q _ => d*q) ?_ ?_ ?_ ?_
      · intro q hq
        simp only [B, Finset.mem_filter, Finset.mem_Icc] at hq
        apply Finset.mem_filter.mpr
        have hqpos : 0 < q := by omega
        have hdqpos : 0 < d*q := Nat.mul_pos hd hqpos
        have hdqge : 1 ≤ d*q := by omega
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdqge, hq.2.2⟩,
          (Nat.coprime_mul_iff_left).2 ⟨hdk, hq.2.1⟩⟩, ?_⟩
        exact dvd_mul_right d q
      · intro q hq q' hq' he
        exact Nat.mul_left_cancel hd he
      · intro a ha
        simp only [A, Finset.mem_filter, Finset.mem_Icc] at ha
        have hdiv := ha.2
        have hmul : d*(a/d)=a := Nat.mul_div_cancel' hdiv
        refine ⟨a/d, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          have hqpos : 0 < a/d := Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) hd
          have hqle : a/d ≤ U := (Nat.div_le_self _ _).trans ha.1.1.2
          have hqge : 1 ≤ a/d := by omega
          refine ⟨Finset.mem_Icc.mpr ⟨hqge, hqle⟩, ?_⟩
          exact ⟨Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hdiv) ha.1.2,
            by rw [hmul]; exact ha.1.1.2⟩
        · exact hmul
      · intro q hq
        simp [Nat.cast_mul]
    have hsubset : (∑ q ∈ B, (q : ℝ)⁻¹) ≤ ∑ a ∈ A, (a : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        simp only [B, A, Finset.mem_filter] at hq ⊢
        exact ⟨hq.1, hq.2.1⟩
      · intro q hq hqA
        positivity
    have hscale : (∑ q ∈ B, (d*q : ℝ)⁻¹) =
        (d : ℝ)⁻¹ * ∑ q ∈ B, (q : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqpos : 0 < q := by
        have hqlo := (Finset.mem_Icc.mp ((Finset.mem_filter.mp hq).1)).1
        omega
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
      field_simp [hd0, hq0]
    rw [show (∑ a ∈ (Finset.Icc 1 U).filter (fun a => a.Coprime k),
        divisorReciprocal d a) = ∑ a ∈ A, divisorReciprocal d a by rfl,
      hA, hbij, hscale]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    calc
      (d : ℝ)⁻¹ * ∑ q ∈ B, (q : ℝ)⁻¹ ≤
          (d : ℝ)⁻¹ * ∑ a ∈ A, (a : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hsubset (inv_nonneg.mpr hdR.le)
      _ = (∑ a ∈ A, (a : ℝ)⁻¹) / d := by
        rw [div_eq_mul_inv]
        ring
  · have hzero : (∑ a ∈ A, divisorReciprocal d a) = 0 := by
      apply sum_eq_zero
      intro a ha
      simp only [A, Finset.mem_filter] at ha
      unfold divisorReciprocal
      split_ifs with hda
      · exact False.elim (hdk (Nat.Coprime.of_dvd_left hda ha.2))
      · rfl
    rw [show (∑ a ∈ (Finset.Icc 1 U).filter (fun a => a.Coprime k),
        divisorReciprocal d a) = ∑ a ∈ A, divisorReciprocal d a by rfl, hzero]
    have hnonneg : 0 ≤ ∑ a ∈ A, (a : ℝ)⁻¹ :=
      sum_nonneg fun a _ => by positivity
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    exact div_nonneg hnonneg hdR.le

/-- An even modulus leaves a quarter of the finite pair harmonic mass on
pairs whose product is squarefree. -/
theorem coprimePairMass_quarter (k U : ℕ) (hk : 2 ∣ k) :
    (∑ a ∈ (Finset.Icc 1 U).filter (fun a => a.Coprime k), (a : ℝ)⁻¹)^2 / 4 ≤
      squarefreePairMass ((Finset.Icc 1 U).filter (fun a => a.Coprime k)) := by
  let A := (Finset.Icc 1 U).filter (fun a => a.Coprime k)
  have hA : ∀ a ∈ A, 0 < a ∧ a ≤ U ∧ ¬2 ∣ a := by
    intro a ha
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at ha
    refine ⟨by omega, ha.1.2, ?_⟩
    intro h2a
    have hg := Nat.dvd_gcd h2a hk
    rw [ha.2.gcd_eq_one] at hg
    norm_num at hg
  have hdiv : ∀ d : ℕ, 0 < d →
      ∑ a ∈ A, divisorReciprocal d a ≤ (∑ a ∈ A, (a : ℝ)⁻¹) / d := by
    intro d hd
    simpa [A] using coprimeDivisorReciprocal_le U k d hd
  simpa [A] using squarefreePairMass_quarter A hA hdiv

end MathGacha
