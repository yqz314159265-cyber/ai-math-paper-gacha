import Gacha.AbelZeroPair
import Gacha.MertensPrefix

open Filter Topology

namespace MathGacha

noncomputable def badFibIndexLogWeight (K X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1),
    if n.Prime ∧ (Nat.fib n).minFac ≤ K * n then
      Real.log (n : ℝ) / (n : ℝ) else 0

noncomputable def goodFibIndexLogWeight (K X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 X,
    if n.Prime ∧ K * n < (Nat.fib n).minFac then
      Real.log (n : ℝ) / (n : ℝ) else 0

theorem badFibIndexLogWeight_div_log_tendsto_zero (K : ℕ) :
    Tendsto (fun X : ℕ => badFibIndexLogWeight K X / Real.log (X : ℝ))
      atTop (𝓝 0) := by
  let δ : ℕ → ℝ := fun X => (Real.log (X : ℝ))⁻¹
  let s : ℕ → ℝ := fun X => 1 + δ X
  have hX : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlog
  have hs : Tendsto s atTop (𝓝 1) := by
    simpa [s, δ] using tendsto_const_nhds.add hδ
  have hwithin : Tendsto s atTop (𝓝[>] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hs
    · filter_upwards [eventually_gt_atTop (2 : ℕ)] with X hX2
      have hpos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
      have : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hpos
      simpa [s, δ] using (lt_add_of_pos_right (1 : ℝ) this)
  have hAbel := (fullBadFibIndexAbelLimit K).comp hwithin
  have htarget : Tendsto (fun X : ℕ =>
      (s X - 1) * badFibIndexTsum K (s X)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hAbel
  have hle : ∀ᶠ X : ℕ in atTop,
      0 ≤ badFibIndexLogWeight K X / Real.log (X : ℝ) ∧
      badFibIndexLogWeight K X / Real.log (X : ℝ) ≤
        Real.exp 1 * ((s X - 1) * badFibIndexTsum K (s X)) := by
    filter_upwards [eventually_gt_atTop (2 : ℕ)] with X hX2
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    have hsX : 1 < s X := by
      simp [s, δ]
      positivity
    have hsum := summable_badFibIndexTerm K (s X) hsX
    have hterm : ∀ n ∈ Finset.range (X + 1),
        (if n.Prime ∧ (Nat.fib n).minFac ≤ K * n then
          Real.log (n : ℝ) / (n : ℝ) else 0) ≤
        Real.exp 1 * badFibIndexTerm K (s X) n := by
      intro n hn
      by_cases hb : n.Prime ∧ (Nat.fib n).minFac ≤ K * n
      · have hnX : n ≤ X := by simp only [Finset.mem_range] at hn; omega
        have hn2 : 0 < n := hb.1.pos
        have hn1 : 1 ≤ n := hb.1.one_le
        have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
        have hlelog : Real.log (n : ℝ) ≤ Real.log (X : ℝ) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast hnX
        have hexp : Real.exp (Real.log (n : ℝ) * δ X) ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          dsimp [δ]
          calc
            Real.log (n : ℝ) * (Real.log (X : ℝ))⁻¹ ≤
                Real.log (X : ℝ) * (Real.log (X : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_right hlelog (le_of_lt (inv_pos.mpr hlogX))
            _ = 1 := by field_simp [hlogX.ne']
        have hpow : (n : ℝ) ^ (s X) =
            (n : ℝ) * Real.exp (Real.log (n : ℝ) * δ X) := by
          rw [Real.rpow_def_of_pos (by exact_mod_cast hb.1.pos)]
          rw [show s X = 1 + δ X by rfl, mul_add, mul_one, Real.exp_add,
            Real.exp_log (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hb.1.pos)]
        have hden : (n : ℝ) ^ (s X) ≤ Real.exp 1 * (n : ℝ) := by
          rw [hpow]
          calc
            (n : ℝ) * Real.exp (Real.log (n : ℝ) * δ X) =
                Real.exp (Real.log (n : ℝ) * δ X) * (n : ℝ) := by ring
            _ ≤ Real.exp 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hexp (by positivity)
        simp [badFibIndexTerm, hb]
        have hpowpos : 0 < (n : ℝ) ^ (s X) := Real.rpow_pos_of_pos (by exact_mod_cast hn2) _
        have hfactor : 1 ≤ Real.exp 1 * (n : ℝ) / (n : ℝ) ^ (s X) := by
          rw [le_div_iff₀ hpowpos]
          simpa using hden
        rw [div_le_iff₀ (by exact_mod_cast hn2)]
        calc
          Real.log (n : ℝ) ≤ Real.log (n : ℝ) *
              (Real.exp 1 * (n : ℝ) / (n : ℝ) ^ (s X)) :=
            by simpa using (mul_le_mul_of_nonneg_left hfactor hlogn)
          _ = Real.exp 1 * (Real.log (n : ℝ) / (n : ℝ) ^ (s X)) * (n : ℝ) := by ring
      · simp [hb, badFibIndexTerm]
    have hfinle : badFibIndexLogWeight K X ≤
        Real.exp 1 * badFibIndexTsum K (s X) := by
      rw [badFibIndexLogWeight]
      calc
        _ ≤ ∑ n ∈ Finset.range (X + 1), Real.exp 1 * badFibIndexTerm K (s X) n := by
          apply Finset.sum_le_sum
          intro n hn
          exact hterm n hn
        _ = Real.exp 1 * ∑ n ∈ Finset.range (X + 1), badFibIndexTerm K (s X) n := by
          simp_rw [Finset.mul_sum]
        _ ≤ Real.exp 1 * badFibIndexTsum K (s X) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg 1)
          exact hsum.sum_le_tsum (Finset.range (X + 1)) (fun n hn => badFibIndexTerm_nonneg K (s X) n)
    have hnonneg : 0 ≤ badFibIndexLogWeight K X := by
      unfold badFibIndexLogWeight
      apply Finset.sum_nonneg
      intro n hn
      by_cases hb : n.Prime ∧ (Nat.fib n).minFac ≤ K * n
      · simp [hb]
        have hn1 : 1 ≤ n := hb.1.one_le
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) (by positivity)
      · simp [hb]
    constructor
    · exact div_nonneg hnonneg (le_of_lt hlogX)
    · have hnorm : (s X - 1) = (Real.log (X : ℝ))⁻¹ := by simp [s, δ]
      rw [hnorm]
      have htsum_nonneg : 0 ≤ badFibIndexTsum K (s X) :=
        tsum_nonneg (fun n => badFibIndexTerm_nonneg K (s X) n)
      calc
        badFibIndexLogWeight K X / Real.log (X : ℝ) ≤
            (Real.exp 1 * badFibIndexTsum K (s X)) / Real.log (X : ℝ) :=
          div_le_div_of_nonneg_right hfinle (le_of_lt hlogX)
        _ = Real.exp 1 * ((Real.log (X : ℝ))⁻¹ * badFibIndexTsum K (s X)) := by ring
        _ = Real.exp 1 * ((Real.log (X : ℝ))⁻¹ * badFibIndexTsum K (s X)) := rfl
  have hupper : Tendsto (fun X : ℕ =>
      Real.exp 1 * ((s X - 1) * badFibIndexTsum K (s X))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul htarget
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero hupper
  · filter_upwards [hle] with X hX
    exact hX.1
  · filter_upwards [hle] with X hX
    exact hX.2

theorem goodFibIndexLogWeight_div_log_tendsto_one (K : ℕ) :
    Tendsto (fun X : ℕ => goodFibIndexLogWeight K X / Real.log (X : ℝ))
      atTop (𝓝 1) := by
  have hrange (X : ℕ) : Finset.range (X + 1) = insert 0 (Finset.Ioc 0 X) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hbadIoc (X : ℕ) : badFibIndexLogWeight K X =
      ∑ n ∈ Finset.Ioc 0 X,
        if n.Prime ∧ (Nat.fib n).minFac ≤ K * n then
          Real.log (n : ℝ) / (n : ℝ) else 0 := by
    unfold badFibIndexLogWeight
    rw [hrange, Finset.sum_insert (by simp)]
    simp
  have hsplit (X : ℕ) : primeMertensPrefix X =
      goodFibIndexLogWeight K X + badFibIndexLogWeight K X := by
    rw [hbadIoc]
    unfold primeMertensPrefix goodFibIndexLogWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · by_cases hb : (Nat.fib n).minFac ≤ K * n
      · simp [hp, hb]
      · have hg : K * n < (Nat.fib n).minFac := by omega
        simp [hp, hb, hg]
    · simp [hp]
  have hprime := tendsto_primeMertensPrefix
  have hbad := badFibIndexLogWeight_div_log_tendsto_zero K
  have hsub : Tendsto (fun X : ℕ =>
      primeMertensPrefix X / Real.log (X : ℝ) -
        badFibIndexLogWeight K X / Real.log (X : ℝ)) atTop (𝓝 (1 - 0)) :=
    hprime.sub hbad
  have heq : ∀ᶠ X : ℕ in atTop,
      goodFibIndexLogWeight K X / Real.log (X : ℝ) =
        primeMertensPrefix X / Real.log (X : ℝ) -
          badFibIndexLogWeight K X / Real.log (X : ℝ) := by
    filter_upwards [eventually_gt_atTop (2 : ℕ)] with X hX
    have hlog : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).ne'
    rw [hsplit]
    field_simp
    ring
  simpa using Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hsub

end MathGacha
