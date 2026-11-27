import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter Topology

namespace MathGacha

noncomputable def eulerPrimeRecip (n : ℕ) : ℝ := if n.Prime then 1 / (n : ℝ) else 0

noncomputable def eulerAllowedRecip (j n : ℕ) : ℝ :=
  if n.Prime ∧ 2 < n ∧ ¬ n ∣ j then 1 / ((n : ℝ) - 1) else 0

noncomputable def eulerBadRecip (j n : ℕ) : ℝ :=
  if n.Prime ∧ ¬ (2 < n ∧ ¬ n ∣ j) then 1 / (n : ℝ) else 0

noncomputable def eulerFactor (r : ℕ) : ℝ := ((r : ℝ) - 2) / ((r : ℝ) - 1)

theorem eulerPrimeRecNotSummable : ¬ Summable eulerPrimeRecip := by
  intro h
  apply not_summable_one_div_on_primes
  convert h using 1
  ext n
  by_cases hn : n.Prime <;> simp [eulerPrimeRecip, Set.indicator, hn]

theorem eulerAllowedRecip_not_summable {j : ℕ} (hj : j ≠ 0) :
    ¬ Summable (eulerAllowedRecip j) := by
  intro hg
  let b : ℕ → ℝ := eulerBadRecip j
  let K := max j 2
  have hbfin : {n | b n ≠ 0}.Finite := by
    apply (Set.finite_Iic K).subset
    intro n hn
    change b n ≠ 0 at hn
    by_contra hnk
    have hlarge : K < n := lt_of_not_ge hnk
    have hgtj : j < n := lt_of_le_of_lt (le_max_left _ _) hlarge
    have hgt2 : 2 < n := lt_of_le_of_lt (le_max_right _ _) hlarge
    by_cases hp : n.Prime
    · have hdiv : ¬ n ∣ j := by
        intro hd
        have hnle : n ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) hd
        omega
      have : b n = 0 := by simp [b, eulerBadRecip, hp, hgt2, hdiv]
      exact hn this
    · have : b n = 0 := by simp [b, eulerBadRecip, hp]
      exact hn this
  have hb : Summable b := summable_of_hasFiniteSupport hbfin
  have hdom : ∀ n, 0 ≤ eulerPrimeRecip n ∧ eulerPrimeRecip n ≤ eulerAllowedRecip j n + b n := by
    intro n
    by_cases hp : n.Prime
    · by_cases hgood : 2 < n ∧ ¬ n ∣ j
      · have hn1 : 0 < (n : ℝ) - 1 := by
          have hnR : (2 : ℝ) < n := by exact_mod_cast hgood.1
          linarith
        have hden : (n : ℝ) - 1 ≤ n := by
          linarith
        have hrecip : (1 : ℝ) / n ≤ 1 / ((n : ℝ) - 1) :=
          div_le_div_of_nonneg_left (by norm_num) hn1 hden
        constructor
        · simp [eulerPrimeRecip, hp]
        · simpa [eulerPrimeRecip, eulerAllowedRecip, b, eulerBadRecip, hp, hgood] using hrecip
      · constructor
        · simp [eulerPrimeRecip, hp]
        · simp [eulerPrimeRecip, eulerAllowedRecip, b, eulerBadRecip, hp, hgood]
    · constructor
      · simp [eulerPrimeRecip, hp]
      · simp [eulerPrimeRecip, eulerAllowedRecip, b, eulerBadRecip, hp]
  have hprime : Summable eulerPrimeRecip :=
    Summable.of_nonneg_of_le (fun n ↦ (hdom n).1) (fun n ↦ (hdom n).2) (hg.add hb)
  exact eulerPrimeRecNotSummable hprime

/-- A finite product over primes greater than two and not dividing `j` can
be made arbitrarily small. -/
theorem existsEulerAvoidancePrimes {j : ℕ} (hj : j ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, (∀ r ∈ s, r.Prime ∧ 2 < r ∧ ¬ r ∣ j) ∧
      (∏ r ∈ s, eulerFactor r) < ε := by
  have hg0 (n : ℕ) : 0 ≤ eulerAllowedRecip j n := by
    dsimp [eulerAllowedRecip]
    split_ifs with h
    · have hnR : (2 : ℝ) < n := by exact_mod_cast h.2.1
      exact div_nonneg (by norm_num) (by linarith)
    · exact le_rfl
  have hgdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hg0).mp
    (eulerAllowedRecip_not_summable hj)
  let A : ℝ := -Real.log ε + 1
  obtain ⟨N, _, hN⟩ := exists_lt_of_tendsto_atTop hgdiv 0 A
  let s := (Finset.range N).filter (fun r => r.Prime ∧ 2 < r ∧ ¬ r ∣ j)
  have hs (r : ℕ) (hr : r ∈ s) : r.Prime ∧ 2 < r ∧ ¬ r ∣ j := by
    simpa [s] using (Finset.mem_filter.mp hr).2
  have hsumS : (∑ r ∈ s, 1 / ((r : ℝ) - 1)) =
      ∑ n ∈ Finset.range N, eulerAllowedRecip j n := by
    simp [s, eulerAllowedRecip, Finset.sum_filter]
  have hsumlarge : A < ∑ r ∈ s, 1 / ((r : ℝ) - 1) := by
    rw [hsumS]
    exact hN
  have hden (r : ℕ) (hr : r ∈ s) : (1 : ℝ) < (r : ℝ) - 1 := by
    have hrR : (2 : ℝ) < r := by exact_mod_cast (hs r hr).2.1
    linarith
  have hfacpos (r : ℕ) (hr : r ∈ s) : 0 < 1 - 1 / ((r : ℝ) - 1) := by
    have hden' := hden r hr
    have hdiv : (1 : ℝ) / ((r : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith)).2 hden'
    linarith
  have hlog (r : ℕ) (hr : r ∈ s) :
      Real.log (1 - 1 / ((r : ℝ) - 1)) ≤ -(1 / ((r : ℝ) - 1)) := by
    have h := Real.log_le_sub_one_of_pos (hfacpos r hr)
    linarith
  have hprodpos : 0 < ∏ r ∈ s, (1 - 1 / ((r : ℝ) - 1)) :=
    Finset.prod_pos fun r hr ↦ hfacpos r hr
  have hprodexp : (∏ r ∈ s, (1 - 1 / ((r : ℝ) - 1))) ≤
      Real.exp (-(∑ r ∈ s, 1 / ((r : ℝ) - 1))) := by
    apply (Real.log_le_iff_le_exp hprodpos).mp
    rw [Real.log_prod (fun r hr ↦ (hfacpos r hr).ne')]
    calc
      (∑ r ∈ s, Real.log (1 - 1 / ((r : ℝ) - 1))) ≤
          ∑ r ∈ s, -(1 / ((r : ℝ) - 1)) := Finset.sum_le_sum fun r hr ↦ hlog r hr
      _ = -(∑ r ∈ s, 1 / ((r : ℝ) - 1)) := by rw [Finset.sum_neg_distrib]
  have heulerFactor (r : ℕ) (hr : r ∈ s) :
      eulerFactor r = 1 - 1 / ((r : ℝ) - 1) := by
    dsimp [eulerFactor]
    have hne : (r : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith [hden r hr])
    field_simp
    ring
  have hproduct : (∏ r ∈ s, eulerFactor r) < ε := by
    have hA : -A < Real.log ε := by dsimp [A]; linarith
    have hexpA : Real.exp (-A) < ε := by
      rw [← Real.exp_log hε]
      exact Real.exp_lt_exp.mpr hA
    have hsumexp : Real.exp (-(∑ r ∈ s, 1 / ((r : ℝ) - 1))) < ε := by
      calc
        _ < Real.exp (-A) := Real.exp_lt_exp.mpr (by linarith [hsumlarge])
        _ < ε := hexpA
    calc
      (∏ r ∈ s, eulerFactor r) = ∏ r ∈ s, (1 - 1 / ((r : ℝ) - 1)) :=
        Finset.prod_congr rfl fun r hr ↦ heulerFactor r hr
      _ ≤ Real.exp (-(∑ r ∈ s, 1 / ((r : ℝ) - 1))) := hprodexp
      _ < ε := hsumexp
  exact ⟨s, hs, hproduct⟩

end MathGacha
