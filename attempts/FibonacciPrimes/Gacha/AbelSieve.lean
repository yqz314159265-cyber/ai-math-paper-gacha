import Mathlib.NumberTheory.LSeries.PrimesInAP
import Gacha.WeightedSieve

open Complex LSeries ArithmeticFunction ArithmeticFunction.vonMangoldt
open Filter Topology
open scoped LSeries.notation
set_option linter.style.haveILetI false

namespace MathGacha

variable {q : ℕ} {a : ZMod q}

/-- The Abel-smoothed complex L-series has residue `1 / φ(q)` at `s = 1`. -/
theorem tendsto_complexResidueClass_abel_weight [NeZero q] (ha : IsUnit a) :
    Tendsto
      (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * L ↗(residueClass a) (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℂ)⁻¹)) := by
  let G : ℝ → ℂ := fun x => LFunctionResidueClassAux a (x : ℂ)
  have hGcont : ContinuousOn G (Set.Ici (1 : ℝ)) := by
    exact (continuousOn_LFunctionResidueClassAux a).comp
      continuous_ofReal.continuousOn (by
        intro x hx
        simpa only [Set.mem_ofPred_eq, Complex.ofReal_re, Set.mem_Ici] using hx)
  have hG : Tendsto G (𝓝[>] (1 : ℝ)) (𝓝 (G 1)) := by
    exact (hGcont.continuousWithinAt (by simp : (1 : ℝ) ∈ Set.Ici 1)).mono_left
      (nhdsWithin_mono (1 : ℝ) (by
        intro x hx
        exact le_of_lt (Set.mem_Ioi.mp hx)))
  have hlin : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hid : Tendsto id (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hsub : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using hid.sub_const (1 : ℝ)
    have h := (continuous_ofReal.tendsto (0 : ℝ)).comp hsub
    simpa only [Function.comp_def, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_zero] using h
  have hrem : Tendsto
      (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * G x)
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    convert hlin.mul hG using 1
    simp [G]
  have hformula : (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * L ↗(residueClass a) (x : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * G x + (q.totient : ℂ)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have heq := eqOn_LFunctionResidueClassAux (a := a) ha hx'
    have hne : (x : ℂ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hx.ne')
    have hsub := heq
    dsimp [G] at hsub
    have hsub' : L ↗(residueClass a) (x : ℂ) = G x +
        (q.totient : ℂ)⁻¹ / ((x : ℂ) - 1) := by
      have hsub'' := hsub.symm
      rw [sub_eq_iff_eq_add] at hsub''
      simpa [G, add_comm] using hsub''
    rw [hsub']
    rw [show ((x - 1 : ℝ) : ℂ) = (x : ℂ) - 1 by simp]
    rw [mul_add, mul_div_cancel₀ _ hne]
  have hlim : Tendsto
      (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * L ↗(residueClass a) (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℂ)⁻¹)) := by
    have := hrem.add_const ((q.totient : ℂ)⁻¹)
    simpa using this.congr' hformula.symm
  exact hlim

/-- Along the real axis, the real part of the complex L-series is the
ordinary real Dirichlet series with denominator `n^x`. -/
theorem re_residueClass_LSeries_eq_tsum {x : ℝ} (hx : 1 < x) :
    (L ↗(residueClass a) (x : ℂ)).re =
      ∑' n : ℕ, residueClass a n / (n : ℝ) ^ x := by
  rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
    (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by norm_cast]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero, zero_re, residueClass_apply_zero, zero_div]
  · simp only [term_of_ne_zero hn, ← ofReal_natCast n, ← ofReal_cpow n.cast_nonneg,
      ← ofReal_div, ofReal_re]

/-- The corresponding real-valued Abel limit for the full von Mangoldt
Dirichlet series in the residue class. -/
theorem tendsto_realResidueClass_abel_weight [NeZero q] (ha : IsUnit a) :
    Tendsto
      (fun x : ℝ => (x - 1) * ∑' n : ℕ, residueClass a n / (n : ℝ) ^ x)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h := tendsto_complexResidueClass_abel_weight (a := a) ha
  have hre : Tendsto
      (fun x : ℝ => (((x - 1 : ℝ) : ℂ) * L ↗(residueClass a) (x : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (((q.totient : ℂ)⁻¹).re)) :=
    (continuous_re.continuousAt.tendsto).comp h
  have hEq : (fun x : ℝ => (((x - 1 : ℝ) : ℂ) * L ↗(residueClass a) (x : ℂ)).re) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => (x - 1) * ∑' n : ℕ, residueClass a n / (n : ℝ) ^ x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [re_residueClass_LSeries_eq_tsum (a := a) hx]
  have hlim := hre.congr' hEq
  have hval : (((q.totient : ℂ)⁻¹).re) = (q.totient : ℝ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  simpa only [hval] using hlim

noncomputable def primeResidueTerm (a : ZMod q) (x : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x

noncomputable def nonprimeResidueTerm (a : ZMod q) (x : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x

noncomputable def nonprimeResidueTsum (a : ZMod q) (x : ℝ) : ℝ :=
  ∑' n : ℕ, nonprimeResidueTerm a x n

noncomputable def primeResidueTsum (a : ZMod q) (x : ℝ) : ℝ :=
  ∑' n : ℕ, primeResidueTerm a x n

noncomputable def sievedTerm (K : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ K * n < (Nat.fib n).minFac then Real.log n / (n : ℝ) ^ x else 0

noncomputable def sievedTsum (K : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, sievedTerm K x n

noncomputable def smallClassTerm (a : ZMod q) (x : ℝ) (n : ℕ) : ℝ :=
  if n < 6 then primeResidueTerm a x n else 0

noncomputable def finiteCapTerm (n : ℕ) : ℝ :=
  if n < 6 ∧ n.Prime then Real.log n / (n : ℝ) else 0

/-- The non-prime part of the residue-class series is bounded by its summable
weight at `x = 1`, so its contribution vanishes after multiplication by `x-1`. -/
theorem tendsto_scaled_nonprimeResidueTsum (a : ZMod q) :
    Tendsto (fun x : ℝ => (x - 1) * nonprimeResidueTsum a x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  let M (n : ℕ) : ℝ := (if n.Prime then 0 else residueClass a n) / n
  let C : ℝ := ∑' n : ℕ, M n
  have hM : Summable M := by
    change Summable (fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / n)
    exact summable_residueClass_non_primes_div (a := a)
  have hM0 (n : ℕ) : 0 ≤ M n := by
    dsimp [M]
    positivity [residueClass_nonneg a n]
  have hC0 : 0 ≤ C := tsum_nonneg hM0
  have hterm0 (x : ℝ) (n : ℕ) : 0 ≤ nonprimeResidueTerm a x n := by
    dsimp [nonprimeResidueTerm]
    positivity [residueClass_nonneg a n]
  have hle (x : ℝ) (hx : 1 < x) (n : ℕ) : nonprimeResidueTerm a x n ≤ M n := by
    dsimp [nonprimeResidueTerm, M]
    by_cases hn0 : n = 0
    · subst n
      simp [residueClass]
    · by_cases hprime : n.Prime
      · simp [hprime]
      · have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
        have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
        have hpow : (n : ℝ) ≤ (n : ℝ) ^ x := by
          simpa using Real.rpow_le_rpow_of_exponent_le hn1 hx.le
        have hnum : 0 ≤ (if n.Prime then 0 else residueClass a n) := by
          split_ifs
          positivity [residueClass_nonneg a n]
        exact div_le_div_of_nonneg_left hnum hn hpow
  have hsum (x : ℝ) (hx : 1 < x) : Summable (nonprimeResidueTerm a x) :=
    Summable.of_nonneg_of_le (hterm0 x) (hle x hx) hM
  have htail_le (x : ℝ) (hx : 1 < x) : nonprimeResidueTsum a x ≤ C :=
    Summable.tsum_le_tsum (hle x hx) (hsum x hx) hM
  have htail0 (x : ℝ) (hx : 1 < x) : 0 ≤ nonprimeResidueTsum a x :=
    tsum_nonneg (hterm0 x)
  have hlinear : Tendsto (fun x : ℝ => (x - 1) * C)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have h := tendsto_id.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ))
      simpa using h.sub_const (1 : ℝ)
    simpa using hid.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) _ (𝓝 C))
  refine squeeze_zero' ?_ ?_ hlinear
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (sub_nonneg.mpr hx.le) (htail0 x hx)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_le_mul_of_nonneg_left (htail_le x hx) (sub_nonneg.mpr hx.le)

theorem summable_primeResidueTerm [NeZero q] (a : ZMod q) (x : ℝ) (hx : 1 < x) :
    Summable (primeResidueTerm a x) := by
  let f (n : ℕ) := residueClass a n / (n : ℝ) ^ x
  have hf : Summable f := by
    change Summable (fun n : ℕ => residueClass a n / (n : ℝ) ^ x)
    exact summable_real_of_abscissaOfAbsConv_lt <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by norm_cast
  have hf0 (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    positivity [residueClass_nonneg a n]
  have hp0 (n : ℕ) : 0 ≤ primeResidueTerm a x n := by
    dsimp [primeResidueTerm]
    positivity [residueClass_nonneg a n]
  have hle (n : ℕ) : primeResidueTerm a x n ≤ f n := by
    by_cases hn : n.Prime
    · simp [primeResidueTerm, f, hn]
    · simp [primeResidueTerm, f, hn]
      exact hf0 n
  exact hf.of_nonneg_of_le hp0 hle

/-- The real L-series splits into its prime and non-prime terms. -/
theorem residueClass_tsum_eq_prime_add_nonprime [NeZero q] (x : ℝ) (hx : 1 < x) :
    (∑' n : ℕ, residueClass a n / (n : ℝ) ^ x) =
      primeResidueTsum a x + nonprimeResidueTsum a x := by
  let f (n : ℕ) := residueClass a n / (n : ℝ) ^ x
  have hf : Summable f := by
    change Summable (fun n : ℕ => residueClass a n / (n : ℝ) ^ x)
    exact summable_real_of_abscissaOfAbsConv_lt <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by norm_cast
  have hf0 (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    positivity [residueClass_nonneg a n]
  have hp0 (n : ℕ) : 0 ≤ primeResidueTerm a x n := by
    dsimp [primeResidueTerm]
    positivity [residueClass_nonneg a n]
  have hnp0 (n : ℕ) : 0 ≤ nonprimeResidueTerm a x n := by
    dsimp [nonprimeResidueTerm]
    positivity [residueClass_nonneg a n]
  have hp_le (n : ℕ) : primeResidueTerm a x n ≤ f n := by
    by_cases hn : n.Prime
    · simp [primeResidueTerm, f, hn]
    · simp [primeResidueTerm, f, hn]
      exact hf0 n
  have hnp_le (n : ℕ) : nonprimeResidueTerm a x n ≤ f n := by
    by_cases hn : n.Prime
    · simp [nonprimeResidueTerm, f, hn]
      exact hf0 n
    · simp [nonprimeResidueTerm, f, hn]
  have hpSum : Summable (primeResidueTerm a x) := hf.of_nonneg_of_le hp0 hp_le
  have hnpSum : Summable (nonprimeResidueTerm a x) := hf.of_nonneg_of_le hnp0 hnp_le
  have hpoint (n : ℕ) : f n = primeResidueTerm a x n + nonprimeResidueTerm a x n := by
    by_cases hn : n.Prime <;> simp [f, primeResidueTerm, nonprimeResidueTerm, hn]
  calc
    _ = ∑' n : ℕ, (primeResidueTerm a x n + nonprimeResidueTerm a x n) :=
      tsum_congr fun n => hpoint n
    _ = primeResidueTsum a x + ∑' n : ℕ, nonprimeResidueTerm a x n := by
      rw [Summable.tsum_add hpSum hnpSum, primeResidueTsum]
    _ = primeResidueTsum a x + nonprimeResidueTsum a x := by rfl

/-- Removing the non-prime powers leaves the same Abel pole coefficient for
the prime-only real weight `log(p) / p^x`. -/
theorem tendsto_primeResidueClass_abel_weight [NeZero q] (ha : IsUnit a) :
    Tendsto (fun x : ℝ => (x - 1) * primeResidueTsum a x)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hfull := tendsto_realResidueClass_abel_weight (a := a) ha
  have htail := tendsto_scaled_nonprimeResidueTsum (a := a)
  have hsub := hfull.sub htail
  have heq : (fun x : ℝ => (x - 1) * primeResidueTsum a x) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => (x - 1) * ∑' n : ℕ, residueClass a n / (n : ℝ) ^ x -
        (x - 1) * nonprimeResidueTsum a x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [residueClass_tsum_eq_prime_add_nonprime (a := a) x hx]
    ring
  simpa using hsub.congr' heq.symm

/-- For each fixed sieve, the sum of its surviving weights is at least the
prime weight in the selected residue class, up to the first six terms. -/
theorem linearFormsClass_sum_le_sieved_add_small (K : ℕ) (x : ℝ) (hx : 1 < x) :
    primeResidueTsum (a := (3 : ZMod (MathGacha.linearFormsModulus K))) x ≤
      sievedTsum K x +
        ∑' n : ℕ, smallClassTerm (a := (3 : ZMod (MathGacha.linearFormsModulus K))) x n := by
  classical
  let M := MathGacha.linearFormsModulus K
  let a : ZMod M := 3
  have hM0 : M ≠ 0 := by
    intro hz
    have hc := MathGacha.linearFormsModulusCoprime K
    simp [M, hz] at hc
  haveI : NeZero M := ⟨hM0⟩
  have hclassSum : Summable (primeResidueTerm a x) := summable_primeResidueTerm a x hx
  have hsmall : Summable (smallClassTerm a x) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_Iio 6).subset
    intro n hn
    by_contra hnnot
    have hn6 : ¬ n < 6 := by simpa only [Set.mem_Iio] using hnnot
    apply hn
    simp [smallClassTerm, hn6]
  haveI : NeZero 1 := ⟨by norm_num⟩
  have hallPrime : Summable (primeResidueTerm (0 : ZMod 1) x) :=
    summable_primeResidueTerm (0 : ZMod 1) x hx
  have hscreen0 (n : ℕ) : 0 ≤ sievedTerm K x n := by
    dsimp [sievedTerm]
    split_ifs
    · positivity
    · exact le_rfl
  have hscreen_le (n : ℕ) : sievedTerm K x n ≤ primeResidueTerm (0 : ZMod 1) x n := by
    have hcast : (n : ZMod 1) = 0 := Subsingleton.elim _ _
    have hres : residueClass (0 : ZMod 1) n = vonMangoldt n := by
      simp [residueClass, hcast]
    by_cases hn : n.Prime
    · rw [sievedTerm, primeResidueTerm]
      simp only [hn, ↓reduceIte]
      by_cases hs : K * n < (Nat.fib n).minFac
      · simp [hs, hres, vonMangoldt_apply_prime hn]
      · simp only [hs, hres, vonMangoldt_apply_prime hn]
        positivity
    · simp [sievedTerm, primeResidueTerm, hn]
  have hscreen : Summable (sievedTerm K x) :=
    hallPrime.of_nonneg_of_le hscreen0 hscreen_le
  have hterm (n : ℕ) : primeResidueTerm a x n ≤
      sievedTerm K x n + smallClassTerm a x n := by
    by_cases hsmall' : n < 6
    · calc
        _ = smallClassTerm a x n := by simp [smallClassTerm, hsmall']
        _ ≤ sievedTerm K x n + smallClassTerm a x n := by linarith [hscreen0 n]
    · have hnlarge : 6 ≤ n := by omega
      by_cases hclass : n.Prime ∧ (n : ZMod M) = a
      · have hp := hclass.1
        have hmod : n ≡ 3 [MOD M] := by
          apply (ZMod.natCast_eq_natCast_iff n 3 M).mp
          simpa [a] using hclass.2
        have hbound := MathGacha.leastFactorBoundOnClass hp (by omega) hmod
        have hresClass : residueClass a n = vonMangoldt n := by
          simp [residueClass, hclass.2]
        simp [primeResidueTerm, sievedTerm, smallClassTerm, hclass, hbound,
          vonMangoldt_apply_prime hp]
        simp [hsmall']
      · by_cases hp : n.Prime
        · have hneq : (n : ZMod M) ≠ a := by
            intro heq
            exact hclass ⟨hp, heq⟩
          have hresClass : residueClass a n = 0 := by
            simp [residueClass, hneq]
          simp [primeResidueTerm, sievedTerm, smallClassTerm, hp, hresClass, hsmall']
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          split_ifs <;> positivity [Real.log_nonneg hn1]
        · simp [primeResidueTerm, sievedTerm, smallClassTerm, hp, hsmall']
  have hsum := hscreen.add hsmall
  have hineq := Summable.tsum_le_tsum hterm hclassSum hsum
  calc
    primeResidueTsum a x = ∑' n : ℕ, primeResidueTerm a x n := rfl
    _ ≤ ∑' n : ℕ, (sievedTerm K x n + smallClassTerm a x n) := hineq
    _ = sievedTsum K x + ∑' n : ℕ, smallClassTerm a x n := by
      rw [Summable.tsum_add hscreen hsmall, sievedTsum]

/-- The finite correction from indices below six is bounded uniformly for `x > 1`. -/
theorem smallClassTerm_le_finiteCap (a : ZMod q) {x : ℝ} (hx : 1 < x) (n : ℕ) :
    smallClassTerm a x n ≤ finiteCapTerm n := by
  by_cases hs : n < 6
  · by_cases hp : n.Prime
    · simp only [smallClassTerm, if_pos hs, primeResidueTerm, if_pos hp,
        finiteCapTerm, if_pos (show n < 6 ∧ n.Prime from ⟨hs, hp⟩)]
      have hnum : residueClass a n ≤ Real.log n := by
        rw [← vonMangoldt_apply_prime hp]
        exact residueClass_le a n
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hp.pos
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n from le_trans (by norm_num) hp.two_le)
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ x := by
        simpa using Real.rpow_le_rpow_of_exponent_le hn1 hx.le
      calc
        residueClass a n / (n : ℝ) ^ x ≤ Real.log n / (n : ℝ) ^ x :=
          div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ Real.log n / (n : ℝ) :=
          div_le_div_of_nonneg_left (Real.log_nonneg hn1) hnpos hpow
    · simp [smallClassTerm, primeResidueTerm, finiteCapTerm, hs, hp]
  · simp [smallClassTerm, finiteCapTerm, hs]

/-- For every constant below `1/φ(M_K)`, the normalized Abel weight of
prime indices surviving the moving least-factor sieve eventually exceeds it. -/
theorem linearFormsSievedWeight_eventually_gt {K : ℕ}
    {c : ℝ} (hc : c < ((MathGacha.linearFormsModulus K).totient : ℝ)⁻¹) :
    ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), c < (x - 1) * sievedTsum K x := by
  classical
  let M := MathGacha.linearFormsModulus K
  let a : ZMod M := 3
  have hM0 : M ≠ 0 := by
    intro hz
    have hcop := MathGacha.linearFormsModulusCoprime K
    simp [M, hz] at hcop
  haveI : NeZero M := ⟨hM0⟩
  have hcop := MathGacha.linearFormsModulusCoprime K
  have ha : IsUnit a := by
    change IsUnit (3 : ZMod M)
    exact (ZMod.isUnit_iff_coprime 3 M).mpr hcop
  have hclass := tendsto_primeResidueClass_abel_weight (a := a) ha
  have hcapSum : Summable finiteCapTerm := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_Iio 6).subset
    intro n hn
    by_contra hnot
    have hn6 : ¬ n < 6 := by simpa only [Set.mem_Iio] using hnot
    exact hn (by simp [finiteCapTerm, hn6])
  have hcap0 (n : ℕ) : 0 ≤ finiteCapTerm n := by
    dsimp [finiteCapTerm]
    split_ifs with h
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n from le_trans (by norm_num) h.2.two_le)
      exact div_nonneg (Real.log_nonneg hn1) (Nat.cast_nonneg _)
    · exact le_rfl
  let C : ℝ := ∑' n : ℕ, finiteCapTerm n
  have hC0 : 0 ≤ C := tsum_nonneg hcap0
  have hsmallTendsto : Tendsto
      (fun x : ℝ => (x - 1) * ∑' n : ℕ, smallClassTerm a x n)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hsmallSum (x : ℝ) (hx : 1 < x) : Summable (smallClassTerm a x) := by
      apply summable_of_hasFiniteSupport
      apply (Set.finite_Iio 6).subset
      intro n hn
      by_contra hnot
      have hn6 : ¬ n < 6 := by simpa only [Set.mem_Iio] using hnot
      exact hn (by simp [smallClassTerm, hn6])
    have hsmallLe (x : ℝ) (hx : 1 < x) :
        ∑' n : ℕ, smallClassTerm a x n ≤ C := by
      exact Summable.tsum_le_tsum (fun n => smallClassTerm_le_finiteCap a hx n)
        (hsmallSum x hx) hcapSum
    have hsmallNonneg (x : ℝ) (hx : 1 < x) : 0 ≤ ∑' n : ℕ, smallClassTerm a x n :=
      tsum_nonneg (fun n => by
        dsimp [smallClassTerm]
        split_ifs
        · dsimp [primeResidueTerm]
          positivity [residueClass_nonneg a n]
        · exact le_rfl)
    have hlinear : Tendsto (fun x : ℝ => (x - 1) * C)
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
        have h := tendsto_id.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ))
        simpa using h.sub_const (1 : ℝ)
      simpa using hid.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) _ (𝓝 C))
    refine squeeze_zero' ?_ ?_ hlinear
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg (sub_nonneg.mpr hx.le) (hsmallNonneg x hx)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_le_mul_of_nonneg_left (hsmallLe x hx) (sub_nonneg.mpr hx.le)
  have hmain : Tendsto
      (fun x : ℝ => (x - 1) * primeResidueTsum a x -
        (x - 1) * ∑' n : ℕ, smallClassTerm a x n)
      (𝓝[>] (1 : ℝ)) (𝓝 ((M.totient : ℝ)⁻¹)) := by
    simpa using hclass.sub hsmallTendsto
  have hineq : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      (x - 1) * primeResidueTsum a x -
        (x - 1) * ∑' n : ℕ, smallClassTerm a x n ≤ (x - 1) * sievedTsum K x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsum := linearFormsClass_sum_le_sieved_add_small K x hx
    have hpos : 0 ≤ x - 1 := sub_nonneg.mpr hx.le
    nlinarith [mul_le_mul_of_nonneg_left hsum hpos]
  have hc' : c < (M.totient : ℝ)⁻¹ := by exact_mod_cast hc
  filter_upwards [hmain.eventually (Ioi_mem_nhds hc'), hineq] with x hmainx hineqx
  exact lt_of_lt_of_le hmainx hineqx

end MathGacha
