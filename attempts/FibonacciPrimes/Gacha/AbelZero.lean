import Gacha.AbelSieve
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt

namespace MathGacha

variable {q : ℕ} [NeZero q]

noncomputable def abelZeroNormalizedPrimeClass (a : ZMod q) (x : ℝ) : ℝ :=
  (x - 1) * primeResidueTsum a x

/-- A finite collection of invertible residue classes has Abel mass equal to
its cardinality divided by the totient. -/
theorem tendsto_finitePrimeClassMass (T : Finset (ZMod q))
    (hunit : ∀ a ∈ T, IsUnit a) :
    Tendsto (fun x : ℝ => ∑ a ∈ T, abelZeroNormalizedPrimeClass a x)
      (𝓝[>] (1 : ℝ)) (𝓝 (∑ _a ∈ T, (q.totient : ℝ)⁻¹)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [abelZeroNormalizedPrimeClass]
  | @insert a T ha ih =>
      have haUnit : IsUnit a := hunit a (by simp)
      have hTunit : ∀ b ∈ T, IsUnit b := by
        intro b hb
        exact hunit b (by simp [hb])
      have hhead := tendsto_primeResidueClass_abel_weight (a := a) haUnit
      have htail := ih hTunit
      convert hhead.add htail using 1
      · simp [abelZeroNormalizedPrimeClass, Finset.sum_insert, ha]
      · simp [ha]
        ring

noncomputable def candidatePrimeTerm (P : ℕ → Prop) [DecidablePred P]
    (x : ℝ) (n : ℕ) : ℝ := if P n then Real.log n / (n : ℝ) ^ x else 0

noncomputable def candidatePrimeTsum (P : ℕ → Prop) [DecidablePred P]
    (x : ℝ) : ℝ := ∑' n : ℕ, candidatePrimeTerm P x n

theorem abelZeroSummableFinsetSum {α : Type*} (T : Finset α)
    (f : α → ℕ → ℝ) (hf : ∀ a ∈ T, Summable (f a)) :
    Summable (fun n => Finset.sum T (fun a => f a n)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (by
        intro b hb
        exact hf b (by simp [hb])))

/-- If every prime in a candidate family lies in one of finitely many unit
classes, its normalized Abel mass is eventually bounded by the total mass of
those classes. -/
theorem eventually_candidatePrimeMass_le_classes {P : ℕ → Prop} [DecidablePred P]
    (T : Finset (ZMod q)) (hunit : ∀ a ∈ T, IsUnit a)
    (hmem : ∀ n, P n → n.Prime ∧ (n : ZMod q) ∈ T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      (x - 1) * candidatePrimeTsum P x <
        (∑ _a ∈ T, (q.totient : ℝ)⁻¹) + δ := by
  classical
  have hclasslim := tendsto_finitePrimeClassMass (q := q) T hunit
  have hδ' : (∑ a ∈ T, (q.totient : ℝ)⁻¹) <
      (∑ a ∈ T, (q.totient : ℝ)⁻¹) + δ := by linarith
  have hev := hclasslim.eventually (Iio_mem_nhds hδ')
  filter_upwards [self_mem_nhdsWithin, hev] with x hx hbound
  have hterm0 (n : ℕ) : 0 ≤ candidatePrimeTerm P x n := by
    dsimp [candidatePrimeTerm]
    split_ifs
    · positivity
    · exact le_rfl
  let G : ℕ → ℝ := fun n => Finset.sum T (fun a => primeResidueTerm a x n)
  have hG : Summable G := by
    exact abelZeroSummableFinsetSum T (fun a n => primeResidueTerm a x n)
      (fun a _ => summable_primeResidueTerm a x hx)
  have hterm (n : ℕ) : candidatePrimeTerm P x n ≤ G n := by
    by_cases hn : P n
    · obtain ⟨hnprime, hclass⟩ := hmem n hn
      let a : ZMod q := n
      have ha : a ∈ T := by simpa [a] using hclass
      have hres : residueClass a n = Real.log n := by
        simp [residueClass, a, ArithmeticFunction.vonMangoldt_apply_prime hnprime]
      have hval : primeResidueTerm a x n = candidatePrimeTerm P x n := by
        simp [candidatePrimeTerm, primeResidueTerm, hn, hnprime, hres]
      have hsingle : primeResidueTerm a x n ≤ G n := by
        exact Finset.single_le_sum
          (f := fun b => primeResidueTerm b x n)
          (fun b hb => by
            dsimp [primeResidueTerm]
            positivity [residueClass_nonneg b n]) ha
      rw [← hval]
      exact hsingle
    · simp only [candidatePrimeTerm, if_neg hn]
      exact Finset.sum_nonneg fun a ha => by
        dsimp [primeResidueTerm]
        positivity [residueClass_nonneg a n]
  have hPsum : Summable (candidatePrimeTerm P x) :=
    hG.of_nonneg_of_le hterm0 hterm
  have htsum := Summable.tsum_le_tsum hterm hPsum hG
  have hswap : (∑' n : ℕ, G n) = ∑ a ∈ T, primeResidueTsum a x := by
    dsimp [G, primeResidueTsum]
    rw [Summable.tsum_finsetSum (fun a ha => summable_primeResidueTerm a x hx)]
  have hmass : (x - 1) * candidatePrimeTsum P x ≤
      ∑ a ∈ T, abelZeroNormalizedPrimeClass a x := by
    calc
      (x - 1) * candidatePrimeTsum P x =
          (x - 1) * ∑' n : ℕ, candidatePrimeTerm P x n := rfl
      _ ≤ (x - 1) * ∑' n : ℕ, G n := by
        exact mul_le_mul_of_nonneg_left htsum (sub_nonneg.mpr hx.le)
      _ = ∑ a ∈ T, abelZeroNormalizedPrimeClass a x := by
        rw [hswap]
        dsimp [abelZeroNormalizedPrimeClass]
        rw [Finset.mul_sum]
  exact lt_of_le_of_lt hmass hbound

/-- The same majorant works when a finite set of indices is excepted from the
residue-class cover. Its contribution vanishes after Abel normalization. -/
theorem eventually_candidatePrimeMass_le_classes_except {P : ℕ → Prop}
    [DecidablePred P] (T : Finset (ZMod q)) (hunit : ∀ a ∈ T, IsUnit a)
    (E : Finset ℕ)
    (hprime : ∀ n, P n → n.Prime)
    (hmem : ∀ n, P n → n ∉ E → (n : ZMod q) ∈ T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      (x - 1) * candidatePrimeTsum P x <
        (∑ _a ∈ T, (q.totient : ℝ)⁻¹) + δ := by
  classical
  have hclasslim := tendsto_finitePrimeClassMass (q := q) T hunit
  let C : ℝ := ∑ n ∈ E, max (Real.log n) 0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hclass : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      ∑ a ∈ T, abelZeroNormalizedPrimeClass a x <
        (∑ _a ∈ T, (q.totient : ℝ)⁻¹) + δ / 2 := by
    have hlim := hclasslim.eventually (Iio_mem_nhds (by linarith :
      (∑ _a ∈ T, (q.totient : ℝ)⁻¹) <
        (∑ _a ∈ T, (q.totient : ℝ)⁻¹) + δ / 2))
    exact hlim
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), (x - 1) * C < δ / 2 := by
    have hlin : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have h := tendsto_id.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ))
      simpa using h.sub_const (1 : ℝ)
    by_cases hC0 : C = 0
    · have hCeq : C = 0 := by simpa using hC0
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [hCeq]
      simp
      linarith
    · have hCpos : 0 < C := by
        rcases lt_or_eq_of_le hC with h | h
        · exact h
        · exact (hC0 h.symm).elim
      have hpos : 0 < δ / (2 * C) := by positivity
      have hnear := hlin.eventually (Iio_mem_nhds hpos)
      filter_upwards [hnear, self_mem_nhdsWithin] with x hx hx1
      have hxpos : 0 ≤ x - 1 := sub_nonneg.mpr hx1.le
      have hmul := mul_lt_mul_of_pos_right hx hCpos
      have hdiv : δ / (2 * C) * C = δ / 2 := by field_simp
      nlinarith
  have hmain : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      (x - 1) * candidatePrimeTsum P x ≤
        (∑ a ∈ T, abelZeroNormalizedPrimeClass a x) + (x - 1) * C := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hterm0 (n : ℕ) : 0 ≤ candidatePrimeTerm P x n := by
      dsimp [candidatePrimeTerm]
      split_ifs <;> positivity
    let G : ℕ → ℝ := fun n => Finset.sum T (fun a => primeResidueTerm a x n)
    let H : ℕ → ℝ := fun n => if n ∈ E then candidatePrimeTerm P x n else 0
    have hG : Summable G := by
      exact abelZeroSummableFinsetSum T (fun a n => primeResidueTerm a x n)
        (fun a _ => summable_primeResidueTerm a x hx)
    have hH : Summable H := by
      apply summable_of_hasFiniteSupport
      have hsub : {n | H n ≠ 0} ⊆ (E : Set ℕ) := by
        intro n hn
        by_cases hnE : n ∈ E
        · exact hnE
        · have hz : H n = 0 := by simp [H, hnE]
          exact (hn hz).elim
      have hfin : {n | H n ≠ 0}.Finite := E.finite_toSet.subset hsub
      exact hfin
    have hterm (n : ℕ) : candidatePrimeTerm P x n ≤ G n + H n := by
      by_cases hnP : P n
      · by_cases hnE : n ∈ E
        · simp [H, hnE]
          have hGnonneg : 0 ≤ G n := Finset.sum_nonneg fun a ha => by
            dsimp [primeResidueTerm]
            positivity [residueClass_nonneg a n]
          linarith
        · have hclass := hmem n hnP hnE
          have hnprime := hprime n hnP
          let a : ZMod q := n
          have ha : a ∈ T := by simpa [a] using hclass
          have hres : residueClass a n = Real.log n := by
            simp [residueClass, a, ArithmeticFunction.vonMangoldt_apply_prime hnprime]
          have hval : primeResidueTerm a x n = candidatePrimeTerm P x n := by
            simp [candidatePrimeTerm, primeResidueTerm, hnP, hnprime, hres]
          have hs : primeResidueTerm a x n ≤ G n := by
            exact Finset.single_le_sum (f := fun b => primeResidueTerm b x n)
              (fun b hb => by
                dsimp [primeResidueTerm]
                positivity [residueClass_nonneg b n]) ha
          rw [← hval]
          simpa [H, hnE] using hs
      · simp [candidatePrimeTerm, hnP]
        apply add_nonneg (Finset.sum_nonneg fun a ha => by
          dsimp [primeResidueTerm]
          positivity [residueClass_nonneg a n])
        dsimp [H]
        split_ifs with hnE
        · exact hterm0 n
        · positivity
    have hPsum : Summable (candidatePrimeTerm P x) :=
      (hG.add hH).of_nonneg_of_le hterm0 hterm
    have htsum := Summable.tsum_le_tsum hterm hPsum (hG.add hH)
    have hswap : (∑' n : ℕ, G n) = ∑ a ∈ T, primeResidueTsum a x := by
      dsimp [G, primeResidueTsum]
      rw [Summable.tsum_finsetSum (fun a ha => summable_primeResidueTerm a x hx)]
    have hHsum : (∑' n : ℕ, H n) = ∑ n ∈ E, candidatePrimeTerm P x n := by
      rw [tsum_eq_sum (s := E) (f := H) (by
        intro n hn
        simp [H, hn])]
      apply Finset.sum_congr rfl
      intro n hn
      simp [H, hn]
    have hHbound : (∑' n : ℕ, H n) ≤ C := by
      rw [hHsum]
      apply Finset.sum_le_sum
      intro n hn
      by_cases hnP : P n
      · have hnprime := hprime n hnP
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnprime.one_le
        have hxpos : (1 : ℝ) < x := hx
        have hxnonneg : 0 ≤ x := le_trans (by norm_num) hxpos.le
        have hpow : 1 ≤ (n : ℝ) ^ x := Real.one_le_rpow hnR hxnonneg
        have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
        have hmax : max (Real.log n) 0 = Real.log n := max_eq_left hlog
        rw [candidatePrimeTerm, if_pos hnP, hmax]
        rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ x)]
        nlinarith [mul_nonneg hlog (sub_nonneg.mpr hpow)]
      · simp [candidatePrimeTerm, hnP]
    have htsum' : (∑' n : ℕ, candidatePrimeTerm P x n) ≤
        (∑' n : ℕ, G n) + (∑' n : ℕ, H n) := by
      calc
        _ ≤ ∑' n : ℕ, (G n + H n) := htsum
        _ = _ := Summable.tsum_add hG hH
    have hmass0 : candidatePrimeTsum P x ≤
        (∑ a ∈ T, primeResidueTsum a x) + C := by
      dsimp [candidatePrimeTsum]
      rw [hswap] at htsum'
      linarith
    have hmass := mul_le_mul_of_nonneg_left hmass0 (sub_nonneg.mpr hx.le)
    calc
      (x - 1) * candidatePrimeTsum P x ≤ (x - 1) *
          ((∑ a ∈ T, primeResidueTsum a x) + C) := hmass
      _ = (∑ a ∈ T, abelZeroNormalizedPrimeClass a x) + (x - 1) * C := by
        simp [abelZeroNormalizedPrimeClass, Finset.mul_sum, mul_add]
  filter_upwards [hclass, hsmall, hmain] with x hx hc hm
  linarith

/-- If a candidate prime family can be covered by unit residue classes of
arbitrarily small total Abel mass, then its normalized Abel mass tends to 0. -/
theorem tendsto_candidatePrimeMass_zero_of_small_class_covers
    {P : ℕ → Prop} [DecidablePred P]
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, ∃ _hq : q ≠ 0,
      ∃ T : Finset (ZMod q),
        (∀ a ∈ T, IsUnit a) ∧
        (∀ n, P n → n.Prime ∧ (n : ZMod q) ∈ T) ∧
        (∑ _a ∈ T, (q.totient : ℝ)⁻¹) < ε) :
    Tendsto (fun x : ℝ => (x - 1) * candidatePrimeTsum P x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hnonneg : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
        0 ≤ (x - 1) * candidatePrimeTsum P x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hsum : 0 ≤ candidatePrimeTsum P x := by
        dsimp [candidatePrimeTsum]
        exact tsum_nonneg fun n => by
          dsimp [candidatePrimeTerm]
          split_ifs <;> positivity
      exact mul_nonneg (sub_nonneg.mpr hx.le) hsum
    filter_upwards [hnonneg] with x hx
    linarith
  · intro a ha
    obtain ⟨q, _hq, T, hunit, hmem, hsmall⟩ := hcover a ha
    let : NeZero q := ⟨_hq⟩
    have hδ : 0 < a - (∑ _a ∈ T, (q.totient : ℝ)⁻¹) := by linarith
    have hb := eventually_candidatePrimeMass_le_classes
      (P := P) T hunit hmem hδ
    filter_upwards [hb] with x hx
    linarith

end MathGacha
