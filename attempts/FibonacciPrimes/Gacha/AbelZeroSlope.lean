import Gacha.AbelZero
import Gacha.EulerAvoid
import Gacha.MultiCRT

open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt

namespace MathGacha

noncomputable def plusPair (k n : ℕ) : Prop := n.Prime ∧ (k * n + 1).Prime

/-- Finite CRT sieve cover for the primes p with k p + 1 prime.
The indices in `E` account for the finitely many cases where a selected sieve
prime itself equals p or 2 j p + 1. -/
theorem exists_plusPair_small_class_cover {k₀ : ℕ} (hk₀ : 0 < k₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ _hq : q ≠ 0, ∃ T : Finset (ZMod q), ∃ E : Finset ℕ,
      (∀ a ∈ T, IsUnit a) ∧
      (∀ n, plusPair k₀ n → n.Prime) ∧
      (∀ n, plusPair k₀ n → n ∉ E → (n : ZMod q) ∈ T) ∧
      (∑ _a ∈ T, (q.totient : ℝ)⁻¹) < ε := by
  classical
  let η : ℝ := min (ε / 2) (1 / 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by
    calc η ≤ ε / 2 := by exact min_le_left _ _
    _ < ε := by linarith
  have hηlt1 : η < 1 := by
    have : η ≤ (1 : ℝ) / 2 := by exact min_le_right _ _
    linarith
  obtain ⟨s, hsp, hfac⟩ := existsEulerAvoidancePrimes hk₀.ne' hη
  have hfac' :
      (∏ r : multiCRTIndex s,
        ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) < η := by
    have hprod (f : ℕ → ℝ) :
        (∏ r : multiCRTIndex s, f r.1) = ∏ r ∈ s, f r := by
      simpa [multiCRTIndex] using (Finset.prod_attach s f)
    have hnum := hprod (fun r => ((r - 2 : ℕ) : ℝ))
    have hden := hprod (fun r => ((r - 1 : ℕ) : ℝ))
    have hdivIdx :
        (∏ r : multiCRTIndex s,
          ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
        (∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ)) /
          (∏ r : multiCRTIndex s, ((r.1 - 1 : ℕ) : ℝ)) := by
      simp only [Finset.prod_div_distrib]
    have hfacEq :
        (∏ r : multiCRTIndex s,
          ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
          ∏ r ∈ s, eulerFactor r := by
      calc
        _ = (∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ)) /
            (∏ r : multiCRTIndex s, ((r.1 - 1 : ℕ) : ℝ)) := hdivIdx
        _ = (∏ r ∈ s, ((r - 2 : ℕ) : ℝ)) /
            (∏ r ∈ s, ((r - 1 : ℕ) : ℝ)) := by rw [hnum, hden]
        _ = ∏ r ∈ s, eulerFactor r := by
          have hratioProd := (Finset.prod_div_distrib (s := s)
            (fun r => ((r - 2 : ℕ) : ℝ))
            (fun r => ((r - 1 : ℕ) : ℝ))).symm
          rw [hratioProd]
          apply Finset.prod_congr rfl
          intro r hr
          have hr2 : 2 ≤ r := by have := (hsp r hr).2.1; omega
          have hr1 : 1 ≤ r := by omega
          simp [eulerFactor, Nat.cast_sub hr2, Nat.cast_sub hr1]
    rw [hfacEq]
    exact hfac
  have hsne : s.Nonempty := by
    by_contra he
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst s
    have : 1 < η := by simpa [eulerFactor] using hfac
    linarith
  let M := multiCRTModulus s
  have hMpos : 0 < M := by
    dsimp [M, multiCRTModulus]
    exact Finset.prod_pos (fun r _ => (hsp r.1 r.2).1.pos)
  let : NeZero M := ⟨hMpos.ne'⟩
  let : ∀ r : multiCRTIndex s, NeZero r.1 := fun r => ⟨(hsp r.1 r.2).1.ne_zero⟩
  let : ∀ r : multiCRTIndex s, Fact r.1.Prime := fun r => ⟨(hsp r.1 r.2).1⟩
  let coeff : ∀ r : multiCRTIndex s, ZMod r.1 := fun _ => (k₀ : ℕ)
  let c : ∀ r : multiCRTIndex s, ZMod r.1 := fun _ => 1
  have hcoeff (r : multiCRTIndex s) : coeff r ≠ 0 := by
    intro hz
    have hdiv : r.1 ∣ k₀ := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [coeff] using hz)
    exact (hsp r.1 r.2).2.2 hdiv
  have hc (r : multiCRTIndex s) : c r ≠ 0 := by simp [c]
  have hpS : ∀ r ∈ s, r.Prime := fun r hr => (hsp r hr).1
  let Good : Finset (ZMod M)ˣ := Finset.univ.filter fun u =>
    ∀ r : multiCRTIndex s,
      coeff r * ((multiCRTCrtUnitEquiv s hpS u) r : ZMod r.1) + c r ≠ 0
  let T : Finset (ZMod M) := Finset.image (fun u : (ZMod M)ˣ => (u : ZMod M)) Good
  have hcount := multiCRTCardCrtAffineAvoiders s hpS coeff c hcoeff hc
  have hTcard : T.card = ∏ r : multiCRTIndex s, (r.1 - 2) := by
    change (Finset.image (fun u : (ZMod M)ˣ => (u : ZMod M)) Good).card = _
    calc
      _ = Good.card := Finset.card_image_of_injective Good (by
        intro u v huv
        exact Units.ext huv)
      _ = Fintype.card
          {u : (ZMod M)ˣ // ∀ r : multiCRTIndex s,
            coeff r * ((multiCRTCrtUnitEquiv s hpS u) r : ZMod r.1) + c r ≠ 0} := by
        simp [Good, Fintype.card_subtype]
      _ = _ := hcount
  have hratio := multiCRTGoodResidueFinsetRatio s hpS
  have hcardcast : (T.card : ℝ) =
      ∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ) := by
    rw [hTcard]
    norm_cast
  have hmassratio :
      (∏ r : multiCRTIndex s,
        ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
      (T.card : ℝ) / (M.totient : ℝ) := by
    simpa [M, hcardcast] using hratio
  have hTmass : (∑ _a ∈ T, (M.totient : ℝ)⁻¹) < ε := by
    have hsum : (∑ _a ∈ T, (M.totient : ℝ)⁻¹) =
        (T.card : ℝ) / (M.totient : ℝ) := by
      simp [div_eq_mul_inv]
    rw [hsum, ← hmassratio]
    exact lt_trans hfac' hηε
  refine ⟨M, hMpos.ne', T, Finset.range (M + 2), ?_, ?_, ?_, hTmass⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
    exact ⟨u, rfl⟩
  · intro n hn
    exact hn.1
  · intro n hn hnE
    have hcop : n.Coprime M := by
      rw [Nat.coprime_prod_right_iff]
      intro r hr
      apply ((hsp r.1 r.2).1.coprime_iff_not_dvd.mpr ?_).symm
      intro hdiv
      have hrprime := (hsp r.1 r.2).1
      have heq : r.1 = n := by
        rcases (Nat.dvd_prime hn.1).mp hdiv with h | h
        · exact False.elim (hrprime.ne_one h)
        · exact h
      have hrdiv : r.1 ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ r)
      have hrM : r.1 ≤ M := Nat.le_of_dvd (by omega) hrdiv
      have hnsmall : n < M + 2 := by omega
      exact hnE (Finset.mem_range.mpr hnsmall)
    let u : (ZMod M)ˣ := ZMod.unitOfCoprime n hcop
    have huGood : u ∈ Good := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro r
      have hcoord := multiCRTCrtUnitEquivNatCast s hpS n hcop r
      have hcoord' : ((multiCRTCrtUnitEquiv s hpS u) r : ZMod r.1) =
          (n : ZMod r.1) := by simpa [u] using hcoord
      have hrprime := (hsp r.1 r.2).1
      have hrdiv : r.1 ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ r)
      have hrM : r.1 ≤ M := Nat.le_of_dvd (by omega) hrdiv
      have hnotdiv : ¬ r.1 ∣ k₀ * n + 1 := by
        intro hd
        have heq : r.1 = k₀ * n + 1 := by
          rcases (Nat.dvd_prime hn.2).mp hd with h | h
          · exact False.elim (hrprime.ne_one h)
          · exact h
        have hnle : n ≤ k₀ * n + 1 := by nlinarith [hk₀, hn.1.two_le]
        have hnsmall : n < M + 2 := by omega
        exact hnE (Finset.mem_range.mpr hnsmall)
      intro hz
      have hzero : ((k₀ * n + 1 : ℕ) : ZMod r.1) = 0 := by
        have hz' := hz
        rw [hcoord'] at hz'
        dsimp [coeff, c] at hz'
        change ((k₀ : ℕ) : ZMod r.1) * (n : ZMod r.1) + 1 = 0 at hz'
        convert hz' using 1; push_cast; ring
      exact hnotdiv ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
    apply Finset.mem_image.mpr
    refine ⟨u, huGood, ?_⟩
    simp [u, ZMod.coe_unitOfCoprime]

noncomputable def minusPair (k n : ℕ) : Prop := n.Prime ∧ (k * n - 1).Prime
theorem exists_minusPair_small_class_cover {k₀ : ℕ} (hk₀ : 0 < k₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ _hq : q ≠ 0, ∃ T : Finset (ZMod q), ∃ E : Finset ℕ,
      (∀ a ∈ T, IsUnit a) ∧
      (∀ n, minusPair k₀ n → n.Prime) ∧
      (∀ n, minusPair k₀ n → n ∉ E → (n : ZMod q) ∈ T) ∧
      (∑ _a ∈ T, (q.totient : ℝ)⁻¹) < ε := by
  classical
  let η : ℝ := min (ε / 2) (1 / 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by
    calc η ≤ ε / 2 := by exact min_le_left _ _
    _ < ε := by linarith
  have hηlt1 : η < 1 := by
    have : η ≤ (1 : ℝ) / 2 := by exact min_le_right _ _
    linarith
  obtain ⟨s, hsp, hfac⟩ := existsEulerAvoidancePrimes hk₀.ne' hη
  have hfac' :
      (∏ r : multiCRTIndex s,
        ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) < η := by
    have hprod (f : ℕ → ℝ) :
        (∏ r : multiCRTIndex s, f r.1) = ∏ r ∈ s, f r := by
      simpa [multiCRTIndex] using (Finset.prod_attach s f)
    have hnum := hprod (fun r => ((r - 2 : ℕ) : ℝ))
    have hden := hprod (fun r => ((r - 1 : ℕ) : ℝ))
    have hdivIdx :
        (∏ r : multiCRTIndex s,
          ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
        (∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ)) /
          (∏ r : multiCRTIndex s, ((r.1 - 1 : ℕ) : ℝ)) := by
      simp only [Finset.prod_div_distrib]
    have hfacEq :
        (∏ r : multiCRTIndex s,
          ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
          ∏ r ∈ s, eulerFactor r := by
      calc
        _ = (∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ)) /
            (∏ r : multiCRTIndex s, ((r.1 - 1 : ℕ) : ℝ)) := hdivIdx
        _ = (∏ r ∈ s, ((r - 2 : ℕ) : ℝ)) /
            (∏ r ∈ s, ((r - 1 : ℕ) : ℝ)) := by rw [hnum, hden]
        _ = ∏ r ∈ s, eulerFactor r := by
          have hratioProd := (Finset.prod_div_distrib (s := s)
            (fun r => ((r - 2 : ℕ) : ℝ))
            (fun r => ((r - 1 : ℕ) : ℝ))).symm
          rw [hratioProd]
          apply Finset.prod_congr rfl
          intro r hr
          have hr2 : 2 ≤ r := by have := (hsp r hr).2.1; omega
          have hr1 : 1 ≤ r := by omega
          simp [eulerFactor, Nat.cast_sub hr2, Nat.cast_sub hr1]
    rw [hfacEq]
    exact hfac
  have hsne : s.Nonempty := by
    by_contra he
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst s
    have : 1 < η := by simpa [eulerFactor] using hfac
    linarith
  let M := multiCRTModulus s
  have hMpos : 0 < M := by
    dsimp [M, multiCRTModulus]
    exact Finset.prod_pos (fun r _ => (hsp r.1 r.2).1.pos)
  let : NeZero M := ⟨hMpos.ne'⟩
  let : ∀ r : multiCRTIndex s, NeZero r.1 := fun r => ⟨(hsp r.1 r.2).1.ne_zero⟩
  let : ∀ r : multiCRTIndex s, Fact r.1.Prime := fun r => ⟨(hsp r.1 r.2).1⟩
  let coeff : ∀ r : multiCRTIndex s, ZMod r.1 := fun _ => (k₀ : ℕ)
  let c : ∀ r : multiCRTIndex s, ZMod r.1 := fun _ => -1
  have hcoeff (r : multiCRTIndex s) : coeff r ≠ 0 := by
    intro hz
    have hdiv : r.1 ∣ k₀ := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa [coeff] using hz)
    exact (hsp r.1 r.2).2.2 hdiv
  have hc (r : multiCRTIndex s) : c r ≠ 0 := by simp [c]
  have hpS : ∀ r ∈ s, r.Prime := fun r hr => (hsp r hr).1
  let Good : Finset (ZMod M)ˣ := Finset.univ.filter fun u =>
    ∀ r : multiCRTIndex s,
      coeff r * ((multiCRTCrtUnitEquiv s hpS u) r : ZMod r.1) + c r ≠ 0
  let T : Finset (ZMod M) := Finset.image (fun u : (ZMod M)ˣ => (u : ZMod M)) Good
  have hcount := multiCRTCardCrtAffineAvoiders s hpS coeff c hcoeff hc
  have hTcard : T.card = ∏ r : multiCRTIndex s, (r.1 - 2) := by
    change (Finset.image (fun u : (ZMod M)ˣ => (u : ZMod M)) Good).card = _
    calc
      _ = Good.card := Finset.card_image_of_injective Good (by
        intro u v huv
        exact Units.ext huv)
      _ = Fintype.card
          {u : (ZMod M)ˣ // ∀ r : multiCRTIndex s,
            coeff r * ((multiCRTCrtUnitEquiv s hpS u) r : ZMod r.1) + c r ≠ 0} := by
        simp [Good, Fintype.card_subtype]
      _ = _ := hcount
  have hratio := multiCRTGoodResidueFinsetRatio s hpS
  have hcardcast : (T.card : ℝ) =
      ∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ) := by
    rw [hTcard]
    norm_cast
  have hmassratio :
      (∏ r : multiCRTIndex s,
        ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
      (T.card : ℝ) / (M.totient : ℝ) := by
    simpa [M, hcardcast] using hratio
  have hTmass : (∑ _a ∈ T, (M.totient : ℝ)⁻¹) < ε := by
    have hsum : (∑ _a ∈ T, (M.totient : ℝ)⁻¹) =
        (T.card : ℝ) / (M.totient : ℝ) := by
      simp [div_eq_mul_inv]
    rw [hsum, ← hmassratio]
    exact lt_trans hfac' hηε
  refine ⟨M, hMpos.ne', T, Finset.range (M + 2), ?_, ?_, ?_, hTmass⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
    exact ⟨u, rfl⟩
  · intro n hn
    exact hn.1
  · intro n hn hnE
    have hcop : n.Coprime M := by
      rw [Nat.coprime_prod_right_iff]
      intro r hr
      apply ((hsp r.1 r.2).1.coprime_iff_not_dvd.mpr ?_).symm
      intro hdiv
      have hrprime := (hsp r.1 r.2).1
      have heq : r.1 = n := by
        rcases (Nat.dvd_prime hn.1).mp hdiv with h | h
        · exact False.elim (hrprime.ne_one h)
        · exact h
      have hrdiv : r.1 ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ r)
      have hrM : r.1 ≤ M := Nat.le_of_dvd (by omega) hrdiv
      have hnsmall : n < M + 2 := by omega
      exact hnE (Finset.mem_range.mpr hnsmall)
    let u : (ZMod M)ˣ := ZMod.unitOfCoprime n hcop
    have huGood : u ∈ Good := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro r
      have hcoord := multiCRTCrtUnitEquivNatCast s hpS n hcop r
      have hcoord' : ((multiCRTCrtUnitEquiv s hpS u) r : ZMod r.1) =
          (n : ZMod r.1) := by simpa [u] using hcoord
      have hrprime := (hsp r.1 r.2).1
      have hrdiv : r.1 ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ r)
      have hrM : r.1 ≤ M := Nat.le_of_dvd (by omega) hrdiv
      have hnotdiv : ¬ r.1 ∣ k₀ * n - 1 := by
        intro hd
        have heq : r.1 = k₀ * n - 1 := by
          rcases (Nat.dvd_prime hn.2).mp hd with h | h
          · exact False.elim (hrprime.ne_one h)
          · exact h
        have hnle : n ≤ k₀ * n := by nlinarith [hk₀, hn.1.two_le]
        have hnsmall : n < M + 2 := by omega
        exact hnE (Finset.mem_range.mpr hnsmall)
      intro hz
      have hkn : 1 ≤ k₀ * n := by nlinarith [hk₀, hn.1.two_le]
      have hzero : ((k₀ * n - 1 : ℕ) : ZMod r.1) = 0 := by
        have hz' := hz
        rw [hcoord'] at hz'
        dsimp [coeff, c] at hz'
        change ((k₀ : ℕ) : ZMod r.1) * (n : ZMod r.1) + (-1) = 0 at hz'
        rw [Nat.cast_sub hkn]
        convert hz' using 1; push_cast; ring
      exact hnotdiv ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
    apply Finset.mem_image.mpr
    refine ⟨u, huGood, ?_⟩
    simp [u, ZMod.coe_unitOfCoprime]

/-- Finite-exception version of the small-class criterion. -/
theorem tendsto_candidatePrimeMass_zero_of_small_class_covers_except
    {P : ℕ → Prop} [DecidablePred P]
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, ∃ _hq : q ≠ 0,
      ∃ T : Finset (ZMod q), ∃ E : Finset ℕ,
        (∀ a ∈ T, IsUnit a) ∧
        (∀ n, P n → n.Prime) ∧
        (∀ n, P n → n ∉ E → (n : ZMod q) ∈ T) ∧
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
    obtain ⟨q, _hq, T, E, hunit, hprime, hmem, hsmall⟩ := hcover a ha
    let : NeZero q := ⟨_hq⟩
    have hδ : 0 < a - (∑ _a ∈ T, (q.totient : ℝ)⁻¹) := by linarith
    have hb := eventually_candidatePrimeMass_le_classes_except
      (P := P) T hunit E hprime hmem hδ
    filter_upwards [hb] with x hx
    linarith

/-- For every fixed positive slope, the primes p for which 2 j p + 1 is
prime have zero normalized Abel mass among the primes. -/
theorem tendsto_plusPair_abel_zero {k₀ : ℕ} (hk₀ : 0 < k₀)
    [DecidablePred (plusPair k₀)] :
    Tendsto (fun x : ℝ => (x - 1) * candidatePrimeTsum (plusPair k₀) x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  classical
  apply tendsto_candidatePrimeMass_zero_of_small_class_covers_except
  intro ε hε
  obtain ⟨q, hq, T, E, hunit, hprime, hmem, hsmall⟩ :=
    exists_plusPair_small_class_cover hk₀ hε
  exact ⟨q, hq, T, E, hunit, hprime, hmem, hsmall⟩

/-- For every fixed positive slope, the primes p for which k p - 1 is
prime have zero normalized Abel mass among the primes. -/
theorem tendsto_minusPair_abel_zero {k₀ : ℕ} (hk₀ : 0 < k₀)
    [DecidablePred (minusPair k₀)] :
    Tendsto (fun x : ℝ => (x - 1) * candidatePrimeTsum (minusPair k₀) x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  classical
  apply tendsto_candidatePrimeMass_zero_of_small_class_covers_except
  intro ε hε
  obtain ⟨q, hq, T, E, hunit, hprime, hmem, hsmall⟩ :=
    exists_minusPair_small_class_cover hk₀ hε
  exact ⟨q, hq, T, E, hunit, hprime, hmem, hsmall⟩

end MathGacha
