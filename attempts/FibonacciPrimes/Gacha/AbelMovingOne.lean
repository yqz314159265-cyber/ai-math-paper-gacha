import Gacha.AbelSieve

open Filter Topology
open LSeries ArithmeticFunction ArithmeticFunction.vonMangoldt

namespace MathGacha

/-- The prime-index weight of indices whose least Fibonacci factor is below the
moving cutoff. -/
noncomputable def badFibIndexTerm (K : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (Nat.fib n).minFac ≤ K * n then
    Real.log n / (n : ℝ) ^ x else 0

noncomputable def badFibIndexTsum (K : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, badFibIndexTerm K x n

/-- Pair weights arising from a progression multiplier k and either sign. -/
noncomputable def linearPrimePairTerm (k : ℕ) (plus : Bool) (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (if plus then k * n + 1 else k * n - 1).Prime then
    Real.log n / (n : ℝ) ^ x else 0

noncomputable def linearPrimePairTsum (k : ℕ) (plus : Bool) (x : ℝ) : ℝ :=
  ∑' n : ℕ, linearPrimePairTerm k plus x n

noncomputable def finiteAbelSum (E : Finset ℕ) (f : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ E, f n / (n : ℝ) ^ x

theorem tendsto_scaled_finiteAbelSum (E : Finset ℕ) (f : ℕ → ℝ)
    (hE : ∀ n ∈ E, n ≠ 0) :
    Tendsto (fun x : ℝ => (x - 1) * finiteAbelSum E f x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  classical
  have hlin : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hid : Tendsto id (𝓝[>] (1 : ℝ)) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.sub_const (1 : ℝ)
  have hterm (n : ℕ) (hn : n ≠ 0) :
      Tendsto (fun x : ℝ => (x - 1) * (f n / (n : ℝ) ^ x))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcont : ContinuousAt (fun x : ℝ => (n : ℝ) ^ x) 1 :=
      Real.continuousAt_const_rpow hnpos.ne'
    have hden : (n : ℝ) ^ (1 : ℝ) ≠ 0 := by positivity
    have hquot : Tendsto (fun x : ℝ => f n / (n : ℝ) ^ x)
        (𝓝[>] (1 : ℝ)) (𝓝 (f n / (n : ℝ) ^ (1 : ℝ))) :=
      (continuousAt_const.div hcont hden).tendsto.mono_left nhdsWithin_le_nhds
    have := hlin.mul hquot
    simpa using this
  have hsum : Tendsto (fun x : ℝ =>
      ∑ n ∈ E, (x - 1) * (f n / (n : ℝ) ^ x)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using tendsto_finsetSum E (fun n hn => hterm n (hE n hn))
  have heq : (fun x : ℝ => (x - 1) * finiteAbelSum E f x) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x => ∑ n ∈ E, (x - 1) * (f n / (n : ℝ) ^ x)) := by
    filter_upwards with x
    simp [finiteAbelSum, Finset.mul_sum]
  exact hsum.congr' heq.symm

/-- Every bad index above five is represented by one of the finitely many
linear prime pairs. The witness is the least prime divisor of `fib n`. -/
theorem badFibIndex_progression_cover (K n : ℕ) (hn : n.Prime) (hn5 : 5 < n)
    (hbad : (Nat.fib n).minFac ≤ K * n) :
    ∃ k ∈ Finset.Icc 1 K, (k * n + 1).Prime ∨ (k * n - 1).Prime := by
  have hfib : Nat.fib n ≠ 1 := by
    have hmono : Nat.fib 3 ≤ Nat.fib n := Nat.fib_mono (by omega)
    exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < Nat.fib 3) hmono)
  let q := (Nat.fib n).minFac
  have hq : q.Prime := Nat.minFac_prime hfib
  have hdiv : q ∣ Nat.fib n := Nat.minFac_dvd _
  obtain ⟨k, hk1, hkK, hform⟩ := divisorProgressionUpTo hn hn5 hq hdiv hbad
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkK⟩, ?_⟩
  rcases hform with hp | hm
  · left
    rw [← hp]
    exact hq
  · right
    rw [← hm]
    exact hq

theorem badFibIndexTerm_le_progressionTerm (K : ℕ) (x : ℝ) (n : ℕ)
    (hcover : n.Prime → 5 < n → (Nat.fib n).minFac ≤ K * n →
      ∃ k ∈ Finset.Icc 1 K, (k * n + 1).Prime ∨ (k * n - 1).Prime) :
    badFibIndexTerm K x n ≤
      (∑ k ∈ Finset.Icc 1 K,
        (linearPrimePairTerm k true x n + linearPrimePairTerm k false x n)) +
      (if n < 6 ∧ n.Prime then Real.log n / (n : ℝ) ^ x else 0) := by
  classical
  by_cases hn : n.Prime ∧ (Nat.fib n).minFac ≤ K * n
  · rcases hn with ⟨hp, hbad⟩
    have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hp.two_le
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hden : 0 < (n : ℝ) ^ x := by
      exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
    have hpairnonneg (j : ℕ) (s : Bool) : 0 ≤ linearPrimePairTerm j s x n := by
      by_cases hc : n.Prime ∧ (if s then j * n + 1 else j * n - 1).Prime
      · simp [linearPrimePairTerm, hc]
        exact div_nonneg hlog hden.le
      · simp [linearPrimePairTerm, hc]
    by_cases hn6 : n < 6
    · simp [badFibIndexTerm, hp, hbad, hn6]
      have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 K,
          (linearPrimePairTerm k true x n + linearPrimePairTerm k false x n) :=
        Finset.sum_nonneg fun k _ => add_nonneg (hpairnonneg k true) (hpairnonneg k false)
      linarith
    · have hn5 : 5 < n := by omega
      obtain ⟨k, hk, hsign⟩ := hcover hp hn5 hbad
      have hpairBound : Real.log n / (n : ℝ) ^ x ≤
          linearPrimePairTerm k true x n + linearPrimePairTerm k false x n := by
        rcases hsign with hplus | hminus
        · have hmain : linearPrimePairTerm k true x n = Real.log n / (n : ℝ) ^ x := by
            simp [linearPrimePairTerm, hp, hplus]
          rw [hmain]
          exact le_add_of_nonneg_right (hpairnonneg k false)
        · have hmain : linearPrimePairTerm k false x n = Real.log n / (n : ℝ) ^ x := by
            simp [linearPrimePairTerm, hp, hminus]
          rw [hmain]
          exact le_add_of_nonneg_left (hpairnonneg k true)
      have hnonneg (j : ℕ) (_ : j ∈ Finset.Icc 1 K) :
          0 ≤ linearPrimePairTerm j true x n + linearPrimePairTerm j false x n := by
        exact add_nonneg (hpairnonneg j true) (hpairnonneg j false)
      have hle := Finset.single_le_sum hnonneg hk
      simp [badFibIndexTerm, hp, hbad, hn6]
      exact hpairBound.trans hle
  · have hpairnonneg (j : ℕ) (s : Bool) : 0 ≤ linearPrimePairTerm j s x n := by
      by_cases hp : n.Prime
      · have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hp.two_le
        have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
        have hden : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
        by_cases hc : (if s then j * n + 1 else j * n - 1).Prime
        · simp [linearPrimePairTerm, hp, hc]
          exact div_nonneg hlog hden.le
        · simp [linearPrimePairTerm, hp, hc]
      · simp [linearPrimePairTerm, hp]
    have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 K,
        (linearPrimePairTerm k true x n + linearPrimePairTerm k false x n) :=
      Finset.sum_nonneg fun k _ => add_nonneg (hpairnonneg k true) (hpairnonneg k false)
    have hcorr : 0 ≤ (if n < 6 ∧ n.Prime then Real.log n / (n : ℝ) ^ x else 0) := by
      by_cases hp : n.Prime
      · have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hp.two_le
        have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
        have hden : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
        split_ifs <;> positivity
      · simp [hp]
    simp [badFibIndexTerm, hn]
    exact add_nonneg hsum hcorr

theorem tendsto_scaled_finiteLinearPairSum (K : ℕ)
    (hpair : ∀ k ∈ Finset.Icc 1 K, ∀ s : Bool,
      Tendsto (fun x : ℝ => (x - 1) * linearPrimePairTsum k s x)
        (𝓝[>] (1 : ℝ)) (𝓝 0)) :
    Tendsto (fun x : ℝ => (x - 1) *
      (∑ k ∈ Finset.Icc 1 K,
        (linearPrimePairTsum k true x + linearPrimePairTsum k false x)))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.Icc 1 K)
    (fun k hk => (hpair k hk true).add (hpair k hk false))
  have hsum0 : Tendsto
      (fun x : ℝ => ∑ k ∈ Finset.Icc 1 K,
        ((x - 1) * linearPrimePairTsum k true x +
         (x - 1) * linearPrimePairTsum k false x))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using hsum
  have heq : (fun x : ℝ => (x - 1) *
      (∑ k ∈ Finset.Icc 1 K,
        (linearPrimePairTsum k true x + linearPrimePairTsum k false x))) =ᶠ[
          𝓝[>] (1 : ℝ)]
      (fun x => ∑ k ∈ Finset.Icc 1 K,
        ((x - 1) * linearPrimePairTsum k true x +
         (x - 1) * linearPrimePairTsum k false x)) := by
    filter_upwards with x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_add]
  exact hsum0.congr' heq.symm

noncomputable def exceptionTerm (x : ℝ) (n : ℕ) : ℝ :=
  if n < 6 ∧ n.Prime then Real.log n / (n : ℝ) ^ x else 0

noncomputable def progressionMajorantTerm (K : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 K,
    (linearPrimePairTerm k true x n + linearPrimePairTerm k false x n)) +
    exceptionTerm x n

noncomputable def smallExceptionTsum (x : ℝ) : ℝ :=
  finiteAbelSum (Finset.Icc 1 5) (fun n => if n.Prime then Real.log n else 0) x

theorem summable_finiteSum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hnot ih =>
      have ha := hf a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, Summable (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hrest := ih hs
      simpa [Finset.sum_insert hnot] using ha.add hrest

theorem totalPrimeTerm_eq_log (x : ℝ) {n : ℕ} (hn : n.Prime) :
    primeResidueTerm (0 : ZMod 1) x n = Real.log n / (n : ℝ) ^ x := by
  have hcast : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  have hres : residueClass (0 : ZMod 1) n = vonMangoldt n := by
    simp [residueClass, hcast]
  simp [primeResidueTerm, hn, hres, vonMangoldt_apply_prime hn]

theorem linearPrimePairTerm_le_total (k : ℕ) (s : Bool) (x : ℝ) (n : ℕ) :
    linearPrimePairTerm k s x n ≤ primeResidueTerm (0 : ZMod 1) x n := by
  by_cases hn : n.Prime
  · by_cases hpair : (if s then k * n + 1 else k * n - 1).Prime
    · rw [linearPrimePairTerm, if_pos ⟨hn, hpair⟩, totalPrimeTerm_eq_log x hn]
    · simp only [linearPrimePairTerm, hn, hpair, and_false, ↓reduceIte]
      have hnonneg : 0 ≤ primeResidueTerm (0 : ZMod 1) x n := by
        dsimp [primeResidueTerm]
        positivity [residueClass_nonneg (0 : ZMod 1) n]
      exact hnonneg
  · rw [linearPrimePairTerm, if_neg (by exact fun h => hn h.1), primeResidueTerm]
    simp [hn]

theorem linearPrimePairTerm_nonneg (k : ℕ) (s : Bool) (x : ℝ) (n : ℕ) :
    0 ≤ linearPrimePairTerm k s x n := by
  by_cases hp : n.Prime
  · have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hp.two_le
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hden : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
    by_cases hs : (if s then k * n + 1 else k * n - 1).Prime
    · simp [linearPrimePairTerm, hp, hs]
      exact div_nonneg hlog hden.le
    · simp [linearPrimePairTerm, hp, hs]
  · simp [linearPrimePairTerm, hp]

theorem summable_linearPrimePairTerm (k : ℕ) (s : Bool) (x : ℝ) (hx : 1 < x) :
    Summable (linearPrimePairTerm k s x) := by
  have htotal := summable_primeResidueTerm (0 : ZMod 1) x hx
  exact htotal.of_nonneg_of_le
    (fun n => linearPrimePairTerm_nonneg k s x n)
    (fun n => linearPrimePairTerm_le_total k s x n)

theorem summable_exceptionTerm (x : ℝ) : Summable (exceptionTerm x) := by
  apply summable_of_ne_finset_zero (s := Finset.range 6)
  intro n hn
  have hn6 : ¬ n < 6 := by simpa using hn
  simp [exceptionTerm, hn6]

theorem progressionMajorantTerm_nonneg (K : ℕ) (x : ℝ) (n : ℕ) :
    0 ≤ progressionMajorantTerm K x n := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro k hk
    exact add_nonneg (linearPrimePairTerm_nonneg k true x n)
      (linearPrimePairTerm_nonneg k false x n)
  · by_cases hp : n.Prime
    · have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hp.two_le
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      have hden : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
      simp [exceptionTerm]
      split_ifs <;> positivity
    · simp [exceptionTerm, hp]

theorem summable_progressionMajorantTerm (K : ℕ) (x : ℝ) (hx : 1 < x) :
    Summable (progressionMajorantTerm K x) := by
  have hpair (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      Summable (fun n => linearPrimePairTerm k true x n +
        linearPrimePairTerm k false x n) :=
    (summable_linearPrimePairTerm k true x hx).add
      (summable_linearPrimePairTerm k false x hx)
  have hsum := summable_finiteSum (Finset.Icc 1 K)
    (fun k n => linearPrimePairTerm k true x n + linearPrimePairTerm k false x n) hpair
  exact hsum.add (summable_exceptionTerm x)

theorem badFibIndexTerm_nonneg (K : ℕ) (x : ℝ) (n : ℕ) :
    0 ≤ badFibIndexTerm K x n := by
  by_cases hp : n.Prime
  · have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hp.two_le
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hden : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) x
    simp [badFibIndexTerm, hp]
    split_ifs <;> positivity
  · simp [badFibIndexTerm, hp]

theorem badFibIndexTerm_le_progressionMajorantTerm (K : ℕ) (x : ℝ) (n : ℕ) :
    badFibIndexTerm K x n ≤ progressionMajorantTerm K x n := by
  exact badFibIndexTerm_le_progressionTerm K x n
    (fun hp hn5 hbad => badFibIndex_progression_cover K n hp hn5 hbad)

theorem summable_badFibIndexTerm (K : ℕ) (x : ℝ) (hx : 1 < x) :
    Summable (badFibIndexTerm K x) := by
  have hmaj := summable_progressionMajorantTerm K x hx
  exact hmaj.of_nonneg_of_le
    (fun n => badFibIndexTerm_nonneg K x n)
    (fun n => badFibIndexTerm_le_progressionMajorantTerm K x n)

theorem badFibIndexTsum_le_progressionMajorant (K : ℕ) (x : ℝ) (hx : 1 < x) :
    badFibIndexTsum K x ≤ ∑' n : ℕ, progressionMajorantTerm K x n := by
  exact Summable.tsum_le_tsum
    (fun n => badFibIndexTerm_le_progressionMajorantTerm K x n)
    (summable_badFibIndexTerm K x hx)
    (summable_progressionMajorantTerm K x hx)

theorem exceptionTsum_eq_smallExceptionTsum (x : ℝ) :
    (∑' n : ℕ, exceptionTerm x n) = smallExceptionTsum x := by
  have hzero : ∀ n ∉ Finset.Icc 1 5, exceptionTerm x n = 0 := by
    intro n hn
    by_cases h0 : n = 0
    · subst n
      simp [exceptionTerm]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
      have hn5 : 5 < n := by
        by_contra h
        have hnmem : n ∈ Finset.Icc 1 5 := Finset.mem_Icc.mpr ⟨hn1, by omega⟩
        exact hn hnmem
      simp [exceptionTerm, not_lt.mpr (by omega : 6 ≤ n)]
  rw [tsum_eq_sum hzero]
  simp only [smallExceptionTsum, finiteAbelSum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn6 : n < 6 := by
    have := Finset.mem_Icc.mp hn
    omega
  by_cases hp : n.Prime <;> simp [exceptionTerm, hp, hn6]

theorem tsum_progressionMajorant_eq (K : ℕ) (x : ℝ) (hx : 1 < x) :
    (∑' n : ℕ, progressionMajorantTerm K x n) =
      (∑ k ∈ Finset.Icc 1 K,
        (linearPrimePairTsum k true x + linearPrimePairTsum k false x)) +
        smallExceptionTsum x := by
  let P : ℕ → ℕ → ℝ := fun k n =>
    linearPrimePairTerm k true x n + linearPrimePairTerm k false x n
  have hpair (k : ℕ) (hk : k ∈ Finset.Icc 1 K) : Summable (P k) := by
    exact (summable_linearPrimePairTerm k true x hx).add
      (summable_linearPrimePairTerm k false x hx)
  have hfinite : Summable (fun n => ∑ k ∈ Finset.Icc 1 K, P k n) :=
    summable_finiteSum (Finset.Icc 1 K) P hpair
  have hex : Summable (exceptionTerm x) := summable_exceptionTerm x
  rw [show progressionMajorantTerm K x =
      (fun n => (∑ k ∈ Finset.Icc 1 K, P k n) + exceptionTerm x n) by
        funext n
        rfl]
  rw [Summable.tsum_add hfinite hex, Summable.tsum_finsetSum hpair]
  have hpairEq : ∀ k ∈ Finset.Icc 1 K,
      (∑' n : ℕ, P k n) =
        linearPrimePairTsum k true x + linearPrimePairTsum k false x := by
    intro k hk
    dsimp [P]
    exact Summable.tsum_add (summable_linearPrimePairTerm k true x hx)
      (summable_linearPrimePairTerm k false x hx)
  rw [exceptionTsum_eq_smallExceptionTsum]
  congr 1
  exact Finset.sum_congr rfl hpairEq

theorem tendsto_scaled_badFibIndexTsum (K : ℕ)
    (hpair : ∀ k ∈ Finset.Icc 1 K, ∀ s : Bool,
      Tendsto (fun x : ℝ => (x - 1) * linearPrimePairTsum k s x)
        (𝓝[>] (1 : ℝ)) (𝓝 0)) :
    Tendsto (fun x : ℝ => (x - 1) * badFibIndexTsum K x)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hpairs := tendsto_scaled_finiteLinearPairSum K hpair
  have hE : ∀ n ∈ Finset.Icc 1 5, n ≠ 0 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    omega
  have hex := tendsto_scaled_finiteAbelSum (Finset.Icc 1 5)
    (fun n => if n.Prime then Real.log n else 0) hE
  have hscale : Tendsto
      (fun x : ℝ => (x - 1) *
        ((∑ k ∈ Finset.Icc 1 K,
          (linearPrimePairTsum k true x + linearPrimePairTsum k false x)) +
          smallExceptionTsum x))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa [smallExceptionTsum, mul_add] using hpairs.add hex
  have hmajorant : Tendsto
      (fun x : ℝ => (x - 1) * (∑' n : ℕ, progressionMajorantTerm K x n))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have heq : (fun x : ℝ => (x - 1) *
        (∑' n : ℕ, progressionMajorantTerm K x n)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun x => (x - 1) *
          ((∑ k ∈ Finset.Icc 1 K,
            (linearPrimePairTsum k true x + linearPrimePairTsum k false x)) +
            smallExceptionTsum x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [tsum_progressionMajorant_eq K x hx]
    exact hscale.congr' heq.symm
  let F : ℝ → ℝ := fun x =>
    if 1 < x then (x - 1) * badFibIndexTsum K x else 0
  let G : ℝ → ℝ := fun x =>
    if 1 < x then (x - 1) * (∑' n : ℕ, progressionMajorantTerm K x n) else 0
  have hFnonneg : ∀ x, 0 ≤ F x := by
    intro x
    by_cases hx : 1 < x
    · simp only [F, if_pos hx]
      exact mul_nonneg (sub_nonneg.mpr hx.le)
        (tsum_nonneg (fun n => badFibIndexTerm_nonneg K x n))
    · simp [F, hx]
  have hFG : ∀ x, F x ≤ G x := by
    intro x
    by_cases hx : 1 < x
    · simp only [F, G, if_pos hx]
      exact mul_le_mul_of_nonneg_left (badFibIndexTsum_le_progressionMajorant K x hx)
        (sub_nonneg.mpr hx.le)
    · simp [F, G, hx]
  have hG : Tendsto G (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have heq : G =ᶠ[𝓝[>] (1 : ℝ)]
        (fun x => (x - 1) * (∑' n : ℕ, progressionMajorantTerm K x n)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 1 < x := by simpa using hx
      simp [G, hx']
    exact hmajorant.congr' heq.symm
  have hF := squeeze_zero hFnonneg hFG hG
  have heqF : F =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x => (x - 1) * badFibIndexTsum K x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < x := by simpa using hx
    simp [F, hx']
  exact hF.congr' heqF

theorem sieved_add_bad_term_eq_total (K : ℕ) (x : ℝ) (n : ℕ) :
    sievedTerm K x n + badFibIndexTerm K x n =
      primeResidueTerm (0 : ZMod 1) x n := by
  by_cases hn : n.Prime
  · have htotal := totalPrimeTerm_eq_log x hn
    by_cases hs : K * n < (Nat.fib n).minFac
    · simp [sievedTerm, badFibIndexTerm, hn, hs, htotal]
    · have hb : (Nat.fib n).minFac ≤ K * n := le_of_not_gt hs
      simp [sievedTerm, badFibIndexTerm, hn, hs, hb, htotal]
  · simp [sievedTerm, badFibIndexTerm, primeResidueTerm, hn]

theorem summable_sievedTerm (K : ℕ) (x : ℝ) (hx : 1 < x) :
    Summable (sievedTerm K x) := by
  have hall := summable_primeResidueTerm (0 : ZMod 1) x hx
  have hnonneg (n : ℕ) : 0 ≤ sievedTerm K x n := by
    dsimp [sievedTerm]
    split_ifs <;> positivity
  have hle (n : ℕ) : sievedTerm K x n ≤ primeResidueTerm (0 : ZMod 1) x n := by
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
  exact hall.of_nonneg_of_le hnonneg hle

theorem sievedTsum_add_badFibIndexTsum_eq_total (K : ℕ) (x : ℝ) (hx : 1 < x) :
    sievedTsum K x + badFibIndexTsum K x = primeResidueTsum (0 : ZMod 1) x := by
  have hs := summable_sievedTerm K x hx
  have hb := summable_badFibIndexTerm K x hx
  calc
    sievedTsum K x + badFibIndexTsum K x =
        ∑' n : ℕ, (sievedTerm K x n + badFibIndexTerm K x n) := by
      rw [Summable.tsum_add hs hb]
      rfl
    _ = primeResidueTsum (0 : ZMod 1) x := by
      rw [tsum_congr (fun n => sieved_add_bad_term_eq_total K x n)]
      rfl

theorem tendsto_scaled_sievedTsum (K : ℕ)
    (hpair : ∀ k ∈ Finset.Icc 1 K, ∀ s : Bool,
      Tendsto (fun x : ℝ => (x - 1) * linearPrimePairTsum k s x)
        (𝓝[>] (1 : ℝ)) (𝓝 0)) :
    Tendsto (fun x : ℝ => (x - 1) * sievedTsum K x)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have hbad := tendsto_scaled_badFibIndexTsum K hpair
  have ha : IsUnit (0 : ZMod 1) :=
    (ZMod.isUnit_iff_coprime 0 1).mpr (by decide : Nat.Coprime 0 1)
  have htotal := tendsto_primeResidueClass_abel_weight (a := (0 : ZMod 1)) ha
  have hunit : ((1 : ℕ).totient : ℝ)⁻¹ = 1 := by norm_num [Nat.totient]
  have htotal' : Tendsto
      (fun x : ℝ => (x - 1) * primeResidueTsum (0 : ZMod 1) x)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    simpa [hunit] using htotal
  have hsub := htotal'.sub hbad
  have heq : (fun x : ℝ => (x - 1) * sievedTsum K x) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x => (x - 1) * primeResidueTsum (0 : ZMod 1) x -
        (x - 1) * badFibIndexTsum K x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < x := by simpa using hx
    have hsplit := sievedTsum_add_badFibIndexTsum_eq_total K x hx'
    rw [← hsplit]
    ring
  simpa using hsub.congr' heq.symm

end MathGacha
