import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

open Finset
namespace MathGacha
noncomputable def coprimeHarmonic (N m : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, if a.Coprime m then (a : ℝ)⁻¹ else 0

noncomputable def badHarmonicMass (N m r : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N,
    if a.Coprime m ∧ r ∣ a then (a : ℝ)⁻¹ else 0

/-- Split coprime harmonic mass according to divisibility by one prime. -/
theorem coprimeHarmonic_split {N m r : ℕ} (hr : r.Prime) :
    coprimeHarmonic N m = coprimeHarmonic N (m*r) + badHarmonicMass N m r := by
  have hstep (a : ℕ) : a.Coprime (m*r) ↔ a.Coprime m ∧ ¬r ∣ a := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨ham, har⟩
      exact ⟨ham, hr.coprime_iff_not_dvd.mp har.symm⟩
    · rintro ⟨ham, hnr⟩
      exact ⟨ham, (hr.coprime_iff_not_dvd.mpr hnr).symm⟩
  unfold coprimeHarmonic badHarmonicMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases ham : a.Coprime m <;> by_cases hdiv : r ∣ a <;>
    simp [hstep, ham, hdiv]

/-- The multiples of one prime contribute at most the reciprocal-prime
fraction of the original coprime harmonic mass. -/
theorem badHarmonicMass_le {N m r : ℕ} (hr : r.Prime) (hrm : ¬ r ∣ m) :
    badHarmonicMass N m r ≤ (r : ℝ)⁻¹ * coprimeHarmonic N m := by
  let A := (Finset.Icc 1 N).filter fun a => a.Coprime m ∧ r ∣ a
  let B := (Finset.Icc 1 N).filter fun n => n.Coprime m ∧ r*n ≤ N
  have hA : badHarmonicMass N m r = ∑ a ∈ A, (a : ℝ)⁻¹ := by
    simp [badHarmonicMass, A, Finset.sum_filter]
  have hbij : (∑ a ∈ A, (a : ℝ)⁻¹) = ∑ n ∈ B, (r*n : ℝ)⁻¹ := by
    symm
    refine Finset.sum_bij (fun n _ => r*n) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [B, Finset.mem_filter, Finset.mem_Icc] at hn
      apply Finset.mem_filter.mpr
      have hnpos : 0 < n := by omega
      have hrpos : 0 < r := hr.pos
      have hprodpos : 0 < r*n := Nat.mul_pos hrpos hnpos
      have hprodge : 1 ≤ r*n := by omega
      refine ⟨Finset.mem_Icc.mpr ⟨hprodge, hn.2.2⟩, ?_⟩
      exact ⟨(Nat.coprime_mul_iff_left).2
        ⟨hr.coprime_iff_not_dvd.mpr hrm, hn.2.1⟩, dvd_mul_right r n⟩
    · intro n hn n' hn' he
      exact Nat.mul_left_cancel hr.pos he
    · intro a ha
      simp only [A, Finset.mem_filter, Finset.mem_Icc] at ha
      refine ⟨a/r, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        have hrle : r ≤ a := Nat.le_of_dvd (by omega) ha.2.2
        have hquotpos : 0 < a/r := Nat.div_pos hrle hr.pos
        have hquotle : a/r ≤ N := (Nat.div_le_self _ _).trans ha.1.2
        have hmul : r*(a/r)=a := by
          calc
            r*(a/r) = (a/r)*r := Nat.mul_comm _ _
            _ = a := Nat.div_mul_cancel ha.2.2
        have hquotge : 1 ≤ a/r := by omega
        refine ⟨Finset.mem_Icc.mpr ⟨hquotge, hquotle⟩, ?_⟩
        refine ⟨Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd ha.2.2) ha.2.1, ?_⟩
        rw [hmul]
        exact ha.1.2
      · calc
          r*(a/r) = (a/r)*r := Nat.mul_comm _ _
          _ = a := Nat.div_mul_cancel ha.2.2
    · intro n hn
      simp [Nat.cast_mul]
  have hsubset : (∑ n ∈ B, (n : ℝ)⁻¹) ≤ coprimeHarmonic N m := by
    unfold coprimeHarmonic
    simp only [B, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hc : n.Coprime m
    · by_cases hbound : r*n ≤ N
      · simp [hbound]
      · simp [hbound]
        positivity
    · simp [hc]
  have hscale : (∑ n ∈ B, (r*n : ℝ)⁻¹) =
      (r : ℝ)⁻¹ * ∑ n ∈ B, (n : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have hnpos : 1 ≤ n := (Finset.mem_Icc.mp ((Finset.mem_filter.mp hn).1)).1
      exact_mod_cast (by omega : n ≠ 0)
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
    field_simp [hr0, hn0]
  rw [hA, hbij, hscale]
  exact mul_le_mul_of_nonneg_left hsubset (by positivity)

/-- Removing a new prime from the harmonic sieve preserves the Euler-factor
fraction `1−1/r` of the mass. -/
theorem coprimeHarmonic_prime_step {N m r : ℕ} (hr : r.Prime) (hrm : ¬ r ∣ m) :
    coprimeHarmonic N (m*r) ≥
      (1 - (r : ℝ)⁻¹) * coprimeHarmonic N m := by
  rw [coprimeHarmonic_split (N:=N) (m:=m) (r:=r) hr]
  have hbad := badHarmonicMass_le (N:=N) hr hrm
  rw [coprimeHarmonic_split (N:=N) (m:=m) (r:=r) hr] at hbad
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hscaled := mul_le_mul_of_nonneg_left hbad (le_of_lt hrpos)
  have hscaled' : (r : ℝ) * badHarmonicMass N m r ≤
      coprimeHarmonic N (m*r) + badHarmonicMass N m r := by
    calc
      (r : ℝ) * badHarmonicMass N m r ≤
          (r : ℝ) * ((r : ℝ)⁻¹ *
            (coprimeHarmonic N (m*r) + badHarmonicMass N m r)) := hscaled
      _ = coprimeHarmonic N (m*r) + badHarmonicMass N m r := by
        field_simp [hr0]
  have hfactor : 1 - (r : ℝ)⁻¹ = ((r : ℝ)-1) / r := by
    field_simp [hr0]
  rw [hfactor, div_mul_eq_mul_div]
  apply (div_le_iff₀ hrpos).2
  nlinarith

noncomputable def deletionFactorList : List ℕ → ℝ
  | [] => 1
  | r :: L => (1 - (r : ℝ)⁻¹) * deletionFactorList L

theorem prime_not_dvd_list_prod {r : ℕ} (hr : r.Prime) (L : List ℕ)
    (hprime : ∀ p ∈ L, p.Prime) (hne : ∀ p ∈ L, p ≠ r) : ¬ r ∣ L.prod := by
  induction L with
  | nil => simp [hr.not_dvd_one]
  | cons p L ih =>
      intro h
      rw [List.prod_cons] at h
      rcases hr.dvd_mul.mp h with hdivp | hdivL
      · have hcase := (Nat.dvd_prime (hprime p (by simp))).mp hdivp
        rcases hcase with h1 | heq
        · exact hr.ne_one h1
        · exact hne p (by simp) heq.symm
      · exact ih (fun q hq => hprime q (by simp [hq]))
          (fun q hq => hne q (by simp [hq])) hdivL

/-- Iterating prime deletion gives the product of the local Euler factors. -/
theorem coprimeHarmonic_list_lower {N M : ℕ} (L : List ℕ)
    (hnodup : L.Nodup) (hprime : ∀ r ∈ L, r.Prime)
    (hnondvd : ∀ r ∈ L, ¬ r ∣ M) :
    coprimeHarmonic N (M * L.prod) ≥ deletionFactorList L * coprimeHarmonic N M := by
  induction L generalizing M with
  | nil => simp [deletionFactorList]
  | cons r L ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hrnotmem, hLnodup⟩
      have hr : r.Prime := hprime r (by simp)
      have hLprime : ∀ p ∈ L, p.Prime := fun p hp => hprime p (by simp [hp])
      have hLnotM : ∀ p ∈ L, ¬ p ∣ M := fun p hp => hnondvd p (by simp [hp])
      have hrneL : ∀ p ∈ L, p ≠ r := by
        intro p hp heq
        apply hrnotmem
        simpa [heq] using hp
      have hrnotprod : ¬ r ∣ L.prod := prime_not_dvd_list_prod hr L hLprime hrneL
      have hrnot : ¬ r ∣ M * L.prod := by
        intro h
        rcases hr.dvd_mul.mp h with hM | hprod
        · exact hnondvd r (by simp) hM
        · exact hrnotprod hprod
      have hstep := coprimeHarmonic_prime_step (N:=N) (m:=M*L.prod) hr hrnot
      have htail := ih hLnodup hLprime hLnotM
      have hfactor : 0 ≤ 1 - (r : ℝ)⁻¹ := by
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr.one_lt.le
        have hrpos : (0 : ℝ) < r := by exact_mod_cast hr.pos
        rw [sub_nonneg]
        exact (inv_le_one₀ hrpos).2 hrR
      calc
        coprimeHarmonic N (M * (r * L.prod)) =
            coprimeHarmonic N ((M*L.prod)*r) := by congr 1; ac_rfl
        _ ≥ (1 - (r : ℝ)⁻¹) * coprimeHarmonic N (M*L.prod) := hstep
        _ ≥ (1 - (r : ℝ)⁻¹) *
              (deletionFactorList L * coprimeHarmonic N M) :=
              mul_le_mul_of_nonneg_left htail hfactor
        _ = deletionFactorList (r::L) * coprimeHarmonic N M := by
              simp [deletionFactorList]
              ring

theorem coprimeHarmonic_squarefreeProduct_lower {N M k : ℕ}
    (hk : Squarefree k)
    (havoid : ∀ r ∈ k.primeFactorsList, ¬ r ∣ M) :
    coprimeHarmonic N (M*k) ≥
      deletionFactorList k.primeFactorsList * coprimeHarmonic N M := by
  have h := coprimeHarmonic_list_lower (N:=N) (M:=M) k.primeFactorsList
    hk.nodup_primeFactorsList (fun r hr => Nat.prime_of_mem_primeFactorsList hr) havoid
  have hkprod : k.primeFactorsList.prod = k := Nat.prod_primeFactorsList hk.ne_zero
  rw [hkprod] at h
  exact h

theorem deletionFactorList_eq_eulerProduct {k : ℕ} (hk : Squarefree k) :
    deletionFactorList k.primeFactorsList =
      ∏ r ∈ k.primeFactors, (1 - (r : ℝ)⁻¹) := by
  let f : ℕ → ℝ := fun r => 1 - (r : ℝ)⁻¹
  have hmap (L : List ℕ) :
      deletionFactorList L = (L.map f).prod := by
    induction L with
    | nil => simp [deletionFactorList]
    | cons r L ih => simp [deletionFactorList, f, ih]
  calc
    deletionFactorList k.primeFactorsList = (k.primeFactorsList.map f).prod := hmap _
    _ = k.primeFactorsList.toFinset.prod f :=
      (List.prod_toFinset f hk.nodup_primeFactorsList).symm
    _ = ∏ r ∈ k.primeFactors, (1 - (r : ℝ)⁻¹) := by
      simp [f, Nat.toFinset_factors]

theorem coprimeHarmonic_squarefreeEuler_lower {N M k : ℕ}
    (hk : Squarefree k) (havoid : ∀ r ∈ k.primeFactorsList, ¬ r ∣ M) :
    coprimeHarmonic N (M*k) ≥
      (∏ r ∈ k.primeFactors, (1 - (r : ℝ)⁻¹)) * coprimeHarmonic N M := by
  have h := coprimeHarmonic_squarefreeProduct_lower (N:=N) (M:=M) hk havoid
  rw [deletionFactorList_eq_eulerProduct hk] at h
  exact h

noncomputable def eulerCoprimeDensity (k : ℕ) : ℝ :=
  ∏ r ∈ k.primeFactors, (1 - (r : ℝ)⁻¹)

theorem coprimeHarmonic_one_eq_harmonic (N : ℕ) :
    coprimeHarmonic N 1 = (harmonic N : ℝ) := by
  simp [coprimeHarmonic, harmonic_eq_sum_Icc]

theorem eulerCoprimeDensity_nonneg (k : ℕ) : 0 ≤ eulerCoprimeDensity k := by
  unfold eulerCoprimeDensity
  apply Finset.prod_nonneg
  intro r hr
  have hrPrime := Nat.prime_of_mem_primeFactors hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hrPrime.pos
  have hrge : (1 : ℝ) ≤ r := by exact_mod_cast hrPrime.one_lt.le
  rw [sub_nonneg]
  exact (inv_le_one₀ hrpos).2 hrge

theorem coprimeHarmonic_lower_log {N k : ℕ} (hk : Squarefree k) :
    coprimeHarmonic N k ≥ eulerCoprimeDensity k * Real.log (N+1) := by
  have hbase := coprimeHarmonic_squarefreeEuler_lower (N:=N) (M:=1) hk
    (by intro r hr; exact (Nat.prime_of_mem_primeFactorsList hr).not_dvd_one)
  rw [coprimeHarmonic_one_eq_harmonic] at hbase
  have hbase' : eulerCoprimeDensity k * (harmonic N : ℝ) ≤ coprimeHarmonic N k := by
    simpa [eulerCoprimeDensity] using hbase
  have hh : Real.log (N+1) ≤ (harmonic N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
  have he := eulerCoprimeDensity_nonneg k
  exact le_trans (mul_le_mul_of_nonneg_left hh he) hbase'
def totientHarmonicRad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

lemma totientHarmonicRad_eq_radical (m : ℕ) :
    totientHarmonicRad m = UniqueFactorizationMonoid.radical m := by
  rw [totientHarmonicRad, Nat.radical_eq_prod_primeFactors]

lemma totientHarmonicRad_squarefree (m : ℕ) : Squarefree (totientHarmonicRad m) := by
  rw [totientHarmonicRad_eq_radical]
  exact UniqueFactorizationMonoid.squarefree_radical

lemma totientHarmonic_coprime_rad_iff {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    m.Coprime n ↔ (totientHarmonicRad m).Coprime n := by
  have hr : totientHarmonicRad m ≠ 0 := by
    rw [totientHarmonicRad_eq_radical]
    exact (ne_of_gt (Nat.radical_pos m))
  rw [← Nat.disjoint_primeFactors hm hn,
      ← Nat.disjoint_primeFactors hr hn,
      totientHarmonicRad_eq_radical, Nat.primeFactors_radical]

lemma totientHarmonic_radical_density {m : ℕ} (hm : 0 < m) :
    eulerCoprimeDensity (totientHarmonicRad m) = (m.totient : ℝ) / m := by
  rw [eulerCoprimeDensity, totientHarmonicRad_eq_radical, Nat.primeFactors_radical]
  have hRat := Nat.totient_eq_mul_prod_factors m
  have hReal₀ := congrArg (fun z : ℚ => (z : ℝ)) hRat
  have hReal : (m.totient : ℝ) = (m : ℝ) *
      ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] at hReal₀
    exact hReal₀
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  rw [hReal]
  field_simp [hmR]

lemma totientHarmonic_radical_coprime_eq {N m : ℕ} (hm : m ≠ 0) :
    coprimeHarmonic N (totientHarmonicRad m) = coprimeHarmonic N m := by
  unfold coprimeHarmonic
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hiff : n.Coprime m ↔ n.Coprime (totientHarmonicRad m) := by
    simpa only [Nat.coprime_comm] using
      (totientHarmonic_coprime_rad_iff hm hn0)
  by_cases hcop : n.Coprime m
  · have hrad := hiff.mp hcop
    rw [if_pos hrad, if_pos hcop]
  · have hrad : ¬ n.Coprime (totientHarmonicRad m) := by
      intro hrad
      exact hcop (hiff.mpr hrad)
    rw [if_neg hrad, if_neg hcop]

theorem totientHarmonic_coprime_lower_log {N m : ℕ} (hm : 0 < m) :
    coprimeHarmonic N m ≥ (m.totient : ℝ) / m * Real.log (N+1) := by
  have hsf := totientHarmonicRad_squarefree m
  have h := coprimeHarmonic_lower_log (N:=N) (k:=totientHarmonicRad m) hsf
  rw [totientHarmonic_radical_coprime_eq (N:=N) hm.ne'] at h
  rw [totientHarmonic_radical_density hm] at h
  exact h

end MathGacha
