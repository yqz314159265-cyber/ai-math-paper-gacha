import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

open Finset BigOperators

namespace MathGacha


theorem card_filter_dvd_Icc (d K : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 K).filter (fun n => d ∣ n)).card = K / d := by
  classical
  let A := Finset.Icc 1 (K / d)
  have hEq : A.image (fun m => d * m) = (Finset.Icc 1 K).filter (fun n => d ∣ n) := by
    ext n
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨m, hmA, hmn⟩
      have ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hmA
      have hlow : 1 ≤ d*m := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hd.ne' (Nat.ne_of_gt (by omega)))
      have hhigh : d*m ≤ K := by
        calc
          d*m ≤ d*(K/d) := Nat.mul_le_mul_left d hmhi
          _ ≤ K := Nat.mul_div_le K d
      exact ⟨Finset.mem_Icc.mpr ⟨by simpa [hmn] using hlow, by simpa [hmn] using hhigh⟩, ⟨m, hmn.symm⟩⟩
    · rintro ⟨hn, hdiv⟩
      have ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
      rcases hdiv with ⟨m, hmn⟩
      have hmlo : 1 ≤ m := by
        by_contra hm
        have : m = 0 := by omega
        subst m
        simp [hmn] at hnlo
      have hmhi : m ≤ K/d := (Nat.le_div_iff_mul_le hd).2 (by
        simpa [hmn, Nat.mul_comm] using hnhi)
      exact ⟨m, Finset.mem_Icc.mpr ⟨hmlo, hmhi⟩, hmn.symm⟩
  have hinj : Function.Injective (fun m => d*m) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hd (by simpa using hab)
  rw [← hEq, Finset.card_image_of_injective A hinj]
  simp [A]




noncomputable def weight (s : Finset ℕ) (k : ℕ) : ℝ :=
  ∏ r ∈ s, if r ∣ k then ((r : ℝ) - 1) / ((r : ℝ) - 2) else 1

noncomputable def correction (s : Finset ℕ) : ℝ :=
  ∏ r ∈ s, (1 + 1 / ((r : ℝ) * ((r : ℝ) - 2)))

lemma weight_mul_prime {s : Finset ℕ} {p m : ℕ}
    (hp : p.Prime) (hps : ∀ q ∈ s, q.Prime) (hpn : p ∉ s) :
    weight s (p*m) = weight s m := by
  classical
  unfold weight
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : Nat.Coprime q p := by
    apply (Nat.coprime_primes (hps q hq) hp).mpr
    intro heq
    exact hpn (heq ▸ hq)
  have hdvd : q ∣ p*m ↔ q ∣ m := by
    simpa [Nat.Coprime] using hqp.dvd_mul_left
  simp [hdvd]

lemma sum_multiples_weight {s : Finset ℕ} {p K : ℕ}
    (hp : p.Prime) (hps : ∀ q ∈ s, q.Prime) (hpn : p ∉ s) :
    (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), weight s k) =
      ∑ m ∈ Finset.Icc 1 (K/p), weight s m := by
  classical
  apply Finset.sum_bij (fun k hk => k/p)
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hki, hdiv⟩
    have hkpos : 0 < k := by have := (Finset.mem_Icc.mp hki).1; omega
    have hkp : p ≤ k := Nat.le_of_dvd hkpos hdiv
    have hlow : 1 ≤ k/p := Nat.succ_le_iff.mpr (Nat.div_pos hkp hp.pos)
    have hhigh : k/p ≤ K/p := Nat.div_le_div_right (Finset.mem_Icc.mp hki).2
    exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩
  · intro k hk1 l hl1 heq
    have hd1 := (Finset.mem_filter.mp hk1).2
    have hd2 := (Finset.mem_filter.mp hl1).2
    have hkEq : k/p*p = k := Nat.div_mul_cancel hd1
    have hlEq : l/p*p = l := Nat.div_mul_cancel hd2
    calc
      k = k/p*p := hkEq.symm
      _ = l/p*p := congrArg (fun x => x*p) heq
      _ = l := hlEq
  · intro m hm
    have ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    refine ⟨p*m, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ?_, dvd_mul_right p m⟩
      constructor
      · have hmpos : 0 < m := by omega
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hmpos.ne')
      · calc
          p*m ≤ p*(K/p) := Nat.mul_le_mul_left p hmhi
          _ ≤ K := Nat.mul_div_le K p
    · simp [Nat.mul_div_cancel_left m hp.pos]
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hki, hdiv⟩
    have hrepr : k = p*(k/p) := by
      calc
        k = k/p*p := (Nat.div_mul_cancel hdiv).symm
        _ = p*(k/p) := Nat.mul_comm _ _
    rw [hrepr, Nat.mul_div_cancel_left (k/p) hp.pos]
    exact weight_mul_prime hp hps hpn












lemma weight_insert {s : Finset ℕ} {p k : ℕ} (hpn : p ∉ s) :
    weight (insert p s) k = weight s k *
      (if p ∣ k then ((p : ℝ)-1)/((p : ℝ)-2) else 1) := by
  classical
  unfold weight
  rw [Finset.prod_insert hpn]
  ring

theorem mean_weight_le_correction (s : Finset ℕ)
    (hps : ∀ r ∈ s, r.Prime) (hodd : ∀ r ∈ s, 2 < r) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, weight s k) ≤ (K : ℝ) * correction s := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simp [weight, correction]
  | @insert p s hpn ih =>
    have hpp : p.Prime := hps p (Finset.mem_insert_self p s)
    have hpo : 2 < p := hodd p (Finset.mem_insert_self p s)
    have hps' : ∀ r ∈ s, r.Prime := fun r hr => hps r (Finset.mem_insert_of_mem hr)
    have hodd' : ∀ r ∈ s, 2 < r := fun r hr => hodd r (Finset.mem_insert_of_mem hr)
    have ihK := ih hps' hodd' K
    have ihDiv := ih hps' hodd' (K/p)
    let d : ℝ := (p : ℝ) - 2
    have hd : d ≠ 0 := by
      dsimp [d]
      have hpc : (2 : ℝ) < p := by exact_mod_cast hpo
      linarith
    have hterm (k : ℕ) : weight (insert p s) k =
        weight s k + if p ∣ k then weight s k / d else 0 := by
      rw [weight_insert hpn]
      by_cases hdiv : p ∣ k
      · simp only [if_pos hdiv]
        have hnumeq : (p : ℝ) - 1 = d + 1 := by dsimp [d]; ring
        have hpEq : (p : ℝ) = d + 2 := by dsimp [d]; ring
        rw [hnumeq, hpEq]
        field_simp [hd]
        ring
      · simp [hdiv]
    have hfactor :
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), weight s k / d) =
          (1/d) * (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), weight s k) := by
      calc
        _ = ∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), (1/d) * weight s k := by
          apply Finset.sum_congr rfl
          intro k hk
          field_simp
        _ = _ := by rw [Finset.mul_sum]
    have hsum : (∑ k ∈ Finset.Icc 1 K, weight (insert p s) k) =
        (∑ k ∈ Finset.Icc 1 K, weight s k) +
          (1/d) * (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), weight s k) := by
      calc
        _ = ∑ k ∈ Finset.Icc 1 K, (weight s k + if p ∣ k then weight s k / d else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k
        _ = (∑ k ∈ Finset.Icc 1 K, weight s k) +
            ∑ k ∈ Finset.Icc 1 K, if p ∣ k then weight s k / d else 0 := Finset.sum_add_distrib
        _ = (∑ k ∈ Finset.Icc 1 K, weight s k) +
            ∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), weight s k / d := by
              congr 1
              rw [Finset.sum_ite]
              simp
        _ = _ := by rw [hfactor]
    have hdenpos : 0 < 1/d := by
      apply one_div_pos.mpr
      dsimp [d]
      have hpc : (2 : ℝ) < p := by exact_mod_cast hpo
      linarith
    have hprodpos : 0 ≤ correction s := by
      unfold correction
      apply Finset.prod_nonneg
      intro r hr
      have hro : (2 : ℝ) < r := by exact_mod_cast hodd' r hr
      positivity
    have hKdiv : ((K/p : ℕ) : ℝ) ≤ (K : ℝ) / p := Nat.cast_div_le
    have hrew : (1/d) * ((K : ℝ)/p * correction s) =
        (K : ℝ) * correction s * (1 / ((p : ℝ) * d)) := by
      field_simp [hd]

    have hstep : (K : ℝ) * correction s +
        (1/d) * (((K/p : ℕ) : ℝ) * correction s) ≤
        (K : ℝ) * correction s * (1 + 1 / ((p : ℝ) * d)) := by
      have hle := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hKdiv hprodpos) (le_of_lt hdenpos)
      calc
        _ ≤ (K : ℝ) * correction s +
            (1/d) * ((K : ℝ)/p * correction s) := by
              simpa [add_comm] using add_le_add_left hle ((K : ℝ) * correction s)
        _ = (K : ℝ) * correction s +
            (K : ℝ) * correction s * (1 / ((p : ℝ) * d)) := by rw [hrew]
        _ = _ := by ring
    calc
      (∑ k ∈ Finset.Icc 1 K, weight (insert p s) k)
          ≤ (K : ℝ) * correction s + (1/d) * (((K/p : ℕ) : ℝ) * correction s) := by
            rw [hsum, sum_multiples_weight hpp hps' hpn]
            exact add_le_add ihK (mul_le_mul_of_nonneg_left ihDiv (le_of_lt hdenpos))
      _ ≤ (K : ℝ) * correction s * (1 + 1 / ((p : ℝ) * d)) := hstep
      _ = (K : ℝ) * correction (insert p s) := by
        simp [correction, hpn, d]
        ring







noncomputable def telescopeFactor (r : ℕ) : ℝ :=
  1 + 1 / ((r : ℝ) * ((r : ℝ) - 2))

lemma telescope_step (x : ℝ) (h0 : 0 ≤ x) :
    (2 * (x + 1) / (x + 2)) * (1 + 1 / ((x + 3) * (x + 1))) =
      2 * (x + 2) / (x + 3) := by
  have h1 : x + 1 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have h3 : x + 3 ≠ 0 := by linarith
  field_simp [h1, h2, h3]
  ring

theorem telescope_range (n : ℕ) :
    (∏ i ∈ Finset.range n, telescopeFactor (i + 3)) =
      2 * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by
  induction n with
  | zero => norm_num [telescopeFactor]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [telescopeFactor]
    have hsub : ((↑(n + 3 : ℕ) : ℝ) - 2) = (n : ℝ) + 1 := by push_cast; ring
    rw [hsub]
    push_cast
    convert telescope_step (n : ℝ) (by positivity) using 1; ring_nf

theorem correction_all_numbers (K : ℕ) (hK : 3 ≤ K) :
    correction (Finset.Icc 3 K) = 2 * ((K - 1 : ℕ) : ℝ) / (K : ℝ) := by
  change (∏ r ∈ Finset.Icc 3 K, telescopeFactor r) = _
  have hmap :
      (∏ i ∈ Finset.range (K - 2), telescopeFactor (i + 3)) =
        (∏ r ∈ Finset.Icc 3 K, telescopeFactor r) := by
    apply Finset.prod_bij (fun i _ => i + 3)
    · intro i hi
      simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
      omega
    · intro i hi j hj hij
      omega
    · intro r hr
      have ⟨hrlo, hrhi⟩ := Finset.mem_Icc.mp hr
      refine ⟨r - 3, Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · omega
    · intro i hi
      rfl
  rw [← hmap, telescope_range]
  have hKcast : ((K - 2 + 1 : ℕ) : ℝ) = ((K - 1 : ℕ) : ℝ) := by congr 1; omega
  have hKden : ((K - 2 + 2 : ℕ) : ℝ) = (K : ℝ) := by congr 1; omega
  rw [hKcast, hKden]
lemma correction_le_all_numbers {s : Finset ℕ} {K : ℕ}
    (hs : s ⊆ Finset.Icc 3 K) (_hK : 3 ≤ K) :
    correction s ≤ correction (Finset.Icc 3 K) := by
  unfold correction
  apply Finset.prod_le_prod_of_subset_of_one_le hs
  · intro r hr
    have hr3 : 3 ≤ r := by have := hs hr; exact (Finset.mem_Icc.mp this).1
    have hreal : (2 : ℝ) < (r : ℝ) := by exact_mod_cast (show 2 < r by omega)
    have hden : 0 < (r : ℝ) * ((r : ℝ) - 2) := by positivity
    have hpos : 0 < 1 / ((r : ℝ) * ((r : ℝ) - 2)) := one_div_pos.mpr hden
    linarith
  · intro r hr hnot
    have hr3 : 3 ≤ r := (Finset.mem_Icc.mp hr).1
    have hreal : (2 : ℝ) < (r : ℝ) := by exact_mod_cast (show 2 < r by omega)
    have hden : 0 < (r : ℝ) * ((r : ℝ) - 2) := by positivity
    have hpos : 0 < 1 / ((r : ℝ) * ((r : ℝ) - 2)) := one_div_pos.mpr hden
    linarith
theorem mean_weight_le_two {s : Finset ℕ} {K : ℕ}
    (hps : ∀ r ∈ s, r.Prime) (hodd : ∀ r ∈ s, 2 < r)
    (hs : s ⊆ Finset.Icc 3 K) (hK : 3 ≤ K) :
    (∑ k ∈ Finset.Icc 1 K, weight s k) ≤ 2 * K := by
  calc
    _ ≤ (K : ℝ) * correction s := mean_weight_le_correction s hps hodd K
    _ ≤ (K : ℝ) * correction (Finset.Icc 3 K) := by
      exact mul_le_mul_of_nonneg_left (correction_le_all_numbers hs hK) (by positivity)
    _ = 2 * K * ((K - 1 : ℕ) : ℝ) / (K : ℝ) := by rw [correction_all_numbers K hK]; ring
    _ ≤ 2 * K := by
      have hKpos : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
      have hsub : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.sub_le K 1)
      have heq : 2 * (K : ℝ) * ((K - 1 : ℕ) : ℝ) / (K : ℝ) = 2 * ((K - 1 : ℕ) : ℝ) := by field_simp [ne_of_gt hKpos]
      rw [heq]
      nlinarith
















noncomputable def localWeight (s : Finset ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ r ∈ s, if r ∣ k then 1 + g r else 1

noncomputable def localCorrection (s : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∏ r ∈ s, (1 + g r / (r : ℝ))

lemma localWeight_mul_prime {s : Finset ℕ} {g : ℕ → ℝ} {p m : ℕ}
    (hp : p.Prime) (hps : ∀ q ∈ s, q.Prime) (hpn : p ∉ s) :
    localWeight s g (p*m) = localWeight s g m := by
  classical
  unfold localWeight
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : Nat.Coprime q p := by
    apply (Nat.coprime_primes (hps q hq) hp).mpr
    intro heq
    exact hpn (heq ▸ hq)
  have hdvd : q ∣ p*m ↔ q ∣ m := by
    simpa [Nat.Coprime] using hqp.dvd_mul_left
  simp [hdvd]

lemma sum_multiples_localWeight {s : Finset ℕ} {g : ℕ → ℝ} {p K : ℕ}
    (hp : p.Prime) (hps : ∀ q ∈ s, q.Prime) (hpn : p ∉ s) :
    (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), localWeight s g k) =
      ∑ m ∈ Finset.Icc 1 (K/p), localWeight s g m := by
  classical
  apply Finset.sum_bij (fun k hk => k/p)
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hki, hdiv⟩
    have hkpos : 0 < k := by have := (Finset.mem_Icc.mp hki).1; omega
    have hkp : p ≤ k := Nat.le_of_dvd hkpos hdiv
    have hlow : 1 ≤ k/p := Nat.succ_le_iff.mpr (Nat.div_pos hkp hp.pos)
    have hhigh : k/p ≤ K/p := Nat.div_le_div_right (Finset.mem_Icc.mp hki).2
    exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩
  · intro k hk1 l hl1 heq
    have hd1 := (Finset.mem_filter.mp hk1).2
    have hd2 := (Finset.mem_filter.mp hl1).2
    have hkEq : k/p*p = k := Nat.div_mul_cancel hd1
    have hlEq : l/p*p = l := Nat.div_mul_cancel hd2
    calc
      k = k/p*p := hkEq.symm
      _ = l/p*p := congrArg (fun x => x*p) heq
      _ = l := hlEq
  · intro m hm
    have ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    refine ⟨p*m, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ?_, dvd_mul_right p m⟩
      constructor
      · have hmpos : 0 < m := by omega
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hmpos.ne')
      · calc
          p*m ≤ p*(K/p) := Nat.mul_le_mul_left p hmhi
          _ ≤ K := Nat.mul_div_le K p
    · simp [Nat.mul_div_cancel_left m hp.pos]
  · intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hki, hdiv⟩
    have hrepr : k = p*(k/p) := by
      calc
        k = k/p*p := (Nat.div_mul_cancel hdiv).symm
        _ = p*(k/p) := Nat.mul_comm _ _
    rw [hrepr, Nat.mul_div_cancel_left (k/p) hp.pos]
    exact localWeight_mul_prime hp hps hpn

lemma localWeight_insert {s : Finset ℕ} {g : ℕ → ℝ} {p k : ℕ} (hpn : p ∉ s) :
    localWeight (insert p s) g k = localWeight s g k *
      (if p ∣ k then 1 + g p else 1) := by
  classical
  unfold localWeight
  rw [Finset.prod_insert hpn]
  ring

theorem mean_localWeight_le_correction (s : Finset ℕ) (g : ℕ → ℝ)
    (hps : ∀ r ∈ s, r.Prime) (hpos : ∀ r ∈ s, 0 < r)
    (hg : ∀ r ∈ s, 0 ≤ g r) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, localWeight s g k) ≤ (K : ℝ) * localCorrection s g := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simp [localWeight, localCorrection]
  | @insert p s hpn ih =>
    have hpp : p.Prime := hps p (Finset.mem_insert_self p s)
    have hppos : 0 < p := hpos p (Finset.mem_insert_self p s)
    have hps' : ∀ r ∈ s, r.Prime := fun r hr => hps r (Finset.mem_insert_of_mem hr)
    have hpos' : ∀ r ∈ s, 0 < r := fun r hr => hpos r (Finset.mem_insert_of_mem hr)
    have hg' : ∀ r ∈ s, 0 ≤ g r := fun r hr => hg r (Finset.mem_insert_of_mem hr)
    have ihK := ih hps' hpos' hg' K
    have ihDiv := ih hps' hpos' hg' (K/p)
    have hterm (k : ℕ) : localWeight (insert p s) g k =
        localWeight s g k + if p ∣ k then localWeight s g k * g p else 0 := by
      rw [localWeight_insert hpn]
      by_cases hdiv : p ∣ k
      · simp only [if_pos hdiv]
        ring
      · simp [hdiv]
    have hfactor :
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), localWeight s g k * g p) =
          g p * (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), localWeight s g k) := by
      calc
        _ = ∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), g p * localWeight s g k := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hsum : (∑ k ∈ Finset.Icc 1 K, localWeight (insert p s) g k) =
        (∑ k ∈ Finset.Icc 1 K, localWeight s g k) +
          g p * (∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), localWeight s g k) := by
      calc
        _ = ∑ k ∈ Finset.Icc 1 K,
            (localWeight s g k + if p ∣ k then localWeight s g k * g p else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k
        _ = (∑ k ∈ Finset.Icc 1 K, localWeight s g k) +
            ∑ k ∈ Finset.Icc 1 K, if p ∣ k then localWeight s g k * g p else 0 :=
          Finset.sum_add_distrib
        _ = (∑ k ∈ Finset.Icc 1 K, localWeight s g k) +
            ∑ k ∈ (Finset.Icc 1 K).filter (fun k => p ∣ k), localWeight s g k * g p := by
              congr 1
              rw [Finset.sum_ite]
              simp
        _ = _ := by rw [hfactor]
    have hdenpos : 0 ≤ g p / (p : ℝ) := div_nonneg (hg p (Finset.mem_insert_self p s)) (by positivity)
    have hprodpos : 0 ≤ localCorrection s g := by
      unfold localCorrection
      apply Finset.prod_nonneg
      intro r hr
      have hrpos : 0 < (r : ℝ) := by exact_mod_cast hpos' r hr
      have hgr : 0 ≤ g r := hg' r hr
      positivity
    have hKdiv : ((K/p : ℕ) : ℝ) ≤ (K : ℝ) / p := Nat.cast_div_le
    have hweighted : g p * (((K/p : ℕ) : ℝ) * localCorrection s g) ≤
        (g p / (p : ℝ)) * ((K : ℝ) * localCorrection s g) := by
      have hmul := mul_le_mul_of_nonneg_right hKdiv (mul_nonneg (hg p (Finset.mem_insert_self p s)) hprodpos)
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      calc
        _ = (g p * localCorrection s g) * ((K/p : ℕ) : ℝ) := by ring
        _ ≤ (g p * localCorrection s g) * ((K : ℝ) / p) := by exact mul_le_mul_of_nonneg_left hKdiv (mul_nonneg (hg p (Finset.mem_insert_self p s)) hprodpos)
        _ = (g p / (p : ℝ)) * ((K : ℝ) * localCorrection s g) := by field_simp [hpR]
    have hstep : (K : ℝ) * localCorrection s g +
        g p * (((K/p : ℕ) : ℝ) * localCorrection s g) ≤
        (K : ℝ) * localCorrection s g * (1 + g p / (p : ℝ)) := by
      calc
        _ ≤ (K : ℝ) * localCorrection s g +
            (g p / (p : ℝ)) * ((K : ℝ) * localCorrection s g) := by
              simpa [add_comm] using add_le_add_left hweighted ((K : ℝ) * localCorrection s g)
        _ = _ := by ring
    calc
      (∑ k ∈ Finset.Icc 1 K, localWeight (insert p s) g k)
          ≤ (K : ℝ) * localCorrection s g +
              g p * (((K/p : ℕ) : ℝ) * localCorrection s g) := by
            rw [hsum, sum_multiples_localWeight hpp hps' hpn]
            exact add_le_add ihK (mul_le_mul_of_nonneg_left ihDiv
              (hg p (Finset.mem_insert_self p s)))
      _ ≤ (K : ℝ) * localCorrection s g * (1 + g p / (p : ℝ)) := hstep
      _ = (K : ℝ) * localCorrection (insert p s) g := by
        simp [localCorrection, hpn]
        ring





noncomputable def phiSqExcess (p : ℕ) : ℝ := ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1

def smallPrimeSet (K : ℕ) : Finset ℕ := (Finset.Icc 2 K).filter Nat.Prime

lemma phiSqExcess_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ phiSqExcess p := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hratio : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    rw [le_div_iff₀ hden]
    linarith
  unfold phiSqExcess
  nlinarith [sq_nonneg ((p : ℝ) / ((p : ℝ) - 1) - 1)]

lemma phiSqExcess_div_le {p : ℕ} (hp : p.Prime) :
    phiSqExcess p / (p : ℝ) ≤ 6 / (p : ℝ)^2 := by
  let q : ℝ := p
  have hq : 2 ≤ q := by dsimp [q]; exact_mod_cast hp.two_le
  have hqpos : 0 < q := by linarith
  have hm1 : q - 1 ≠ 0 := by linarith
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hform : (q / (q - 1))^2 - 1 = (2*q - 1) / (q - 1)^2 := by
    field_simp [hm1]
    ring
  rw [show phiSqExcess p = (q / (q - 1))^2 - 1 by simp [phiSqExcess, q], hform]
  have hpoly : q * (2*q - 1) ≤ 6 * (q - 1)^2 := by
    have hx : 0 ≤ (q - 2) * (4*q - 3) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hleft : (2*q - 1) / (q - 1)^2 / q = (2*q - 1) / ((q - 1)^2 * q) := by
    field_simp [hm1, hqne]
  rw [hleft]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

lemma phiSq_localCorrection_le_exp (K : ℕ) :
    localCorrection (smallPrimeSet K) phiSqExcess ≤ Real.exp 6 := by
  classical
  have hsubset : smallPrimeSet K ⊆ Finset.Icc 2 K := Finset.filter_subset _ _
  have hprod : localCorrection (smallPrimeSet K) phiSqExcess ≤
      ∏ p ∈ smallPrimeSet K, (1 + 6 / (p : ℝ)^2) := by
    unfold localCorrection
    apply Finset.prod_le_prod
    · intro p hp
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
      have hg : 0 ≤ phiSqExcess p := phiSqExcess_nonneg hpp
      positivity
    · intro p hp
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have h := phiSqExcess_div_le hpp
      linarith
  have hexp := Real.prod_one_add_le_exp_sum (smallPrimeSet K)
      (fun p => show 0 ≤ 6 / (p : ℝ)^2 by positivity)
  have hsum : (∑ p ∈ smallPrimeSet K, 6 / (p : ℝ)^2) ≤ 6 := by
    by_cases hK : 1 ≤ K
    · calc
        _ ≤ ∑ p ∈ Finset.Icc 2 K, 6 / (p : ℝ)^2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro p hp hpn
          positivity
        _ = 6 * ∑ p ∈ Finset.Icc 2 K, ((p : ℝ)^2)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = 6 * ∑ p ∈ Finset.Ioc 1 K, ((p : ℝ)^2)⁻¹ := by
          have hinterval : Finset.Icc 2 K = Finset.Ioc 1 K := by
            ext p
            simp [Finset.mem_Icc, Finset.mem_Ioc]
            omega
          rw [hinterval]
        _ ≤ 6 := by
          have ht := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := K) (by norm_num) hK
          have ht' : (∑ p ∈ Finset.Ioc 1 K, ((p : ℝ)^2)⁻¹) ≤ 1 := by
            calc
              _ ≤ (1 : ℝ)⁻¹ - (K : ℝ)⁻¹ := by simpa using ht
              _ ≤ 1 := by
                have : 0 ≤ (K : ℝ)⁻¹ := by positivity
                norm_num
          nlinarith
    · have hK0 : K = 0 := by omega
      subst K
      simp [smallPrimeSet]
  calc
    _ ≤ ∏ p ∈ smallPrimeSet K, (1 + 6 / (p : ℝ)^2) := hprod
    _ ≤ Real.exp (∑ p ∈ smallPrimeSet K, 6 / (p : ℝ)^2) := hexp
    _ ≤ Real.exp 6 := Real.exp_le_exp.mpr hsum

theorem mean_phiSq_localWeight_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, localWeight (smallPrimeSet K) phiSqExcess k) ≤
      (K : ℝ) * Real.exp 6 := by
  have hps : ∀ p ∈ smallPrimeSet K, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hpos : ∀ p ∈ smallPrimeSet K, 0 < p := fun p hp => (hps p hp).pos
  have hg : ∀ p ∈ smallPrimeSet K, 0 ≤ phiSqExcess p := fun p hp => phiSqExcess_nonneg (hps p hp)
  calc
    _ ≤ (K : ℝ) * localCorrection (smallPrimeSet K) phiSqExcess :=
      mean_localWeight_le_correction (smallPrimeSet K) phiSqExcess hps hpos hg K
    _ ≤ (K : ℝ) * Real.exp 6 := by
      exact mul_le_mul_of_nonneg_left (phiSq_localCorrection_le_exp K) (by positivity)








lemma localWeight_eq_totient_ratio {k K : ℕ} (hk : 0 < k) (hkK : k ≤ K) :
    localWeight (smallPrimeSet K) phiSqExcess k =
      ((k : ℝ) / (k.totient : ℝ))^2 := by
  classical
  have hfilter : (smallPrimeSet K).filter (fun p => p ∣ k) = k.primeFactors := by
    ext p
    simp only [Finset.mem_filter, smallPrimeSet, Finset.mem_Icc, Nat.mem_primeFactors]
    change ((2 ≤ p ∧ p ≤ K) ∧ p.Prime) ∧ p ∣ k ↔ p.Prime ∧ p ∣ k ∧ k ≠ 0
    constructor
    · rintro ⟨⟨⟨hlo, hhi⟩, hp⟩, hdiv⟩
      exact ⟨hp, hdiv, hk.ne'⟩
    · rintro ⟨hp, hdiv, _⟩
      exact ⟨⟨⟨hp.two_le, (Nat.le_of_dvd hk hdiv).trans hkK⟩, hp⟩, hdiv⟩
  have hprod : localWeight (smallPrimeSet K) phiSqExcess k =
      ∏ p ∈ k.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))^2 := by
    unfold localWeight
    rw [← Finset.prod_filter, hfilter]
    apply Finset.prod_congr rfl
    intro p hp
    have hdiv : p ∣ k := (Nat.mem_primeFactors.mp hp).2.1
    have hpe : 1 + phiSqExcess p = ((p : ℝ) / ((p : ℝ) - 1))^2 := by unfold phiSqExcess; ring
    exact hpe
  rw [hprod, Finset.prod_pow]
  let P : ℝ := ∏ p ∈ k.primeFactors, (p : ℝ)
  let Q : ℝ := ∏ p ∈ k.primeFactors, ((p : ℝ) - 1)
  have hQcast : Q = (↑(∏ p ∈ k.primeFactors, (p - 1 : ℕ)) : ℝ) := by
    dsimp [Q]
    calc
      _ = ∏ p ∈ k.primeFactors, ((p - 1 : ℕ) : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [Nat.cast_sub]
        · norm_num
        · exact Nat.one_le_of_lt ((Nat.mem_primeFactors.mp hp).1.one_lt)
      _ = _ := by rw [Nat.cast_prod]
  have hPcast : P = (↑(∏ p ∈ k.primeFactors, p) : ℝ) := by
    dsimp [P]
    rw [Nat.cast_prod]
  have hNatR : (k.totient : ℝ) * P = (k : ℝ) * Q := by
    rw [hPcast, hQcast]
    exact_mod_cast Nat.totient_mul_prod_primeFactors k
  have hphi : 0 < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hk
  have hQ : 0 < Q := by
    dsimp [Q]
    apply Finset.prod_pos
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hp1 : 1 < p := hpp.one_lt
    have : (1 : ℝ) < p := by exact_mod_cast hp1
    linarith
  have hratio : (k : ℝ) / (k.totient : ℝ) = P / Q := by
    field_simp [ne_of_gt hphi, ne_of_gt hQ]
    nlinarith [hNatR]
  have hprodRatio : (∏ p ∈ k.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) = P / Q := by
    dsimp [P, Q]
    rw [Finset.prod_div_distrib]
  rw [hratio]
  rw [hprodRatio]






theorem mean_totient_ratio_sq_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) / (k.totient : ℝ))^2) ≤
      (K : ℝ) * Real.exp 6 := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 K, localWeight (smallPrimeSet K) phiSqExcess k := by
      apply Finset.sum_congr rfl
      intro k hk
      have ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
      exact (localWeight_eq_totient_ratio (by omega) hhi).symm
    _ ≤ (K : ℝ) * Real.exp 6 := mean_phiSq_localWeight_le K



lemma sum_totient_ratio_on_subset_le_sqrt {K : ℕ} (E : Finset ℕ)
    (hE : E ⊆ Finset.Icc 1 K) :
    (∑ k ∈ E, (k : ℝ) / (k.totient : ℝ)) ≤
      Real.sqrt ((K : ℝ) * Real.exp 6 * (E.card : ℝ)) := by
  have hsq : (∑ k ∈ E, ((k : ℝ) / (k.totient : ℝ))^2) ≤
      (K : ℝ) * Real.exp 6 := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) / (k.totient : ℝ))^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hE
        intro k hk hkn
        positivity
      _ ≤ (K : ℝ) * Real.exp 6 := mean_totient_ratio_sq_le K
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq E
      (fun k => (k : ℝ) / (k.totient : ℝ)) (fun _ => (1 : ℝ))
  have hCS' : (∑ k ∈ E, (k : ℝ) / (k.totient : ℝ))^2 ≤
      ((K : ℝ) * Real.exp 6) * (E.card : ℝ) := by
    calc
      _ ≤ (∑ k ∈ E, ((k : ℝ) / (k.totient : ℝ))^2) * (E.card : ℝ) := by
        simpa using hCS
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (by positivity)
  exact Real.le_sqrt_of_sq_le hCS'



theorem sum_pair_upper_from_totient_lower {K : ℕ} (X c y E : ℝ) (G A : ℕ → ℝ)
    (hX : 0 ≤ X) (hc : 0 < c) (hy : 1 < y)
    (hG : ∀ k ∈ Finset.Icc 1 K,
      c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2 ≤ G k)
    (hA : ∀ k ∈ Finset.Icc 1 K, A k ≤ X / G k + E) :
    (∑ k ∈ Finset.Icc 1 K, A k) ≤
      Real.exp 6 * (K : ℝ) * X / (c * (Real.log y)^2) + (K : ℝ) * E := by
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hden : 0 < c * (Real.log y)^2 := by positivity
  have hrecip : ∀ k ∈ Finset.Icc 1 K,
      1 / G k ≤ ((k : ℝ) / (k.totient : ℝ))^2 / (c * (Real.log y)^2) := by
    intro k hk
    have ⟨hkle, hkhi⟩ := Finset.mem_Icc.mp hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hphi : 0 < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (show 0 < k by omega)
    have hGpos : 0 < G k := lt_of_lt_of_le (by positivity) (hG k hk)
    have hlow : 0 < c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2 := by positivity
    have hInv : 1 / G k ≤ 1 / (c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2) :=
      one_div_le_one_div_of_le hlow (hG k hk)
    have hEq : 1 / (c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2) =
        ((k : ℝ) / (k.totient : ℝ))^2 / (c * (Real.log y)^2) := by
      field_simp [ne_of_gt hkpos, ne_of_gt hphi, ne_of_gt hc, ne_of_gt hlog]

    rw [hEq] at hInv
    exact hInv
  have hsumrecip : (∑ k ∈ Finset.Icc 1 K, 1 / G k) ≤
      (1 / (c * (Real.log y)^2)) *
        (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) / (k.totient : ℝ))^2) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 K,
          ((k : ℝ) / (k.totient : ℝ))^2 / (c * (Real.log y)^2) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hrecip k hk
      _ = ∑ k ∈ Finset.Icc 1 K, (1 / (c * (Real.log y)^2)) * ((k : ℝ) / (k.totient : ℝ))^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hratio := mean_totient_ratio_sq_le K
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (X / G k + E) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hA k hk
    _ = X * (∑ k ∈ Finset.Icc 1 K, 1 / G k) + (K : ℝ) * E := by
      rw [Finset.sum_add_distrib]
      have hfirst : (∑ k ∈ Finset.Icc 1 K, X / G k) = X * (∑ k ∈ Finset.Icc 1 K, 1 / G k) := by
        calc
          _ = ∑ k ∈ Finset.Icc 1 K, X * (1 / G k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = _ := by rw [Finset.mul_sum]
      rw [hfirst]
      simp
    _ ≤ X * ((1 / (c * (Real.log y)^2)) *
          (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) / (k.totient : ℝ))^2)) + (K : ℝ) * E := by
      simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left hsumrecip hX) ((K : ℝ) * E)
    _ ≤ X * ((1 / (c * (Real.log y)^2)) * ((K : ℝ) * Real.exp 6)) +
          (K : ℝ) * E := by
      have hC : 0 ≤ 1 / (c * (Real.log y)^2) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hratio hC
      have hscaledX := mul_le_mul_of_nonneg_left hscaled hX
      have hadd := add_le_add_right hscaledX ((K : ℝ) * E)
      simpa [mul_assoc, add_comm] using hadd
    _ = Real.exp 6 * (K : ℝ) * X / (c * (Real.log y)^2) + (K : ℝ) * E := by ring


theorem exists_good_from_cardinality {P B : Finset ℕ} (hB : B ⊆ P)
    (hcard : B.card < P.card) : ∃ p ∈ P, p ∉ B := by
  by_contra h
  push Not at h
  have hPB : P ⊆ B := by intro p hp; exact h p hp
  have : P = B := Finset.Subset.antisymm hPB hB
  simp [this] at hcard







theorem exists_good_prime_from_pair_count {P B : Finset ℕ} (hB : B ⊆ P)
    (X c y E : ℝ) (K : ℕ)
    (hCheb : c * X / Real.log X ≤ (P.card : ℝ))
    (hBad : (B.card : ℝ) ≤ Real.exp 6 * (K : ℝ) * X / (c * (Real.log y)^2) + (K : ℝ) * E)
    (hGap : Real.exp 6 * (K : ℝ) * X / (c * (Real.log y)^2) + (K : ℝ) * E <
      c * X / Real.log X) : ∃ p ∈ P, p ∉ B := by
  apply exists_good_from_cardinality hB
  have hcardR : (B.card : ℝ) < (P.card : ℝ) := lt_of_le_of_lt hBad (lt_of_lt_of_le hGap hCheb)
  exact_mod_cast hcardR





theorem sum_pair_upper_on_subset {K : ℕ} (J : Finset ℕ)
    (hJ : J ⊆ Finset.Icc 1 K) (X c y E : ℝ) (G A : ℕ → ℝ)
    (hX : 0 ≤ X) (hc : 0 < c) (hy : 1 < y) (hE : 0 ≤ E)
    (hG : ∀ k ∈ J,
      c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2 ≤ G k)
    (hA : ∀ k ∈ J, A k ≤ X / G k + E) :
    (∑ k ∈ J, A k) ≤
      Real.exp 6 * (K : ℝ) * X / (c * (Real.log y)^2) + (K : ℝ) * E := by
  let D : ℕ → ℝ := fun k => c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2
  let G' : ℕ → ℝ := fun k => if k ∈ J then G k else D k
  let A' : ℕ → ℝ := fun k => if k ∈ J then A k else 0
  have hGpos : ∀ k ∈ Finset.Icc 1 K, 0 < G' k := by
    intro k hk
    have ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hphi : 0 < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (show 0 < k by omega)
    have hlog : 0 < Real.log y := Real.log_pos hy
    by_cases hmem : k ∈ J
    · have hlower := hG k hmem
      simpa [G', hmem] using (lt_of_lt_of_le (by positivity) hlower)
    · simp [G', hmem, D]
      positivity
  have hG' : ∀ k ∈ Finset.Icc 1 K,
      c * ((k.totient : ℝ) / (k : ℝ))^2 * (Real.log y)^2 ≤ G' k := by
    intro k hk
    by_cases hmem : k ∈ J
    · simpa [G', hmem] using hG k hmem
    · simp [G', hmem, D]
  have hA' : ∀ k ∈ Finset.Icc 1 K, A' k ≤ X / G' k + E := by
    intro k hk
    by_cases hmem : k ∈ J
    · simpa [A', G', hmem] using hA k hmem
    · simp [A', G', hmem]
      have hpos : 0 < D k := by
        dsimp [D]
        have ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
        have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hphi : 0 < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (show 0 < k by omega)
        have hlog : 0 < Real.log y := Real.log_pos hy
        positivity
      positivity
  have hsum := sum_pair_upper_from_totient_lower (K := K) X c y E G' A' hX hc hy hG' hA'
  have hsumEq : (∑ k ∈ Finset.Icc 1 K, A' k) = ∑ k ∈ J, A k := by
    calc
      _ = ∑ k ∈ J, A' k := (Finset.sum_subset hJ (by
        intro k hk hkn
        simp [A', hkn])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [A', hk]
  rw [← hsumEq]
  exact hsum









end MathGacha
