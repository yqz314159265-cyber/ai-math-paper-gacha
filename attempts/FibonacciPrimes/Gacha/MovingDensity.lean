import Gacha.FiniteBadLogWeight
import Mathlib.Data.Nat.Find

open Filter Topology

namespace MathGacha

/-- For finite estimates valid in the limit at each fixed cutoff, one can choose
a single nondecreasing cutoff tending to infinity along the whole sequence. -/
theorem existsGrowingCutoff {F : ℕ → ℕ → ℝ} {L : ℝ}
    (h : ∀ k, Tendsto (F k) atTop (𝓝 L)) :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
        Tendsto (fun X => F (f X) X) atTop (𝓝 L) := by
  classical
  have hs (k : ℕ) : ∃ T : ℕ, ∀ X≥T, dist (F k X) L < 1/((k:ℝ)+1) :=
    eventually_atTop.1 ((Metric.tendsto_nhds.mp (h k)) _ (by positivity))
  choose T hT using hs
  let f (X : ℕ) := Nat.findGreatest (fun k => T k≤X) X
  have hfmono : Monotone f := fun _ _ hxy => Nat.findGreatest_mono (fun _ hh => hh.trans hxy) hxy
  have hfoo : Tendsto f atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k,eventually_ge_atTop (T k)] with X hx ht
    exact Nat.le_findGreatest hx ht
  refine ⟨f,hfmono,hfoo,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  have hr : Tendsto (fun X => 1/((f X:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hfoo
  filter_upwards [eventually_ge_atTop (T 0),hr.eventually_lt_const hε] with X hx he
  exact (hT (f X) X (Nat.findGreatest_spec (P:=fun k => T k≤X) (Nat.zero_le X) hx)).trans he

noncomputable def movingFibIndexLogWeight (f : ℕ → ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 X, if n.Prime ∧ f n*n<(Nat.fib n).minFac then Real.log n/n else 0

/-- For the same unbounded cutoff f, both the uniform cutoff f(X) in the prefix
and the individual cutoff f(p) retain full logarithmic weight. -/
theorem existsGrowingFullWeightFibSieve :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      Tendsto (fun X => goodFibIndexLogWeight (f X) X/Real.log X) atTop (𝓝 1) ∧
      Tendsto (fun X => movingFibIndexLogWeight f X/Real.log X) atTop (𝓝 1) := by
  obtain ⟨f,hm,ht,hu⟩ := existsGrowingCutoff goodFibIndexLogWeight_div_log_tendsto_one
  refine ⟨f,hm,ht,hu,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hu tendsto_primeMertensPrefix
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with X hX
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1≤X by omega)))
    apply Finset.sum_le_sum
    intro n hn
    have hh := hm (Finset.mem_Ioc.mp hn).2
    have hn1 := (Finset.mem_Ioc.mp hn).1
    have hlog : 0≤Real.log (n:ℝ)/(n:ℝ) := div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) (by positivity)
    change (if n.Prime ∧ f X*n<_ then _ else 0) ≤ (if n.Prime ∧ f n*n<_ then _ else 0)
    split_ifs with h₁ h₂ h₃
    · rfl
    · exact (h₂ ⟨h₁.1,(Nat.mul_le_mul_right n hh).trans_lt h₁.2⟩).elim
    · exact hlog
    · rfl
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with X hX
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1≤X by omega)))
    apply Finset.sum_le_sum
    intro n hn
    have hn1 := (Finset.mem_Ioc.mp hn).1
    have hlog : 0≤Real.log (n:ℝ)/(n:ℝ) := div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) (by positivity)
    change (if n.Prime ∧ f n*n<_ then _ else 0) ≤ (if n.Prime then _ else 0)
    split_ifs with h₁ h₂ h₃
    · rfl
    · exact (h₂ h₁.1).elim
    · exact hlog
    · rfl

end MathGacha
