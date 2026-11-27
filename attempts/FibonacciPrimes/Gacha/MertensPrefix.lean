import Gacha.AbelZeroPair
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Stirling

open Finset Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt

namespace MathGacha

/-- The finite sum of logarithms, reorganised by divisors. -/
theorem factorialLogAsMangoldt (N : ℕ) :
    Real.log (N.factorial:ℝ)=∑ n ∈ Ioc 0 N, vonMangoldt n*(↑(N/n):ℝ) := by
  have hc := sum_Ioc_mul_zeta_eq_sum vonMangoldt N
  rw [vonMangoldt_mul_zeta] at hc
  rw [← hc]
  change Real.log (N.factorial:ℝ)=∑ n ∈ Ioc 0 N, Real.log n
  clear hc
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _),Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity),ih,add_comm]

noncomputable def mangoldtHarmonic (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, vonMangoldt n/n

/-- The rounding error in replacing floor(N/n) by N/n is at most ψ(N). -/
theorem mangoldtHarmonicFloorBounds (N : ℕ) :
    Real.log (N.factorial:ℝ) ≤ N*mangoldtHarmonic N ∧
    N*mangoldtHarmonic N ≤ Real.log (N.factorial:ℝ)+Chebyshev.psi N := by
  have he : (N:ℝ)*mangoldtHarmonic N=∑ n ∈ Ioc 0 N, vonMangoldt n*((N:ℝ)/n) := by
    unfold mangoldtHarmonic
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [he,factorialLogAsMangoldt]
  constructor
  · exact sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left Nat.cast_div_le (vonMangoldt_nonneg (n:=n)))
  · have hpsi : Chebyshev.psi (N:ℝ)=∑ n ∈ Ioc 0 N, vonMangoldt n := by simp [Chebyshev.psi]
    rw [hpsi,← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    have hp := (mem_Ioc.mp hn).1
    have hpos : 0<(n:ℝ) := by exact_mod_cast hp
    have hh : (N:ℝ) < ((N/n:ℕ)+1:ℝ)*n := by exact_mod_cast (Nat.mul_comm n (N/n+1) ▸ Nat.lt_mul_div_succ N hp)
    have hdiv := (div_lt_iff₀ hpos).mpr hh
    nlinarith only [mul_le_mul_of_nonneg_left hdiv.le (vonMangoldt_nonneg (n:=n))]

/-- A uniform additive error in the first Mertens estimate for Λ. -/
theorem mangoldtHarmonicLogBounds {N : ℕ} (hn : 0<N) :
    Real.log N-1≤mangoldtHarmonic N ∧
    mangoldtHarmonic N≤Real.log N+(Real.log 4+4) := by
  have hpos : 0<(N:ℝ) := by exact_mod_cast hn
  obtain ⟨hl,hu⟩ := mangoldtHarmonicFloorBounds N
  have hs := Stirling.le_log_factorial_stirling hn.ne'
  have hnlog := Real.log_nonneg (show 1≤(N:ℝ) by exact_mod_cast hn)
  have hpi := Real.log_nonneg (show 1≤2*Real.pi by linarith [Real.pi_gt_three])
  have hf := Real.log_le_log (show 0<(N.factorial:ℝ) by positivity)
    (show (N.factorial:ℝ)≤(N:ℝ)^N by exact_mod_cast N.factorial_le_pow)
  rw [Real.log_pow] at hf
  have hpsi := Chebyshev.psi_le_const_mul_self hpos.le
  constructor
  · apply le_of_mul_le_mul_left _ hpos
    linarith
  · apply le_of_mul_le_mul_left _ hpos
    nlinarith

/-- The finite Mertens sum over primes, including its upper endpoint. -/
noncomputable def primeMertensPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if n.Prime then Real.log n/n else 0

/-- Removing higher prime powers changes the Mangoldt sum by a bounded amount. -/
theorem primeMertensPrefixLogBounds :
    ∃ C : ℝ, ∀ (N : ℕ), 0<N → Real.log N-C≤primeMertensPrefix N ∧
      primeMertensPrefix N≤Real.log N+(Real.log 4+4) := by
  let t (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n)/n
  have ht (n : ℕ) : 0≤t n := by
    dsimp [t]
    split_ifs <;> positivity [vonMangoldt_nonneg (n:=n)]
  have hsum : Summable t := by
    have he (n : ℕ) : residueClass (0:ZMod 1) n=vonMangoldt n := by
      simp [residueClass,Subsingleton.elim (n:ZMod 1) 0]
    simpa only [he] using summable_residueClass_non_primes_div (0:ZMod 1)
  refine ⟨1+∑' n,t n,?_⟩
  intro N hN
  have hmass := hsum.sum_le_tsum (Ioc 0 N) (fun n _ => ht n)
  have h0 := sum_nonneg (s:=Ioc 0 N) (fun n _ => ht n)
  obtain ⟨hl,hu⟩ := mangoldtHarmonicLogBounds hN
  have hsplit : mangoldtHarmonic N=primeMertensPrefix N+∑ n ∈ Ioc 0 N,t n := by
    unfold mangoldtHarmonic primeMertensPrefix
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hp : n.Prime <;> simp [t,hp,vonMangoldt_apply_prime]
  constructor <;> linarith

/-- First Mertens asymptotic for primes with logarithmic weight. -/
theorem tendsto_primeMertensPrefix :
    Tendsto (fun N : ℕ => primeMertensPrefix N/Real.log N) atTop (𝓝 1) := by
  obtain ⟨C,hC⟩ := primeMertensPrefixLogBounds
  have hg : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ N : ℕ in atTop, -C≤primeMertensPrefix N-Real.log N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    linarith [(hC N (by omega)).1]
  have hu : ∀ᶠ N : ℕ in atTop, primeMertensPrefix N-Real.log N≤Real.log 4+4 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    linarith [(hC N (by omega)).2]
  have h := (tendsto_bdd_div_atTop_nhds_zero hb hu hg).add (tendsto_const_nhds (x:= (1:ℝ)))
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog := Real.log_pos (show 1<(N:ℝ) by exact_mod_cast (show 1<N by omega))
  change (primeMertensPrefix N-Real.log N)/Real.log N+1=primeMertensPrefix N/Real.log N
  field_simp
  ring

end MathGacha
