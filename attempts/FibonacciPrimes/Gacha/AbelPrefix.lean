import Gacha.AbelSieve
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Filter Topology Finset

namespace MathGacha

/-- A lower bound for all partial sums also bounds every decreasing
nonnegative weighted sum; a fixed initial error costs at most C*w(0). -/
theorem compareWeightedPrefixes (a b w : ℕ → ℝ) (C : ℝ)
    (hw : Antitone w) (hw0 : ∀ n, 0≤w n)
    (h : ∀ n, 0≤C+∑ i ∈ range n,(a i-b i)) (n : ℕ) :
    (∑ i ∈ range n,b i*w i) ≤ C*w 0+∑ i ∈ range n,a i*w i := by
  have bounds (m : ℕ) : (C+∑ i ∈ range m,(a i-b i))*w m ≤
      C*w 0+∑ i ∈ range m,(a i-b i)*w i := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hs := mul_le_mul_of_nonneg_left (hw (Nat.le_succ m)) (h (m+1))
      rw [sum_range_succ] at hs
      rw [sum_range_succ, sum_range_succ]
      linarith
  have hl := (mul_nonneg (h n) (hw0 n)).trans (bounds n)
  simp_rw [sub_mul] at hl
  rw [sum_sub_distrib] at hl
  linarith

noncomputable def abelSeqWeight (s : ℝ) (n : ℕ) := 1/((n:ℝ)+1)^s

theorem abelSeqWeightAntitone {s : ℝ} (hs : 1<s) : Antitone (abelSeqWeight s) := by
  intro a b hab
  have hh : (a:ℝ)+1≤(b:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hab
  exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow (by positivity) hh (by linarith))

theorem abelSeqWeightSum {s : ℝ} (hs : 1<s) :
    (∑' n : ℕ, abelSeqWeight s n) = ∑' n : ℕ, 1/(n:ℝ)^s := by
  have ht := (Real.summable_one_div_nat_rpow.mpr hs).tsum_eq_zero_add
  rw [show (1:ℝ)/(0:ℕ)^s=0 by simp [Real.zero_rpow (by linarith : s≠0)]] at ht
  simpa [abelSeqWeight,Nat.cast_succ] using ht.symm

/-- A normalized Abel limit bounds the lower limit of ordinary averages.
The subsequence conclusion suffices for choosing large sieve parameters. -/
theorem frequentlyLowPrefixOfAbelLimit (a : ℕ → ℝ) (d c : ℝ) (hc : d<c) (hc0 : 0<c)
    (ha : ∀ n, 0≤a n) (hsum : ∀ s : ℝ, 1<s → Summable fun n => a n*abelSeqWeight s n)
    (hlim : Tendsto (fun s : ℝ => (s-1)*∑' n,a n*abelSeqWeight s n) (𝓝[>] 1) (𝓝 d))
    (B : ℕ) : ∃ n≥B, (∑ i ∈ range n, a i)<c*n := by
  by_contra! h
  let C := c*(B:ℝ)
  have hC : 0≤C := by dsimp [C]; positivity
  have hlo (n : ℕ) : 0≤C+∑ i ∈ range n,(a i-c) := by
    rw [sum_sub_distrib]
    simp only [sum_const,card_range,nsmul_eq_mul]
    by_cases hn : B≤n
    · nlinarith [h n hn]
    · have hnR : (n:ℝ)≤B := by exact_mod_cast (by omega : n≤B)
      have hs := Finset.sum_nonneg (s:=range n) (fun i _ => ha i)
      have hh := mul_le_mul_of_nonneg_left hnR hc0.le
      dsimp [C]
      linarith
  have hcomp (s : ℝ) (hs : 1<s) :
      c*∑' n : ℕ, 1/(n:ℝ)^s ≤ C+∑' n,a n*abelSeqWeight s n := by
    rw [← abelSeqWeightSum hs]
    have hsw : Summable (abelSeqWeight s) := by
      have hh := (Real.summable_one_div_nat_rpow.mpr hs).comp_injective (i:=fun n : ℕ => n+1) (by intro n m h; exact Nat.succ_injective h)
      change Summable (fun n : ℕ => 1/((n:ℝ)+1)^s)
      simpa [Function.comp_def,Nat.cast_succ] using hh
    have hyp := (hsw.mul_left c).hasSum.tendsto_sum_nat
    rw [tsum_mul_left] at hyp
    apply le_of_tendsto_of_tendsto' hyp (tendsto_const_nhds.add ((hsum s hs).hasSum.tendsto_sum_nat))
    intro n
    simpa [abelSeqWeight] using compareWeightedPrefixes a (fun _ => c) (abelSeqWeight s) C
      (abelSeqWeightAntitone hs) (fun n => by unfold abelSeqWeight; positivity) hlo n
  have hLeft := tendsto_sub_mul_tsum_nat_rpow.const_mul c
  have hlin : Tendsto (fun s : ℝ => s-1) (𝓝[>] 1) (𝓝 0) := by
    have hid : Tendsto id (𝓝[>] (1:ℝ)) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.sub_const (1:ℝ)
  have hRight := (hlin.mul_const C).add hlim
  have hle : c*1 ≤ 0*C+d := le_of_tendsto_of_tendsto hLeft hRight (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1<s := hs
    have hd := mul_le_mul_of_nonneg_left (hcomp s hs') (by linarith : 0≤s-1)
    change c*((s-1)*_) ≤ (s-1)*C+(s-1)*_
    linarith)
  linarith

/-- The logarithm contributed by a prime congruent to one modulo four. -/
noncomputable def quarterLog (n : ℕ) : ℝ :=
  if n.Prime ∧ n%4=1 then Real.log n else 0

theorem quarterLogWeight (s : ℝ) (n : ℕ) :
    quarterLog (n+1)*abelSeqWeight s n=primeResidueTerm (1 : ZMod 4) s (n+1) := by
  have hcast (t : ℕ) : (t : ZMod 4)=1 ↔ t%4=1 := by
    change (t : ZMod 4)=(1:ℕ) ↔ t%4=1
    exact ZMod.natCast_eq_natCast_iff t 1 4
  have hres :
      ArithmeticFunction.vonMangoldt.residueClass (1:ZMod 4) (n+1) =
        if (n+1)%4=1 then ArithmeticFunction.vonMangoldt (n+1) else 0 := by
    simp only [ArithmeticFunction.vonMangoldt.residueClass,Set.indicator_apply,Set.mem_ofPred_eq,hcast]
  by_cases hp : (n+1).Prime
  · simp [quarterLog, primeResidueTerm, hres,hp,abelSeqWeight,
       ArithmeticFunction.vonMangoldt_apply_prime hp,div_eq_mul_inv]
  · simp [quarterLog,primeResidueTerm,hp]

/-- The class theta sum is less than c*N at arbitrarily large endpoints for every c>1/2. -/
theorem quarterThetaFrequentlyBelow {c : ℝ} (hc : 1/2<c) (B : ℕ) :
    ∃ N≥B, (∑ i ∈ range N,quarterLog (i+1)) < c*N := by
  have hnon (n : ℕ) : 0≤quarterLog (n+1) := by
    unfold quarterLog
    split
    next h => exact Real.log_nonneg (by exact_mod_cast (show 1≤n+1 by omega))
    next => exact le_rfl
  have hsums (s : ℝ) (hs : 1<s) :
      Summable (fun n : ℕ => quarterLog (n+1)*abelSeqWeight s n) := by
    simp_rw [quarterLogWeight]
    exact (summable_primeResidueTerm (1 : ZMod 4) s hs).comp_injective Nat.succ_injective
  apply frequentlyLowPrefixOfAbelLimit _ (1/2) c hc (by linarith) hnon hsums _ B
  have hlim := tendsto_primeResidueClass_abel_weight (a:=(1:ZMod 4)) isUnit_one
  have hphi : Nat.totient 4=2 := by decide
  rw [hphi] at hlim
  have hEq : (fun s : ℝ => (s-1)*primeResidueTsum (1:ZMod 4) s) =ᶠ[𝓝[>] (1:ℝ)]
      (fun s : ℝ => (s-1)*∑' n : ℕ,quarterLog (n+1)*abelSeqWeight s n) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp_rw [quarterLogWeight]
    congr 1
    have h := (summable_primeResidueTerm (1:ZMod 4) s hs).tsum_eq_zero_add
    simpa [primeResidueTsum,show primeResidueTerm (1:ZMod 4) s 0=0 by simp [primeResidueTerm]] using h
  simpa [one_div] using hlim.congr' hEq

end MathGacha
