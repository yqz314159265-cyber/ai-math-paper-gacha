import Gacha.PairCountWitness
import Gacha.ConcretePairCount
import Mathlib.Analysis.Complex.ExponentialBounds

namespace MathGacha

theorem fibonacciSieveExpSix : Real.exp 6≤729 := by
  have hh := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 6
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  exact hh

/-- An explicit finite numerical gap. V will be a power of two with
log V proportional to K. The cubic-denominator sieve uses X=V^64. -/
theorem exponentialSieveGap {V K E : ℝ} (hv : 2≤V) (hk : 0≤K) (hkv : K≤V)
    (hscale : 8192*Real.exp 6*K≤Real.log V) (herr : E≤32*V^24) :
    8*Real.exp 6*K*(V^64+1)/(Real.log V)^2 + 2*K*E + V <
      (Real.log 2/2)*V^64/Real.log (V^64) := by
  let L := Real.log V
  have hv0 : 0<V := by linarith
  have hL : 0<L := Real.log_pos (by linarith)
  have hLv : L≤V := Real.log_le_self hv0.le
  have hX : 1≤V^64 := one_le_pow₀ (by linarith)
  have hX0 : 0<V^64 := pow_pos hv0 _
  have hre : 0≤Real.exp 6 := (Real.exp_pos _).le
  have hmain : 8*Real.exp 6*K*(V^64+1)/L^2≤V^64/(512*L) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hL) (by positivity)]
    calc
      _ ≤ (8*Real.exp 6*K)*(2*V^64)*(512*L) := by gcongr; linarith
      _ = (8192*Real.exp 6*K)*(V^64*L) := by ring
      _ ≤ L*(V^64*L) := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := by ring
  have he : 2*K*E+V≤65*V^25 := by
    have hV1 : V≤V^25 := le_self_pow₀ (by linarith) (by decide)
    calc
      _ ≤ 2*V*(32*V^24)+V := add_le_add_left
        (mul_le_mul_of_nonneg_left herr (by positivity) |>.trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkv (by norm_num)) (by positivity))) _
      _ ≤ 2*V*(32*V^24)+V^25 := by gcongr
      _ = _ := by ring
  have hcalc : (33280:ℝ)<V^38 :=
    (show (33280:ℝ)<2^38 by norm_num).trans_le (pow_le_pow_left₀ (by norm_num) hv 38)
  have hsmall : 65*V^25 < V^64/(512*L) := by
    rw [lt_div_iff₀ (by positivity)]
    calc
      _ ≤ (65*V^25)*(512*V) := by gcongr
      _ = 33280*V^26 := by ring
      _ < V^38*V^26 := mul_lt_mul_of_pos_right hcalc (pow_pos hv0 _)
      _ = _ := by ring
  have hhalf : (1:ℝ)/2≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hrat : V^64/(512*L)+V^64/(512*L) ≤ (Real.log 2/2)*V^64/(64*L) := by
    calc
      _ = ((1:ℝ)/2/2)*V^64/(64*L) := by ring
      _ ≤ _ := by gcongr
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  change _ < (Real.log 2/2)*V^64/(64*L)
  exact (by linarith only [hmain,he,hsmall] :
    8*Real.exp 6*K*(V^64+1)/L^2+2*K*E+V < V^64/(512*L)+V^64/(512*L)) |>.trans_le hrat


/-- Extract the logarithmic moving threshold with an explicit constant
from the averaged two-slope count. -/
theorem extractLogRoughFibIndices
    (hcount : ∀ U K : ℕ, 2≤U →
      ((smallFactorIndices ((U+1)^64) U K).card:ℝ) ≤
        8*Real.exp 6*(K:ℝ)*(((U+1:ℕ):ℝ)^64+1)/(Real.log (U+1:ℕ))^2+
        2*K*finitePairError (U^2)) (B : ℕ) :
    ∃ p>B, p.Prime ∧ (p:ℝ)*Real.log p/1073741824 < ((Nat.fib p).minFac:ℝ) := by
  let K := B+6
  let V : ℕ := 2^(16777216*K)
  let U := V-1
  have hK : 6≤K := by dsimp [K]; omega
  have hKV : K<V := calc
    _ < 2^K := Nat.lt_two_pow_self
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega : K≤16777216*K)
  have hu : U+1=V := by dsimp [U]; omega
  have hU : 2≤U := by omega
  have hB : B≤U := by dsimp [K] at hKV; omega
  have hvpow : (V:ℝ)=(2:ℝ)^(16777216*K) := by dsimp [V]; push_cast; rfl
  have hlogV : Real.log (V:ℝ)=16777216*(K:ℝ)*Real.log 2 := by
    rw [hvpow,Real.log_pow]
    push_cast
    ring
  have hK0 : 0≤(K:ℝ) := Nat.cast_nonneg K
  have hsc : 8192*Real.exp 6*(K:ℝ)≤Real.log V := by
    rw [hlogV]
    have h0 : 8192*Real.exp 6≤16777216*Real.log 2 := by
      linarith only [fibonacciSieveExpSix,Real.log_two_gt_d9]
    nlinarith only [mul_le_mul_of_nonneg_right h0 hK0]
  have hEV : finitePairError (U^2)≤32*(V:ℝ)^24 :=
    (finitePairError_sq_le (by omega : 1≤U)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg U) (Nat.cast_le.mpr (show U≤V by omega)) 24) (by norm_num))
  have hgap := exponentialSieveGap (by exact_mod_cast (show 2≤V by omega)) hK0
    (by exact_mod_cast hKV.le) hsc hEV
  have hsmall := hcount U K hU
  rw [hu] at hsmall
  have hm : max B (max U 5)+1=V := by omega
  have hV6 : 6≤V^64 := (show 6≤V by omega).trans (Nat.le_self_pow (by decide) _)
  obtain ⟨p,hpX,hpB,hp,hq⟩ := existsLargeGoodFibIndexOfBound (y:=U) (K:=K) (B:=B) hV6 (by
    rw [hm,show ((V^64:ℕ):ℝ)=(V:ℝ)^64 by exact Nat.cast_pow ..]
    exact (add_le_add_left hsmall (V:ℝ)).trans_lt hgap)
  have hlogp := Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpX : (p:ℝ)≤(V:ℝ)^64)
  rw [Real.log_pow,hlogV] at hlogp
  have htwo : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogp' : Real.log p≤1073741824*(K:ℝ) := by
    norm_num only [Nat.cast_ofNat] at hlogp
    nlinarith only [hlogp,mul_le_mul_of_nonneg_left htwo hK0]
  have hmul := mul_le_mul_of_nonneg_left hlogp' (Nat.cast_nonneg p)
  refine ⟨p,by omega,hp,?_⟩
  apply lt_of_le_of_lt _ (show (K:ℝ)*p<((Nat.fib p).minFac:ℝ) by exact_mod_cast hq)
  nlinarith only [hmul]

end MathGacha
