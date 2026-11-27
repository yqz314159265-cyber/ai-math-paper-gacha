import Gacha.MaskedPrimorial
import Gacha.AbelPrefix
import Gacha.PrimorialScreen

namespace MathGacha

/-- Convert a sparse modulus estimate at one endpoint into a double-log
bound for the size of its cyclotomic witness. -/
theorem sparseModulusLogLog {A : ℝ} (hA : 1/2<A) :
    ∃ c : ℝ, 1/2<c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M p : ℕ, 1<M → 1<p → p≤M^M →
      Real.log M ≤ c*N+Real.log 4*Real.sqrt N → Real.log (Real.log p)<A*(N-1 : ℕ) := by
  obtain ⟨c,hc,hcA⟩ := exists_between hA
  obtain ⟨b,hcb,hbA⟩ := exists_between hcA
  let L := Real.log 4
  have hL : 0<L := Real.log_pos (by norm_num)
  have hb : 0<b := by linarith
  let e := (A-b)/(2*b)
  have he : 0<e := div_pos (by linarith) (by positivity)
  have heB : e*b=(A-b)/2 := by dsimp [e]; field_simp
  have hgap : 0<A-(1+e)*b := by nlinarith
  obtain ⟨Q,hQ⟩ := exists_nat_gt ((L/(b-c))^2)
  obtain ⟨R,hR⟩ := exists_nat_gt ((A-1-Real.log e)/(A-(1+e)*b))
  refine ⟨c,hc,max (max Q R) 2,?_⟩
  intro N hN M p hM hp hbound hl
  have hNpos : 0≤(N:ℝ) := Nat.cast_nonneg _
  have hNs := Real.sq_sqrt hNpos
  have hQN : (Q:ℝ)≤N := by exact_mod_cast (show Q≤N by omega)
  have hRN : (R:ℝ)≤N := by exact_mod_cast (show R≤N by omega)
  have ht := Real.sqrt_nonneg (N:ℝ)
  have hsmall : L/(b-c)≤Real.sqrt N := by
    by_contra! hh
    have he' := sq_lt_sq' (by linarith : -(L/(b-c))<Real.sqrt N) hh
    nlinarith [hQ.trans_le hQN]
  have hmul := (div_le_iff₀ (sub_pos.mpr hcb)).mp hsmall
  have haux := mul_le_mul_of_nonneg_right hmul ht
  have hlinear : Real.log M ≤ b*N := by change Real.log M ≤ c*N+L*Real.sqrt N at hl; nlinarith
  have hmr : 1<(M:ℝ) := by exact_mod_cast hM
  have hmpos : 0<(M:ℝ) := by positivity
  have hlog := Real.log_pos hmr
  have hpow := Real.log_le_log (by exact_mod_cast (show 0<p by omega))
    (show (p:ℝ)≤(M:ℝ)^M by exact_mod_cast hbound)
  rw [Real.log_pow] at hpow
  have hpp := Real.log_le_log (Real.log_pos (by exact_mod_cast hp)) hpow
  rw [Real.log_mul hmpos.ne' hlog.ne'] at hpp
  have hh := Real.log_le_sub_one_of_pos (mul_pos he hlog)
  rw [Real.log_mul he.ne' hlog.ne'] at hh
  have hmain := mul_le_mul_of_nonneg_left hlinear (show 0≤1+e by linarith)
  have hn := (div_lt_iff₀ hgap).mp (hR.trans_le hRN)
  rw [Nat.cast_sub (by omega : 1≤N),Nat.cast_one]
  linarith

/-- Arbitrarily large prime indices admit every denominator above one half
in the superlinear least-factor bound. -/
theorem leastFactorLogLogHalf {A : ℝ} (hA : 1/2<A) (B : ℕ) :
    ∃ p>B, p.Prime ∧ (p:ℝ)*Real.log (Real.log p)<A*((Nat.fib p).minFac:ℝ) := by
  obtain ⟨c,hc,Q,hQ⟩ := sparseModulusLogLog hA
  let H := max B 6+1
  obtain ⟨N,hN,hθ⟩ := quarterThetaFrequentlyBelow hc (max Q (H^2))
  have hsq : H≤N.sqrt := Nat.le_sqrt'.mpr (le_trans (le_max_right _ _) hN)
  have hm : H≤maskedModulus N := by
    apply (hsq.trans le_primorial_self).trans
    exact Nat.le_mul_of_pos_left _ (maskedResidueProduct_pos N)
  have hHB : B<H := by dsimp [H]; omega
  have hH6 : 6<H := by dsimp [H]; omega
  have hN6 : 6<N := (hH6.trans_le hsq).trans_le (Nat.sqrt_le_self _)
  obtain ⟨p,hp,hmod,hmp,hbound⟩ := exists_prime_modEq_one_with_bound (show 3≤maskedModulus N by omega)
  have hlog : Real.log (maskedModulus N) ≤ c*N+Real.log 4*Real.sqrt N := by
    have hh := maskedModulus_log_bound N
    change thetaOneModFour N < c*N at hθ
    linarith
  have hLL := hQ N ((le_max_left _ _).trans hN) _ p (by omega) hp.one_lt hbound hlog
  have hm' : p ≡ 1 [MOD maskedModulus ((N-1)+1)] := by rwa [Nat.sub_add_cancel (by omega)]
  have hl := leastFactorBoundOnMaskedClass (K:=N-1) (by omega) hp (by omega) hm'
  have hreal : ((N-1:ℕ):ℝ)*p<((Nat.fib p).minFac:ℝ) := by exact_mod_cast hl
  have hpos : (0:ℝ)<p := by exact_mod_cast hp.pos
  refine ⟨p,by omega,hp,?_⟩
  linarith [mul_lt_mul_of_pos_left hLL hpos,mul_lt_mul_of_pos_left hreal (show 0<A by linarith)]

end MathGacha
