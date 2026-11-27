import Gacha.EffectiveSieve

namespace MathGacha

/-- For each coefficient above log(4), the double logarithm of every admissible
cyclotomic witness is below that coefficient times K for all sufficiently large K. -/
theorem primorialLogLogBound {A : ℝ} (hA : Real.log 4 < A) :
    ∃ N : ℕ, ∀ K ≥ N, ∀ p : ℕ, 1<p →
      p ≤ (primorial (K+1))^(primorial (K+1)) → Real.log (Real.log p) < A*K := by
  let c : ℝ := Real.log 4
  have hc : 0<c := Real.log_pos (by norm_num)
  let e := (A-c)/(2*c)
  have he : 0<e := div_pos (by linarith) (by positivity)
  have hec : e*c=(A-c)/2 := by dsimp [e]; field_simp
  let b := (1+e)*c
  have hb : b<A := by dsimp [b]; nlinarith [hec]
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-1-Real.log e)/(A-b))
  refine ⟨max N 4,?_⟩
  intro K hK p hp hbound
  let M := primorial (K+1)
  have hM : 1<M := lt_of_lt_of_le (by omega : 1<K+1) le_primorial_self
  have hMr : 1<(M:ℝ) := by exact_mod_cast hM
  have hmpos : 0<(M:ℝ) := by linarith
  have hlogM := Real.log_pos hMr
  have hLp := Real.log_le_log (by exact_mod_cast (show 0<p by omega))
    (show (p:ℝ)≤(M:ℝ)^M by exact_mod_cast hbound)
  rw [Real.log_pow] at hLp
  have hpp := Real.log_le_log (Real.log_pos (by exact_mod_cast hp)) hLp
  rw [Real.log_mul hmpos.ne' hlogM.ne'] at hpp
  have hh := Real.log_le_sub_one_of_pos (mul_pos he hlogM)
  rw [Real.log_mul he.ne' hlogM.ne'] at hh
  have hMpow : (M:ℝ) ≤ (4:ℝ)^(K+1) := by exact_mod_cast primorial_le_four_pow (K+1)
  have hLC := Real.log_le_log hmpos hMpow
  rw [Real.log_pow] at hLC
  push_cast at hLC
  change Real.log (M:ℝ) ≤ ((K:ℝ)+1)*c at hLC
  have hC := mul_le_mul_of_nonneg_left hLC (show 0≤1+e by linarith)
  have hnle : (N:ℝ)≤K := by exact_mod_cast (show N≤K by omega)
  have hlarge := (div_lt_iff₀ (sub_pos.mpr hb)).mp (hN.trans_le hnle)
  change (1+e)*c-1-Real.log e < K*(A-(1+e)*c) at hlarge
  linarith

/-- Arbitrarily large witnesses come from a primorial modulus. -/
theorem leastFactorLogLogPrimorial {A : ℝ} (hA : Real.log 4 < A) (B : ℕ) :
    ∃ p > B, p.Prime ∧ (p:ℝ)*Real.log (Real.log p) < A*((Nat.fib p).minFac : ℝ) := by
  obtain ⟨N,hN⟩ := primorialLogLogBound hA
  let K := max (max B N) 5
  let M := primorial (K+1)
  have hK : 5 ≤ K := le_max_right _ _
  have hB : B ≤ K := (le_max_left B N).trans (le_max_left _ _)
  have hn : N ≤ K := (le_max_right B N).trans (le_max_left _ _)
  have hM : K+1 ≤ M := le_primorial_self
  obtain ⟨p,hp,hmod,hMp,hbound⟩ := exists_prime_modEq_one_with_bound (show 3 ≤ M by omega)
  have hlow := leastFactorAtSmallPrimeCongruences (by omega : 4≤K) hp (by omega) (fun r hr hle =>
    (hr.dvd_primorial_iff.mpr hle).trans hmod.symm.dvd')
  have hlog := hN K hn p hp.one_lt hbound
  have hreal : (K:ℝ)*p < ((Nat.fib p).minFac : ℝ) := by exact_mod_cast hlow
  have ha : 0<A := (Real.log_pos (by norm_num : (1:ℝ)<4)).trans hA
  have pp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  refine ⟨p,by omega,hp,?_⟩
  linarith [mul_lt_mul_of_pos_left hlog pp, mul_lt_mul_of_pos_left hreal ha]

end MathGacha
