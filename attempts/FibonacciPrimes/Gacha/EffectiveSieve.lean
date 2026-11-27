import Gacha.Drobot
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

open Polynomial

namespace MathGacha

/-- An explicit prime in the progression `1 mod M`, obtained as the least
prime divisor of `Φ_M(M)`. The order argument follows Mathlib's
`Nat.exists_prime_gt_modEq_one`; evaluation of the cyclotomic divisibility gives the upper bound. -/
theorem exists_prime_modEq_one_with_bound {M : ℕ} (hM : 3 ≤ M) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD M] ∧ M < p ∧ p ≤ M ^ M := by
  let T := ((Polynomial.cyclotomic M ℤ).eval (M : ℤ)).natAbs
  have hTgt : 1 < T := by
    have h := Polynomial.sub_one_lt_natAbs_cyclotomic_eval
      (n := M) (q := M) (by omega) (by omega)
    dsimp [T]
    omega
  let p := Nat.minFac T
  have hp : p.Prime := Nat.minFac_prime (by dsimp [p]; omega)
  have : Fact p.Prime := ⟨hp⟩
  have hroot : IsRoot (Polynomial.cyclotomic M (ZMod p))
      (Nat.castRingHom (ZMod p) M) := by
    have hcast : ((M : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) M) := by simp
    rw [IsRoot.def, ← Polynomial.map_cyclotomic_int M (ZMod p), Polynomial.eval_map,
      Nat.coe_castRingHom, ← Int.cast_natCast, hcast, Polynomial.eval₂_hom,
      Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact_mod_cast (Nat.minFac_dvd T)
  have hpb : ¬ p ∣ M :=
    hp.coprime_iff_not_dvd.1 (Polynomial.coprime_of_root_cyclotomic (by omega) hroot).symm
  have hcast0 : (M : ZMod p) ≠ 0 := by
    intro hz
    exact hpb ((ZMod.natCast_eq_zero_iff M p).1 hz)
  have horder : M = orderOf (M : ZMod p) := by
    have : NeZero (M : ZMod p) := ⟨hcast0⟩
    exact (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  have horderdiv : orderOf (M : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hpb)
  have hMdiv : M ∣ p - 1 := by rw [horder]; exact horderdiv
  have hcong : p ≡ 1 [MOD M] := (Nat.modEq_iff_dvd' hp.pos).2 hMdiv |>.symm
  have hpleT : p ≤ T := by
    dsimp [p]
    exact Nat.minFac_le (by omega)
  have hcyclDiv : (Polynomial.cyclotomic M ℤ).eval (M : ℤ) ∣
      Polynomial.eval (M : ℤ) (X ^ M - 1 : ℤ[X]) := by
    rcases Polynomial.cyclotomic.dvd_X_pow_sub_one M ℤ with ⟨g, hg⟩
    rw [hg, Polynomial.eval_mul]
    exact dvd_mul_right _ _
  have hpow1 : 1 ≤ M ^ M := Nat.one_le_pow M M (by omega)
  have hcastEval : ((M ^ M - 1 : ℕ) : ℤ) = (M : ℤ) ^ M - 1 := by
    rw [Nat.cast_sub hpow1]
    simp
  have hTdiv : T ∣ M ^ M - 1 := by
    have heval : (Polynomial.cyclotomic M ℤ).eval (M : ℤ) ∣
        ((M ^ M - 1 : ℕ) : ℤ) := by
      simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, hcastEval] using hcyclDiv
    dsimp [T]
    exact Int.dvd_natCast.mp heval
  have hpowgt : 1 < M ^ M := Nat.one_lt_pow (by omega) (by omega)
  have hTle : T ≤ M ^ M - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hpowgt) hTdiv
  have hpgt : M < p := by
    have hpminus : 0 < p - 1 := Nat.sub_pos_of_lt hp.two_le
    have hMle : M ≤ p - 1 := Nat.le_of_dvd hpminus hMdiv
    omega
  refine ⟨p, hp, hcong, hpgt, ?_⟩
  exact hpleT.trans (hTle.trans (Nat.sub_le _ _))

/-- The residue one covers all slopes at least three. The exceptional lower
slopes are eliminated by the interval below 4p+1 and the condition modulo five. -/
theorem leastFactorAtSmallPrimeCongruences {K p : ℕ} (hK : 4 ≤ K) (hp : p.Prime) (hp5 : 5 < p)
    (hsmall : ∀ r : ℕ, r.Prime → r ≤ K+1 → r ∣ p-1) : K*p < (Nat.fib p).minFac := by
  have hpmod : p%5=1 := by have := hsmall 5 (by decide) (by omega); omega
  let q := (Nat.fib p).minFac
  have hf := Nat.le_fib_self (n:=p) (by omega)
  have hqp : q.Prime := Nat.minFac_prime (by omega)
  have hqf : q ∣ Nat.fib p := Nat.minFac_dvd _
  have hgap := (leastFactorGap hp hp5).mpr (by omega)
  change 4*p+1 ≤ q at hgap
  by_contra! hbad
  obtain ⟨k,hk,hK',hform⟩ := divisorProgressionUpTo hp hp5 hqp hqf hbad
  have hk3 : 3 ≤ k := by
    by_contra! hsmall
    interval_cases k <;> rcases hform with hh | hh <;> omega
  have hdiv (d : ℕ) (hd : 2 ≤ d) (hdK : d ≤ K+1) : d.minFac ∣ k*(p-1) :=
    dvd_mul_of_dvd_right (hsmall d.minFac (Nat.minFac_prime (by omega))
      ((Nat.minFac_le (by omega)).trans hdK)) k
  have hmul : k*p=k+k*(p-1) := by
    calc k*p = k*(1+(p-1)) := congrArg (k*·) (by omega)
         _ = _ := by ring
  have hlt : k < k*p := by simpa using Nat.mul_lt_mul_of_pos_left (show 1<p by omega) hk
  rcases hform with hplus | hminus
  · have hd : (k+1).minFac ∣ q := by
      rw [hplus,show k*p+1=(k+1)+k*(p-1) by omega]
      exact dvd_add (Nat.minFac_dvd _) (hdiv _ (by omega) (by omega))
    have hh := (Nat.dvd_prime_two_le hqp (Nat.minFac_prime (by omega)).two_le).mp hd
    have hle := Nat.minFac_le (show 0<k+1 by omega)
    omega
  · have hd : (k-1).minFac ∣ q := by
      rw [hminus,show k*p-1=(k-1)+k*(p-1) by omega]
      exact dvd_add (Nat.minFac_dvd _) (hdiv _ (by omega) (by omega))
    have hh := (Nat.dvd_prime_two_le hqp (Nat.minFac_prime (by omega)).two_le).mp hd
    have hle := Nat.minFac_le (show 0<k-1 by omega)
    omega

/-- The full lcm class supplies all the required prime congruences. -/
theorem leastFactorInOneClass {K p : ℕ} (hK : 4 ≤ K) (hp : p.Prime) (hp5 : 5 < p)
    (hmod : p ≡ 1 [MOD Nat.lcmUpto (K+1)]) : K*p < (Nat.fib p).minFac := by
  apply leastFactorAtSmallPrimeCongruences hK hp hp5
  intro r hr hrK
  have hd : r ∣ Nat.lcmUpto (K+1) :=
    Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨hr.one_le,hrK⟩)
  exact hd.trans hmod.symm.dvd'

/-- A convenient integer constant in the Chebyshev bound for the sieve modulus. -/
theorem logLcmUpper (n : ℕ) : Real.log (Nat.lcmUpto n) ≤ 7*(n:ℝ) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  apply (Chebyshev.psi_le_const_mul_self (by positivity)).trans
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  gcongr
  linarith

/-- An explicit double logarithm bound on the index in the cyclotomic construction. -/
theorem loglogBoundForLcmWitness {p K : ℕ} (hK : 4 ≤ K) (hp : 1 < p)
    (hbound : p ≤ (Nat.lcmUpto (K+1))^(Nat.lcmUpto (K+1))) :
    Real.log (Real.log p) ≤ 20*K := by
  let M := Nat.lcmUpto (K+1)
  have hd : K+1 ∣ M := Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
  have hM : 1 < M := lt_of_lt_of_le (by omega : 1<K+1) (Nat.le_of_dvd (Nat.lcmUpto_pos _) hd)
  have hMpos : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hMone : (1:ℝ)<M := by exact_mod_cast hM
  have hlog := Real.log_pos hMone
  have hboundR : (p:ℝ) ≤ (M:ℝ)^M := by exact_mod_cast hbound
  have hLp := Real.log_le_log (by exact_mod_cast (show 0<p by omega)) hboundR
  rw [Real.log_pow] at hLp
  have hlogp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hpp := Real.log_le_log hlogp hLp
  rw [Real.log_mul (ne_of_gt hMpos) (ne_of_gt hlog)] at hpp
  have hpsi : Real.log (M:ℝ) ≤ 7*((K:ℝ)+1) := by
    simpa [M] using logLcmUpper (K+1)
  have hK' : (4:ℝ)≤K := by exact_mod_cast hK
  linarith [Real.log_le_self hlog.le]

/-- Arbitrarily large prime indices have a least prime factor above a fixed,
explicit superlinear function of the actual index. -/
theorem arbitrarilyLargePrimeLeastFactorLogLog (B : ℕ) :
    ∃ p > B, p.Prime ∧ (p : ℝ)*Real.log (Real.log p) < 20*((Nat.fib p).minFac : ℝ) := by
  let K := max B 5
  let M := Nat.lcmUpto (K+1)
  have hK : 5 ≤ K := le_max_right _ _
  have hd : K+1 ∣ M := Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
  have hM : K+1 ≤ M := Nat.le_of_dvd (Nat.lcmUpto_pos _) hd
  obtain ⟨p,hp,hmod,hMp,hupper⟩ := exists_prime_modEq_one_with_bound (show 3 ≤ M by omega)
  have hl := leastFactorInOneClass (by omega : 4 ≤ K) hp (by omega) hmod
  have he := loglogBoundForLcmWitness (by omega : 4 ≤ K) hp.one_lt hupper
  have hb : B ≤ K := le_max_left _ _
  refine ⟨p,by omega,hp,?_⟩
  have hreal : (K : ℝ)*p < ((Nat.fib p).minFac : ℝ) := by exact_mod_cast hl
  have hp0 : 0 ≤ (p:ℝ) := by positivity
  linarith [mul_le_mul_of_nonneg_left he hp0]

/-- The full least-common-multiple construction imposes an exponential cost in the cutoff. -/
theorem oneClassSizeLimit {p K : ℕ} (hp : Nat.lcmUpto (K+1) < p) :
    2^(K+1) < (K+2)*p := by
  exact (Chebyshev.two_pow_le_mul_lcmUpto (K+1)).trans_lt
    (Nat.mul_lt_mul_of_pos_left hp (by omega))

/-- A polynomial upper bound for primes in these residue classes would replace
the double logarithm of the unconditional construction by a single logarithm. -/
theorem logGainOfPolynomialProgressionBound (L : ℕ)
    (hbound : ∀ M : ℕ, 3 ≤ M → ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD M] ∧ M < p ∧ p ≤ M^L)
    (B : ℕ) :
    ∃ p > B, p.Prime ∧ (p : ℝ)*Real.log p < 14*(L+1 : ℝ)*((Nat.fib p).minFac : ℝ) := by
  let K := max B 5
  let M := Nat.lcmUpto (K+1)
  have hK : 5 ≤ K := le_max_right _ _
  have hd : K+1 ∣ M := Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
  have hM : K+1 ≤ M := Nat.le_of_dvd (Nat.lcmUpto_pos _) hd
  obtain ⟨p,hp,hmod,hMp,hupper⟩ := hbound M (by omega)
  have hrough := leastFactorInOneClass (by omega : 4 ≤ K) hp (by omega) hmod
  have hb : B ≤ K := le_max_left _ _
  refine ⟨p,by omega,hp,?_⟩
  have hupperR : (p : ℝ) ≤ (M:ℝ)^L := by exact_mod_cast hupper
  have hl := Real.log_le_log (by exact_mod_cast hp.pos) hupperR
  rw [Real.log_pow] at hl
  have hpsi : Real.log (M:ℝ) ≤ 7*((K:ℝ)+1) := by
    simpa [M] using logLcmUpper (K+1)
  have hK' : (5:ℝ)≤K := by exact_mod_cast hK
  have hMlog : Real.log M ≤ 14*K := by linarith
  have hL0 : 0 ≤ (L:ℝ) := by positivity
  have hlp : Real.log p ≤ L*(14*(K:ℝ)) := hl.trans (mul_le_mul_of_nonneg_left hMlog hL0)
  have hp0 : 0 ≤ (p:ℝ) := by positivity
  have hfreal : (K : ℝ)*p < ((Nat.fib p).minFac : ℝ) := by exact_mod_cast hrough
  have hm := mul_lt_mul_of_pos_left hfreal (show (0:ℝ)<14*((L:ℝ)+1) by positivity)
  have hkp : 0 ≤ (K:ℝ)*p := by positivity
  linarith [mul_le_mul_of_nonneg_left hlp hp0]

end MathGacha
