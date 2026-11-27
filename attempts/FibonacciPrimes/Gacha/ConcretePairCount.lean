import Gacha.PrimePairQuant
import Gacha.PairCountBridge

open Finset

namespace MathGacha

/-- Over a prime field the polynomial has its zero root and, exactly when
the slope is a unit, the additional root −k⁻¹. -/
theorem pairRootCount_exact (k r : ℕ) (hr : r.Prime) :
    (pairRootResidues k r).card=(if r∣k then 1 else 2) := by
  let : Fact r.Prime := ⟨hr⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  rw [← pairZModRoots_card_eq_pairRootResidues]
  by_cases h : r∣k
  · have hz := (ZMod.natCast_eq_zero_iff k r).mpr h
    have hroots : pairZModRoots k r={0} := by ext x; simp [pairZModRoots,hz]
    simp [hroots,h]
  · have hk : (k:ZMod r)≠0 := fun hh => h ((ZMod.natCast_eq_zero_iff k r).mp hh)
    have hz : (0:ZMod r)≠ -((k:ZMod r)⁻¹) := by simpa only [ne_eq,zero_eq_neg,inv_eq_zero] using hk
    have hroots : pairZModRoots k r = {0, -((k:ZMod r)⁻¹)} := by
      ext x
      simp only [pairZModRoots,mem_filter,mem_univ,true_and,mul_eq_zero,mem_insert,mem_singleton]
      apply or_congr Iff.rfl
      constructor
      · intro he
        calc
          x = (k:ZMod r)⁻¹*((k:ZMod r)*x) := by rw [← mul_assoc,inv_mul_cancel₀ hk,one_mul]
          _ = _ := by simp [show (k:ZMod r)*x= -1 by linear_combination he]
      · rintro rfl
        simp [mul_inv_cancel₀ hk]
    simp [hroots,h,hz]

theorem actualPairSieveNu_eq (k r : ℕ) (hr : r.Prime) :
    pairSieveNu k r = (if r∣k then (1:ℝ) else 2)/(r:ℝ) := by
  simp only [pairSieveNu,ArithmeticFunction.coe_mk,if_neg hr.ne_zero,pairRootDensity,
    pairRootCount_exact k r hr]
  split <;> norm_num

theorem reflectedPairDenominator_eq {P : ℕ} (hP : Squarefree P) {k : ℕ}
    (hk : 2∣k) (X y : ℕ) :
    pairSelbergDen (pairBoundingSieveEven (reflectedSlope P k) X P (reflectedSlope_even hk) hP) y =
    pairSelbergDen (pairBoundingSieveEven k X P hk hP) y := by
  let s := pairBoundingSieveEven (reflectedSlope P k) X P (reflectedSlope_even hk) hP
  let t := pairBoundingSieveEven k X P hk hP
  change (∑ d∈P.divisors,if d≤y then s.selbergTerms d else 0) =
    ∑ d∈P.divisors,if d≤y then t.selbergTerms d else 0
  apply sum_congr rfl
  intro d hd
  have hdp := (Nat.mem_divisors.mp hd).1
  have hsf := Squarefree.squarefree_of_dvd hdp hP
  have hlocal (r : ℕ) (hr : r∈d.primeFactors) : s.nu r=t.nu r := by
    change pairSieveNu _ r=pairSieveNu k r
    have hpr := Nat.prime_of_mem_primeFactors hr
    simp only [actualPairSieveNu_eq _ _ hpr,
      dvdReflectedSlopeIff (Nat.pos_of_ne_zero hP.ne_zero) ((Nat.dvd_of_mem_primeFactors hr).trans hdp)]
  have hnu : s.nu d=t.nu d := by
    rw [← s.nu_mult.prod_primeFactors hsf,← t.nu_mult.prod_primeFactors hsf]
    exact prod_congr rfl hlocal
  have hg : s.selbergTerms d=t.selbergTerms d := by
    rw [s.selbergTerms_apply,t.selbergTerms_apply,hnu]
    congr 1
    exact prod_congr rfl (fun r hr => by rw [hlocal r hr])
  rw [hg]

noncomputable def finitePairError (y : ℕ) : ℝ :=
  ((y*y+1:ℕ):ℝ)^3 * ((y:ℝ)*(y+1))^2 * (y*y:ℝ)

noncomputable def finitePairDen (k X u y : ℕ) (hk : 2∣k) : ℝ :=
  pairSelbergDen (pairBoundingSieveEven k (X+1) (primorial u) hk (squarefree_primorial _)) y

theorem actualTwoSlopeBound (k X u y : ℕ) (hk : 2∣k) (hy : 1≤y) :
    ((largePlusPairIndices X u k).card:ℝ)+(largeMinusPairIndices X u k).card ≤
    2*(((X+1:ℕ):ℝ)/finitePairDen k X u y hk+finitePairError y) := by
  let P := primorial u
  let j := reflectedSlope P k
  have hj : 2∣j := reflectedSlope_even hk
  have hP : Squarefree P := squarefree_primorial _
  let s := pairBoundingSieveEven k (X+1) P hk hP
  let t := pairBoundingSieveEven j (X+1) P hj hP
  have hkeep (l n : ℕ) (hle : n≤X) : n*(l*n+1)∈pairSupport l (X+1) :=
    mem_image.mpr ⟨n,mem_range.mpr (by omega),rfl⟩
  have hp := largePlusPairIndices_le_siftedSum s X u k (pairPoly_injective k) (fun _ _ => rfl)
    rfl (fun n hn => hkeep k n hn)
  have hm := largeMinusPairIndices_le_siftedSum t X u k (pairPoly_injective j) (fun _ _ => rfl)
    rfl (fun n hn => hkeep j n hn)
  have hbound (l : ℕ) (hl : 2∣l) :
      (pairBoundingSieveEven l (X+1) P hl hP).siftedSum ≤
      ((X+1:ℕ):ℝ)/pairSelbergDen (pairBoundingSieveEven l (X+1) P hl hP) y+finitePairError y :=
    pairSelbergEven_sifted_bound_explicit l X P y hl hP hy
  have hb1 := hp.trans (hbound k hk)
  have hb2 := hm.trans (hbound j hj)
  have he := reflectedPairDenominator_eq hP hk (X+1) y
  change pairSelbergDen t y=pairSelbergDen s y at he
  change _ ≤ ((X+1:ℕ):ℝ)/pairSelbergDen t y+finitePairError y at hb2
  rw [he] at hb2
  rw [two_mul]
  exact add_le_add hb1 hb2

/-- The actual polynomial error in both signs is at most 32 times U^24
at denominator cutoff U². -/
theorem finitePairError_sq_le {U : ℕ} (hU : 1≤U) :
    finitePairError (U^2)≤32*(U:ℝ)^24 := by
  let u : ℝ := U
  have h1 : 1≤u := by dsimp only [u]; exact_mod_cast hU
  have h0 : 0≤u := by positivity
  have h4 : 1≤u^4 := one_le_pow₀ h1
  have h2 : 1≤u^2 := one_le_pow₀ h1
  have hA : u^2*u^2+1≤2*u^4 := by nlinarith only [h4]
  have hB : u^2+1≤2*u^2 := by linarith
  unfold finitePairError
  push_cast
  change (u^2*u^2+1)^3*(u^2*(u^2+1))^2*(u^2*u^2)≤32*u^24
  calc
    _ ≤ (2*u^4)^3*(u^2*(2*u^2))^2*(u^2*u^2) := by gcongr
    _ = _ := by ring

end MathGacha
