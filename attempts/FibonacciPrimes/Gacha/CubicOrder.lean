import Gacha.HalfLucas

namespace MathGacha

/-- A possible composite with certified order d below d³ forces a square
discriminant. The parameters s and t are the two digits of (N−1)/d that
recover the sum and product of the two factor multipliers. -/
theorem primeOfCubicOrder {N d c : ℕ} (hN : 1<N) (hd : 0<d)
    (hform : N=d*c+1) (hsize : N<d^3) (cert : largeOrderCertificate N d)
    (hnosq : ¬ ∃ u : ℕ, (c%d)^2=u^2+4*(c/d)) : N.Prime := by
  by_contra hcomp
  let q := N.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  obtain ⟨b,hqb⟩ := Nat.minFac_dvd N
  change N=q*b at hqb
  have hq1 := hq.one_lt
  have hb1 : 1<b := by
    by_contra! hh
    interval_cases b
    · simp at hqb
      omega
    · simp at hqb
      exact hcomp (hqb ▸ hq)
  obtain ⟨x,hx⟩ := orderDividesPrimeFactorSubOne hd cert hq (show q∣N from ⟨b,hqb⟩)
  have hxq : q=d*x+1 := by omega
  have hqmod : 1 ≡ q [MOD d] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨x,hx⟩
  have hnmod : 1 ≡ N [MOD d] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨c,by omega⟩
  have hbmod : 1 ≡ b [MOD d] := by
    rw [hqb] at hnmod
    simpa using hnmod.trans (hqmod.mul_right b).symm
  obtain ⟨y,hy⟩ := (Nat.modEq_iff_dvd' (by omega)).mp hbmod
  have hyb : b=d*y+1 := by omega
  have hx0 : 0<x := by
    by_contra! h
    have hzero : x=0 := by omega
    simp [hzero] at hxq
    omega
  have hy0 : 0<y := by
    by_contra! h
    have hzero : y=0 := by omega
    simp [hzero] at hyb
    omega
  have hprod : N=(d*x+1)*(d*y+1) := by rw [hqb,hxq,hyb]
  have hc : c=x+y+d*(x*y) := by
    apply Nat.eq_of_mul_eq_mul_left hd
    nlinarith only [hprod,hform]
  have hxy : x+y≤x*y+1 := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero hx0.ne'
    obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero hy0.ne'
    rw [ha,hb]
    nlinarith
  have hs : x+y<d := by
    by_contra! hh
    have h1 := Nat.mul_le_mul_left (d^2) (show d≤x*y+1 by omega)
    have h2 := Nat.mul_le_mul_left d hh
    nlinarith only [h1,h2,hprod,hsize]
  have hm : c%d=x+y := by rw [hc,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hs]
  have ht : c/d=x*y := by rw [hc,Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hs,Nat.zero_add]
  apply hnosq
  rw [hm,ht]
  rcases le_total x y with h|h
  · exact ⟨y-x,by have hz := Nat.sub_add_cancel h; nlinarith only [congrArg (fun z : ℕ => z^2) hz,congrArg (fun z : ℕ => x*z) hz]⟩
  · exact ⟨x-y,by have hz := Nat.sub_add_cancel h; nlinarith only [congrArg (fun z : ℕ => z^2) hz,congrArg (fun z : ℕ => y*z) hz]⟩

/-- A computable discriminant check using only integer division and integer square root. -/
theorem primeOfCubicOrderSqrt {N d c : ℕ} (hN : 1<N) (hd : 0<d)
    (hform : N=d*c+1) (hsize : N<d^3) (cert : largeOrderCertificate N d)
    (hdisc : (c%d)^2<4*(c/d) ∨
      (Nat.sqrt ((c%d)^2-4*(c/d)))^2≠(c%d)^2-4*(c/d)) : N.Prime := by
  apply primeOfCubicOrder hN hd hform hsize cert
  rintro ⟨u,hu⟩
  have heq : (c%d)^2-4*(c/d)=u^2 := by omega
  rcases hdisc with h|h
  · omega
  · rw [heq,Nat.sqrt_eq'] at h
    exact h rfl

end MathGacha
