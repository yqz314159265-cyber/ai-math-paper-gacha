import Gacha.DicksonTests
import Gacha.Drobot

namespace MathGacha

open Polynomial

/-- The degree-six condition is a quadratic equation in the odd cubic trace. -/
theorem dicksonSixShiftEval {R : Type*} [CommRing R] (z : R) :
    (dickson 1 (1 : R) 6).eval z + 3 = (z^3-3*z)^2 + 1 := by
  norm_num [dickson, eval_add, eval_sub, eval_mul]
  ring

/-- The shifted sixth Dickson polynomial has a root exactly when the fixed
cubic X³+3X−1 does, over a field containing a square root of minus one. -/
theorem sixthDicksonRootIffCubic {R : Type*} [Field R] (i : R) (hi : i^2 = -1) :
    (∃ z : R, (dickson 1 1 6).eval z = -3) ↔ ∃ x : R, x^3+3*x=1 := by
  constructor
  · rintro ⟨z,hz⟩
    let t := z^3-3*z
    have ht : t^2=-1 := by
      have hh := dicksonSixShiftEval z
      rw [hz] at hh
      dsimp [t]
      linear_combination -hh
    refine ⟨t*z,?_⟩
    calc
      (t*z)^3+3*(t*z) = -t*(z^3-3*z) := by linear_combination t*z^3*ht
      _ = 1 := by change -t*t=1; linear_combination -ht
  · rintro ⟨x,hx⟩
    refine ⟨i*x,?_⟩
    have ht : (i*x)^3-3*(i*x) = -i := by linear_combination i*x^3*hi - i*hx
    have hh := dicksonSixShiftEval (i*x)
    rw [ht,neg_sq,hi] at hh
    linear_combination hh

/-- Any nontrivial divisor below the square of the common lower factor bound is prime. -/
theorem primeDivisorBelowLinearSquare {p q : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hq : 1<q) (hs : q<(2*p-1)^2) (hd : q ∣ Nat.fib p) : q.Prime := by
  by_contra hc
  have hl := fibLeastFactorLinearBound hp hp5 (Nat.minFac_prime (by omega : q≠1))
    ((Nat.minFac_dvd q).trans hd)
  have hle : 2*p-1≤q.minFac := by omega
  have hm : (2*p-1)^2 ≤ q.minFac^2 := by gcongr
  have hh := Nat.minFac_sq_le_self (by omega) hc
  omega

/-- At q=6p−1 the fixed cubic, primality of q, and the index class determine divisibility. -/
theorem sixBoundaryDvdIffCubic {p q : ℕ} (hp : p.Prime) (hp5 : 5<p) (he : q+1=6*p) :
    q ∣ Nat.fib p ↔ q.Prime ∧ (p%5=3 ∨ p%5=4) ∧ ∃ x : ZMod q, x^3+3*x=1 := by
  have hg : 5<q := by omega
  have hbound : q<(2*p-1)^2 := by
    have hh : 2*p-1+1=2*p := by omega
    nlinarith [Nat.mul_le_mul_left (2*p-1) (show 7≤2*p-1 by omega)]
  have idx (h : p%5=3 ∨ p%5=4) : neighborIndex q=6*p := by
    have hq5 : q%5=2 ∨ q%5=3 := by omega
    simp [neighborIndex,hq5,he]
  have test (hq : q.Prime) : hasDicksonRoot q 6 ↔ ∃ x : ZMod q, x^3+3*x=1 := by
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=q)).mpr (by omega)
    exact sixthDicksonRootIffCubic i (by simpa [pow_two] using hi.symm)
  have hd6 : 6*p/p=6 := Nat.mul_div_cancel _ hp.pos
  constructor
  · intro hd
    have hq := primeDivisorBelowLinearSquare hp hp5 (by omega) hbound hd
    obtain ⟨hdp,hr⟩ := (primeDivisorIffDickson hp hq hg).mp hd
    have hclass : p%5=3 ∨ p%5=4 := by
      by_contra hc
      have hn : ¬(q%5=2 ∨ q%5=3) := by omega
      simp [neighborIndex,hn] at hdp
      have htwo : p ∣ 2 := by
        have hd6p : p ∣ 6*p := dvd_mul_left _ _
        have hm := Nat.dvd_sub hd6p hdp
        rwa [show 6*p-(q-1)=2 by omega] at hm
      have := Nat.le_of_dvd (by decide : 0<2) htwo
      omega
    rw [idx hclass,hd6] at hr
    exact ⟨hq,hclass,(test hq).mp hr⟩
  · rintro ⟨hq,hclass,hx⟩
    apply (primeDivisorIffDickson hp hq hg).mpr
    rw [idx hclass,hd6]
    exact ⟨dvd_mul_left _ _,(test hq).mpr hx⟩

end MathGacha
