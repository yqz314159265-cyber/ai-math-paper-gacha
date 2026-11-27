import Gacha.DicksonTests

namespace MathGacha
open Polynomial

/-- Scaling the variable and parameter together scales each Dickson value homogeneously. -/
theorem dicksonScaleEval {R : Type*} [CommRing R] (a c x : R) (n : ℕ) :
    (dickson 1 (c^2*a) n).eval (c*x) = c^n*(dickson 1 a n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C, h0, h1]
    rw [pow_add c n 2, pow_succ c n]
    ring

/-- At odd half-degree, absorbing the square root of minus one gives a polynomial
of degree m with the fixed rational target 1. -/
theorem oddHalfDicksonRootIff {R : Type*} [Field R] (m : ℕ) (ho : Odd m)
    (i : R) (hi : i^2=-1) :
    (∃ z : R, (dickson 1 1 (2*m)).eval z = -3) ↔
    ∃ x : R, (dickson 1 (-1) m).eval x = 1 := by
  have hs (t x : R) (ht : t^2=-1) :
      (dickson 1 1 m).eval (t*x)=t^m*(dickson 1 (-1) m).eval x := by
    simpa [ht] using dicksonScaleEval (-1) t x m
  have ht2 (t : R) (ht : t^2=-1) : (t^m)^2=-1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,ht,ho.neg_one_pow]
  have shift (z : R) : (dickson 1 1 (2*m)).eval z =
      ((dickson 1 1 m).eval z)^2-2 := by
    rw [dickson_one_one_mul, eval_comp, dickson_two]
    simp
    ring
  constructor
  · rintro ⟨z,hz⟩
    rw [shift] at hz
    let t := (dickson 1 (1:R) m).eval z
    have ht : t^2=-1 := by dsimp [t]; linear_combination hz
    let x := -t*z
    have hx : t*x=z := by dsimp [x]; linear_combination -z*ht
    have hv := hs t x ht
    rw [hx] at hv
    change t=t^m*(dickson 1 (-1) m).eval x at hv
    have he := congrArg (fun a : R => a^2) hv
    simp only [mul_pow,ht,ht2 t ht] at he
    have hr : ((dickson 1 (-1) m).eval x)^2=1 := by linear_combination he
    rcases sq_eq_one_iff.mp hr with h|h
    · exact ⟨x,h⟩
    · refine ⟨-x,?_⟩
      have hn := dicksonScaleEval (-1:R) (-1) x m
      simpa [ho.neg_one_pow,h] using hn
  · rintro ⟨x,hx⟩
    refine ⟨i*x,?_⟩
    rw [shift,hs i x hi,hx,mul_one,ht2 i hi]
    ring

/-- For every inert neighbor q=2mp−1 with m odd, test a half-degree polynomial. -/
theorem inertDivisorIffHalfDegree {p q m : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hq : q.Prime) (hq5 : 5<q) (hc : q%5=2 ∨ q%5=3) (he : q+1=2*m*p) (ho : Odd m) :
    q ∣ Nat.fib p ↔ ∃ x : ZMod q, (dickson 1 (-1) m).eval x = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hn : neighborIndex q=2*m*p := by simp [neighborIndex,hc,he]
  have hfour : q%4=1 := by
    obtain ⟨a,ha⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨b,hb⟩ := ho
    rw [ha,hb] at he
    ring_nf at he
    omega
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=q)).mpr (by omega)
  rw [primeDivisorIffDickson hp hq hq5,hn,Nat.mul_div_cancel _ hp.pos,
    and_iff_right (dvd_mul_left p (2*m))]
  exact oddHalfDicksonRootIff m ho i (by simpa [pow_two] using hi.symm)

end MathGacha
