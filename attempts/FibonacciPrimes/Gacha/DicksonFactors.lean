import Gacha.TraceRoots
import Gacha.Frobenius
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.FieldTheory.Finite.Basic

namespace MathGacha

/-- The ratio of the two Fibonacci roots has trace −3 and detects every Fibonacci zero. -/
theorem fibRatioData {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq5 : q ≠ 5) :
    ∃ r : AlgebraicClosure (ZMod q), r ≠ 0 ∧ r ≠ r⁻¹ ∧ r+r⁻¹ = -3 ∧
      ∀ n : ℕ, q ∣ Nat.fib n ↔ r^n=1 := by
  let E := AlgebraicClosure (ZMod q)
  obtain ⟨a,b,ha,hb,hab,_,hne⟩ := fibRootsAtPrime hq2 hq5
  have hprod : a*b = -1 := by linear_combination a*hab - ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  let r : E := a/b
  have hr : r ≠ 0 := div_ne_zero ha0 hb0
  have hinv : r⁻¹=b/a := by simp [r]
  have htrace : r+r⁻¹ = -3 := by
    rw [hinv]
    change a/b+b/a = -3
    have hA : a/b = -(a^2) := (div_eq_iff hb0).mpr (by linear_combination a * hprod)
    have hB : b/a = -(b^2) := (div_eq_iff ha0).mpr (by linear_combination b * hprod)
    rw [hA,hB]
    linear_combination -(a+b+1)*hab + 2*hprod
  have hdiff : r ≠ r⁻¹ := by
    rw [hinv]
    intro he
    have heq := (div_eq_div_iff hb0 ha0).mp he
    apply hne
    have hzero : (a-b)*(a+b)=0 := by linear_combination heq
    simpa [hab] using hzero
  refine ⟨r, hr, hdiff, htrace, fun n => ?_⟩
  have hd := fibPowerDifference ha hb n
  rw [← CharP.cast_eq_zero_iff E q]
  change (Nat.fib n : E)=0 ↔ (a/b)^n=1
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hb0)]
  constructor
  · intro hz
    exact sub_eq_zero.mp (by simpa [hz] using hd.symm)
  · intro he
    exact (mul_eq_zero.mp (by simpa [he] using hd)).resolve_left hne

/-- For nonzero x, membership in the group of order q−1 is the Frobenius fixed condition. -/
theorem powPredecessorOneIff {E : Type*} [Field E] {x : E} (hx : x ≠ 0) {q : ℕ} (hq : 0 < q) :
    x^(q-1) = 1 ↔ x^q = x := by
  have h := pow_succ x (q-1)
  rw [Nat.sub_add_cancel hq] at h
  rw [h]
  exact ⟨fun h1 => by rw [h1, one_mul], fun h1 => mul_right_cancel₀ hx (h1.trans (one_mul x).symm)⟩

/-- Membership in the group of order q+1 makes Frobenius act by inversion. -/
theorem powSuccessorOneIff {E : Type*} [Field E] {x : E} (hx : x ≠ 0) (q : ℕ) :
    x^(q+1) = 1 ↔ x^q = x⁻¹ := by
  rw [pow_succ]
  constructor
  · intro he
    exact mul_right_cancel₀ hx (he.trans (inv_mul_cancel₀ hx).symm)
  · intro he
    rw [he, inv_mul_cancel₀ hx]

/-- A kth root whose trace is fixed belongs to the same rank branch as its power,
provided the power differs from its inverse. -/
theorem traceBranchLift {E : Type*} [Field E] {u r : E} (hu : u ≠ 0) (hr : r ≠ 0)
    (hsep : r ≠ r⁻¹) {q t k : ℕ} (hq : 0 < q) (ht : t = q-1 ∨ t = q+1)
    (hrt : r^t=1) (hk : u^k=r) (huq : u^q=u ∨ u^q=u⁻¹) : u^t=1 := by
  have hcomm : r^q=(u^q)^k := by rw [← hk, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rcases ht with rfl | rfl
  · apply (powPredecessorOneIff hu hq).mpr
    rcases huq with he | he
    · exact he
    · have hrq := (powPredecessorOneIff hr hq).mp hrt
      rw [hrq, he, inv_pow, hk] at hcomm
      exact (hsep hcomm).elim
  · apply (powSuccessorOneIff hu q).mpr
    rcases huq with he | he
    · have hrq := (powSuccessorOneIff hr q).mp hrt
      rw [hrq, he, hk] at hcomm
      exact (hsep hcomm.symm).elim
    · exact he

/-- At rank modulus t=q±1, divisibility by q becomes a value problem for a Dickson polynomial. -/
theorem fibDivisorIffDicksonRootOfBranch {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    {p k t : ℕ} (hk : 0 < k) (ht : t=q-1 ∨ t=q+1) (hsize : k*p=t)
    (hqt : q ∣ Nat.fib t) :
    q ∣ Nat.fib p ↔ ∃ z : ZMod q, (Polynomial.dickson 1 1 k).eval z = -3 := by
  let f := algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
  have hq : q.Prime := Fact.out
  obtain ⟨r,hr,hrsep,hrtrace,hrdetect⟩ := fibRatioData hq2 hq5
  rw [hrdetect]
  have mapped (z : ZMod q) : f ((Polynomial.dickson 1 1 k).eval z) =
      (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (f z) := by
    rw [← Polynomial.eval_map_apply, Polynomial.map_dickson, map_one]
  have fixed (z : ZMod q) : (f z)^q = f z := by
    rw [← map_pow, ZMod.pow_card]
  have tr_pow (u : AlgebraicClosure (ZMod q)) (hu : u ≠ 0) :
      (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (u+u⁻¹) =
      u^k + (u^k)⁻¹ := by
    simpa only [inv_pow] using Polynomial.dickson_one_one_eval_add_inv u u⁻¹ (mul_inv_cancel₀ hu) k
  constructor
  · intro hzero
    obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq r hk
    have hu0 : u ≠ 0 := by
      intro hh
      exact hr (by simpa [hh, zero_pow hk.ne'] using hu.symm)
    have hut : u^t=1 := by rw [← hsize, pow_mul, hu, hzero]
    have hfix : (u+u⁻¹)^q = u+u⁻¹ := by
      rw [add_pow_char, inv_pow]
      rcases ht with rfl | rfl
      · rw [(powPredecessorOneIff hu0 hq.pos).mp hut]
      · rw [(powSuccessorOneIff hu0 q).mp hut, inv_inv, add_comm]
    obtain ⟨z,hz⟩ := (finiteField_image_iff_frobenius_fixed q (u+u⁻¹)).mpr hfix
    refine ⟨z, f.injective ?_⟩
    rw [mapped, show f z=u+u⁻¹ from hz, tr_pow u hu0, hu, hrtrace]
    simp only [map_neg, map_ofNat]
  · rintro ⟨z,hz⟩
    obtain ⟨w,hw0,hw⟩ := exists_unit_with_trace (f z)
    have hsum : w^k + (w^k)⁻¹ = r+r⁻¹ := by
      rw [← tr_pow w hw0, hw, ← mapped, hz, hrtrace]
      simp only [map_neg, map_ofNat]
    have choose : ∃ u : AlgebraicClosure (ZMod q), u≠0 ∧ u+u⁻¹=f z ∧ u^k=r := by
      rcases (inverseTrace_eq_iff_eq_or_inv (pow_ne_zero _ hw0) hr).mp hsum with h | h
      · exact ⟨w, hw0, hw, h⟩
      · exact ⟨w⁻¹, inv_ne_zero hw0, by rw [inv_inv, add_comm]; exact hw,
          by rw [inv_pow,h]; exact inv_inv r⟩
    obtain ⟨u,hu,huz,huk⟩ := choose
    have huq : (u^q)+(u^q)⁻¹=u+u⁻¹ := by
      calc
        _ = (u+u⁻¹)^q := by rw [add_pow_char, inv_pow]
        _ = f z := by rw [huz, fixed]
        _ = _ := huz.symm
    have hut := traceBranchLift hu hr hrsep hq.pos ht ((hrdetect t).mp hqt) huk
      ((inverseTrace_eq_iff_eq_or_inv (pow_ne_zero _ hu) hu).mp huq)
    rwa [← hsize, pow_mul, huk] at hut

end MathGacha
