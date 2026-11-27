import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Adjoin.Field
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic

namespace MathGacha

open Polynomial

/-- The image of `ZMod q` in its algebraic closure is exactly the roots of `X^q - X`. -/
theorem finiteField_image_iff_frobenius_fixed
    (q : ℕ) [Fact q.Prime] {K : Type*} [Field K] [Algebra (ZMod q) K]
    [IsAlgClosure (ZMod q) K] (x : K) :
    (∃ z : ZMod q, algebraMap (ZMod q) K z = x) ↔ x ^ q = x := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [← map_pow, ZMod.pow_card]
  · intro hx
    have hxroot : aeval x (X ^ q - X : (ZMod q)[X]) = 0 := by
      simp [aeval_X_pow, aeval_X, hx]
    have hmin : minpoly (ZMod q) x ∣ (X ^ q - X : (ZMod q)[X]) :=
      minpoly.dvd (ZMod q) x hxroot
    have hpolySplit : (X ^ q - X : (ZMod q)[X]).Splits :=
      GaloisField.splits_zmod_X_pow_sub_X q
    have hpolyNe : (X ^ q - X : (ZMod q)[X]) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod q) (Fact.out : q.Prime).one_lt
    have hminSplit :
        ((minpoly (ZMod q) x).map (algebraMap (ZMod q) (ZMod q))).Splits := by
      simpa using hpolySplit.of_dvd hpolyNe hmin
    have hxint : IsIntegral (ZMod q) x :=
      (Algebra.IsAlgebraic.isAlgebraic (R := ZMod q) x).isIntegral
    exact hxint.mem_range_algebraMap_of_minpoly_splits hminSplit

/-- Every element of an algebraically closed field is a trace `u + u⁻¹`. -/
theorem exists_unit_with_trace {E : Type*} [Field E] [IsAlgClosed E] (z : E) :
    ∃ u : E, u ≠ 0 ∧ u + u⁻¹ = z := by
  let P : E[X] := X ^ 2 - C z * X + 1
  have hQ : (X ^ 2 - C z * X).degree = 2 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · simp
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le z) (by norm_num)
  have hdeg : P.degree ≠ 0 := by
    have hP : P = (X ^ 2 - C z * X) + 1 := by simp [P]
    have h1 : (1 : E[X]).degree < (X ^ 2 - C z * X).degree := by
      rw [hQ]
      norm_num
    rw [hP, Polynomial.degree_add_eq_left_of_degree_lt h1]
    rw [hQ]
    norm_num
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root P hdeg
  have hu' : u ^ 2 - z * u + 1 = 0 := by simpa [P] using hu
  have hu0 : u ≠ 0 := by
    intro hu0
    norm_num [hu0] at hu'
  refine ⟨u, hu0, ?_⟩
  field_simp [hu0]
  linear_combination hu'

/-- Two nonzero elements have the same inverse trace exactly when they are equal
or mutual inverses. -/
theorem inverseTrace_eq_iff_eq_or_inv {E : Type*} [Field E] {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x = y⁻¹ := by
  constructor
  · intro h
    have hpoly : (x - y) * (x * y - 1) = 0 := by
      field_simp [hx, hy] at h
      linear_combination h
    rcases mul_eq_zero.mp hpoly with hxy | hxy
    · exact Or.inl (sub_eq_zero.mp hxy)
    · right
      have : x * y = 1 := sub_eq_zero.mp hxy
      field_simp [hy]
      simpa [mul_comm] using this
  · rintro (rfl | hxy)
    · rfl
    · subst x
      rw [inv_inv]
      ring

end MathGacha
