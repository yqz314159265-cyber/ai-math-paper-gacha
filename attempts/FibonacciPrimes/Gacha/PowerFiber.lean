import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

open Polynomial

namespace MathGacha

/-- In an algebraic closure of characteristic `q`, each nonzero value has
exactly `k` distinct `k`th roots when `q` does not divide `k`. -/
theorem pow_fiber_card
    (E : Type*) [Field E] [IsAlgClosed E] (q k : ℕ) [CharP E q]
    (hk : 0 < k) (hdiv : ¬ q ∣ k) (r : E) (hr : r ≠ 0) :
    (Polynomial.nthRootsFinset k r).card = k := by
  classical
  let f : E[X] := X ^ k - C r
  have hf : f ≠ 0 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    simp [f] at hdeg
    omega
  have hkcast : (k : E) ≠ 0 := by
    intro hz
    exact hdiv ((CharP.cast_eq_zero_iff E q k).mp hz)
  have hmult (a : E) : f.rootMultiplicity a ≤ 1 := by
    by_contra h
    have hgt : 1 < f.rootMultiplicity a := by omega
    have hroot := (one_lt_rootMultiplicity_iff_isRoot hf).mp hgt
    have ha : a ^ k = r := by
      have heval : a ^ k - r = 0 := by
        simpa [f, IsRoot, eval_sub, eval_C, eval_pow, eval_X] using hroot.1
      exact sub_eq_zero.mp heval
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_pow hk.ne'] at ha
      exact hr ha.symm
    have hd : f.derivative.IsRoot a := hroot.2
    change f.derivative.eval a = 0 at hd
    simp [f, derivative_sub, derivative_X_pow] at hd
    have hpow0 : a ^ (k - 1) ≠ 0 := pow_ne_zero _ ha0
    have hkc : (k : E) ≠ 0 := hkcast
    exact (mul_ne_zero hkc hpow0) (by simpa using hd)
  have hroots : f.Splits := IsAlgClosed.splits f
  have hcard : Multiset.card f.roots = k := by
    have hdegree : f.natDegree = k := by simp [f]
    rw [← hroots.natDegree_eq_card_roots, hdegree]
  have hnodup : f.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    rw [count_roots]
    exact hmult a
  have hset : (Polynomial.nthRootsFinset k r).card = Multiset.card f.roots := by
    rw [Polynomial.nthRootsFinset_def, Polynomial.nthRoots]
    simpa [f] using Multiset.toFinset_card_of_nodup hnodup
  exact hset.trans hcard

/-- The subtype of `k`th roots of a nonzero `r` in an algebraic closure has
cardinality `k`, when the characteristic does not divide `k`. -/
theorem natCard_pow_fiber
    (E : Type*) [Field E] [IsAlgClosed E] (q k : ℕ) [CharP E q]
    (hk : 0 < k) (hdiv : ¬ q ∣ k) (r : E) (hr : r ≠ 0) :
    Nat.card {u : E // u ^ k = r} = k := by
  classical
  let S := Polynomial.nthRootsFinset k r
  have hS : (S : Set E) = {u : E | u ^ k = r} := by
    simpa [S] using (Polynomial.nthRootsFinset_toSet hk r)
  have hfinite : ({u : E | u ^ k = r}).Finite := by
    rw [← hS]
    exact S.finite_toSet
  let _ : Fintype {u : E // u ^ k = r} := hfinite.fintype
  let _ : Fintype {u : E // u ∈ S} := Fintype.ofFinite _
  let e : {u : E // u ^ k = r} ≃ {u : E // u ∈ S} := Equiv.setCongr hS.symm
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {u : E // u ^ k = r} = Fintype.card {u : E // u ∈ S} :=
      Fintype.card_congr e
    _ = S.card := Fintype.card_coe S
    _ = k := by simpa [S] using pow_fiber_card E q k hk hdiv r hr

/-- If `q` is prime, it cannot divide `k` when `k*p` is a neighbor of `q`.
The hypotheses are stated as equalities in `Nat`, avoiding subtraction. -/
theorem not_dvd_multiplier_of_neighbor
    {q k p : ℕ} (hq : q.Prime) (hkp : k * p = q - 1 ∨ k * p = q + 1) :
    ¬ q ∣ k := by
  intro hqk
  have hqkp : q ∣ k * p := dvd_mul_of_dvd_left hqk p
  rcases hkp with hminus | hplus
  · have hbad : q ∣ q - 1 := by simpa [hminus] using hqkp
    rcases (Nat.dvd_sub_self_left).mp hbad with hz | hle
    · omega
    · exact (not_le_of_gt hq.one_lt) hle
  · have hbad : q ∣ q + 1 := by simpa [hplus] using hqkp
    have h1 : q ∣ 1 := Nat.dvd_add_self_left.mp hbad
    exact (not_le_of_gt hq.one_lt) (Nat.le_of_dvd Nat.one_pos h1)

end MathGacha
