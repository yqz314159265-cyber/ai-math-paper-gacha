import Gacha.DicksonTests
import Gacha.DicksonRootCount

namespace MathGacha

open Polynomial

/-- The degree of the polynomial gcd with Frobenius counts distinct roots in the base field. -/
theorem frobeniusGcdDegree {q : ℕ} [Fact q.Prime] (P : (ZMod q)[X]) :
    (gcd P (X^q-X)).natDegree = Nat.card {z : ZMod q // P.eval z=0} := by
  classical
  let Q : (ZMod q)[X] := X^q-X
  let g := gcd P Q
  have hQ : Q ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (ZMod q) (Fact.out : q.Prime).one_lt
  have hd : g ∣ Q := gcd_dvd_right _ _
  have hg : g ≠ 0 := fun h => hQ (by simpa [h] using hd)
  have hs := (GaloisField.splits_zmod_X_pow_sub_X q).of_dvd hQ hd
  have hle := Polynomial.roots.le_of_dvd hQ hd
  have hroots : Q.roots=Finset.univ.val := by
    simpa [Q, ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod q)
  rw [hroots] at hle
  have hnod : g.roots.Nodup := Multiset.nodup_of_le hle Finset.univ.nodup
  have hmem (z : ZMod q) : z ∈ g.roots.toFinset ↔ P.eval z=0 := by
    rw [Multiset.mem_toFinset, mem_roots hg, ← dvd_iff_isRoot]
    change X-C z ∣ gcd P Q ↔ _
    rw [dvd_gcd_iff]
    have hqroot : X-C z ∣ Q := dvd_iff_isRoot.mpr (by simp [Q, IsRoot, ZMod.pow_card])
    rw [and_iff_left hqroot, dvd_iff_isRoot, IsRoot.def]
  let e : ↥g.roots.toFinset ≃ {z : ZMod q // P.eval z=0} := Equiv.subtypeEquivRight hmem
  change g.natDegree = _
  rw [hs.natDegree_eq_card_roots, ← Multiset.toFinset_card_of_nodup hnod]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_congr e

/-- Euclid's algorithm for the two polynomials has only two possible output degrees. -/
theorem dicksonFrobeniusGcdDegree {p q : ℕ} [Fact q.Prime] (hp : p.Prime)
    (hq5 : 5 < q) (hd : p ∣ neighborIndex q) :
    (gcd (dickson 1 (1 : ZMod q) (neighborIndex q / p) + 3) (X^q-X)).natDegree =
      if q ∣ Nat.fib p then neighborIndex q / p else 0 := by
  rw [frobeniusGcdDegree, ← natCard_dickson_roots_eq_if_fib_divides hp hq5 hd]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro z
  simp only [eval_add, eval_ofNat]
  exact eq_neg_iff_add_eq_zero.symm

end MathGacha
