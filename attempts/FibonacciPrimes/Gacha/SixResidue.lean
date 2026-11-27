import Gacha.SixthCubic
import Gacha.IndexResidue

namespace MathGacha

/-- At an odd index the triple-angle formula for Fibonacci values holds
in every prime residue field of characteristic greater than five. -/
theorem fibTripleOddResidue {p q : ℕ} (hp : Odd p) (hq : q.Prime) (hq5 : 5<q) :
    (Nat.fib (3*p) : ZMod q) = (Nat.fib p : ZMod q)*(5*(Nat.fib p : ZMod q)^2-3) := by
  have : Fact q.Prime := ⟨hq⟩
  let E := AlgebraicClosure (ZMod q)
  obtain ⟨a,b,ha,hb,hs,hdisc,hne⟩ := fibRootsAtPrime (q:=q) (by omega) (by omega)
  have hprod : a*b=-1 := by linear_combination a*hs-ha
  have hpab : a^p*b^p=-1 := by rw [← mul_pow,hprod,hp.neg_one_pow]
  have hsmall := fibPowerDifference ha hb p
  have hbig := fibPowerDifference ha hb (3*p)
  rw [Nat.mul_comm 3 p,pow_mul,pow_mul] at hbig
  have hcube : (a^p)^3-(b^p)^3 = (a^p-b^p)^3-3*(a^p-b^p) := by
    linear_combination 3*(a^p-b^p)*hpab
  have he : (Nat.fib (3*p) : E) = (Nat.fib p : E)*(5*(Nat.fib p : E)^2-3) := by
    apply mul_left_cancel₀ hne
    rw [Nat.mul_comm 3 p,hbig,hcube,← hsmall,← hdisc]
    ring
  apply (algebraMap (ZMod q) E).injective
  simpa only [map_mul,map_sub,map_natCast,map_pow,map_ofNat] using he

/-- In the inert third position a nonzero Fibonacci residue has precisely
specified square, even when the index is only assumed odd. -/
theorem sixInertResidueAlternatives {p q : ℕ} (hp : Odd p) (hq : q.Prime)
    (hq5 : 5<q) (he : q+1=6*p) (hclass : q%5=2 ∨ q%5=3) :
    (Nat.fib p : ZMod q)=0 ∨ 5*(Nat.fib p : ZMod q)^2=3 := by
  have : Fact q.Prime := ⟨hq⟩
  have ht : Odd (3*p) := (by decide : Odd 3).mul hp
  have hh := fibHalfNeighborSquare ht hq (by omega) (show q+1=2*(3*p) by omega)
  have hsg := (legendreSym_five_eq_neg_one_iff (q:=q) (by omega)).mpr hclass
  rw [fib_prime_index_eq_legendre hq (by omega) (by omega),hsg] at hh
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hh := Nat.le_of_dvd (by decide : 0<2) ((ZMod.natCast_eq_zero_iff 2 q).mp hz)
    omega
  have hz : (Nat.fib (3*p) : ZMod q)=0 := by
    have hmul : 2*(Nat.fib (3*p) : ZMod q)^2=0 := by simpa using hh
    exact (pow_eq_zero_iff (by decide : 2≠0)).mp ((mul_eq_zero.mp hmul).resolve_left h2)
  rw [fibTripleOddResidue hp hq hq5] at hz
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp

end MathGacha
