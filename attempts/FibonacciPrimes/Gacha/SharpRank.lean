import Gacha.IndexResidue
import Mathlib.Data.Nat.Fib.Basic

namespace MathGacha

/-- For a root of `X^2 = X + 1`, its powers encode adjacent Fibonacci numbers. -/
theorem rootPowerFib {K : Type*} [CommRing K] {a : K}
    (ha : a ^ 2 = a + 1) (n : ℕ) :
    a ^ (n + 1) = (Nat.fib (n + 1) : K) * a + Nat.fib n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+1 = n+2 by omega, pow_succ, ih, Nat.fib_add_two]
    rw [add_mul, mul_assoc, ← pow_two, ha, Nat.cast_add]
    ring

/-- The two neighboring Fibonacci numbers at a prime index are selected by the
quadratic character of five. -/
theorem fibNeighborPair {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) :
    (2 : ZMod q) * (Nat.fib (q-1) : ZMod q) = 1 - (legendreSym q 5 : ZMod q) ∧
    (2 : ZMod q) * (Nat.fib (q+1) : ZMod q) = 1 + (legendreSym q 5 : ZMod q) := by
  let K := AlgebraicClosure (ZMod q)
  obtain ⟨a,b,ha,hb,hsum,_,_⟩ := fibRootsAtPrime hq2 hq5
  have hFrob : a^q+b^q=1 := by rw [← add_pow_char, hsum, one_pow]
  have hqpos := hq.pos
  have hidx : q-1+1=q := by omega
  have hrootA := rootPowerFib ha (q-1)
  have hrootB := rootPowerFib hb (q-1)
  rw [hidx] at hrootA hrootB
  have htotal : a^q+b^q = (Nat.fib q : K)*(a+b)+2*(Nat.fib (q-1) : K) := by
    rw [hrootA, hrootB]
    ring
  have hbaseK : (2 : K)*(Nat.fib (q-1) : K)+(Nat.fib q : K)=1 := by
    rw [← hFrob, htotal, hsum]
    ring
  have hbase : (2 : ZMod q)*(Nat.fib (q-1) : ZMod q)+(Nat.fib q : ZMod q)=1 := by
    apply (algebraMap (ZMod q) K).injective
    simpa only [map_add, map_mul, map_natCast, map_one, map_ofNat,
      Nat.cast_add, Nat.cast_mul] using hbaseK
  have hsign : (Nat.fib q : ZMod q)=(legendreSym q 5 : ZMod q) :=
    fib_prime_index_eq_legendre hq hq2 hq5
  have hfirst : (2 : ZMod q)*(Nat.fib (q-1) : ZMod q)=1-(legendreSym q 5 : ZMod q) := by
    rw [← hsign]
    linear_combination hbase
  have hrec := Nat.fib_add_two (n:=q-1)
  have hn : q-1+2=q+1 := by omega
  have hidx' : q-1+1=q := by omega
  have hrecZ : (Nat.fib (q+1) : ZMod q)=(Nat.fib q : ZMod q)+(Nat.fib (q-1) : ZMod q) := by
    simpa [hn, hidx', add_comm] using congrArg (fun n : ℕ => (n : ZMod q)) hrec
  constructor
  · exact hfirst
  · rw [hrecZ]
    rw [← hsign]
    linear_combination hbase

/-- For every prime `q > 5`, the quadratic character selects a neighboring index
at which the Fibonacci number is divisible by `q`. -/
theorem primeDvdNeighborFib {q : ℕ} (hq : q.Prime) (hlarge : 5 < q) :
    q ∣ Nat.fib (if q % 5 = 2 ∨ q % 5 = 3 then q+1 else q-1) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have hq5 : q ≠ 5 := by omega
  have hpair := fibNeighborPair hq hq2 hq5
  have hfive : (5 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 5 := (CharP.cast_eq_zero_iff (ZMod q) q 5).mp hz
    have hqeq : q = 5 := (Nat.dvd_prime_two_le (by decide : Nat.Prime 5) hq.two_le).mp hd
    omega
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp hz
    have hqeq : q = 2 := (Nat.dvd_prime_two_le Nat.prime_two hq.two_le).mp hd
    omega
  rcases legendreSym.eq_one_or_neg_one q (a := 5) (by exact_mod_cast hfive) with hpos | hneg
  · have hres : ¬ (q % 5 = 2 ∨ q % 5 = 3) := by
      intro hr
      have hchar := (legendreSym_five_eq_neg_one_iff hq2).mpr hr
      rw [hpos] at hchar
      norm_num at hchar
    have hmul : (2 : ZMod q) * (Nat.fib (q-1) : ZMod q) = 0 := by
      rw [hpair.1, hpos]
      norm_num
    have hfibzero : (Nat.fib (q-1) : ZMod q)=0 := (mul_eq_zero.mp hmul).resolve_left htwo
    have hd : q ∣ Nat.fib (q-1) := (ZMod.natCast_eq_zero_iff _ _).mp hfibzero
    simpa [hres] using hd
  · have hres : q % 5 = 2 ∨ q % 5 = 3 :=
      (legendreSym_five_eq_neg_one_iff hq2).mp hneg
    have hmul : (2 : ZMod q) * (Nat.fib (q+1) : ZMod q) = 0 := by
      rw [hpair.2, hneg]
      norm_num
    have hfibzero : (Nat.fib (q+1) : ZMod q)=0 := (mul_eq_zero.mp hmul).resolve_left htwo
    have hd : q ∣ Nat.fib (q+1) := (ZMod.natCast_eq_zero_iff _ _).mp hfibzero
    simpa [hres] using hd

end MathGacha
