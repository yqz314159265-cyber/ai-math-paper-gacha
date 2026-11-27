import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

set_option maxHeartbeats 1000000

namespace MathGacha

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * bitsValue bs + b.toNat

def fibPairMod (d : ℕ) : List Bool → ZMod d × ZMod d
  | [] => (0, 1)
  | b :: bs =>
      let (x, y) := fibPairMod d bs
      let c := x * (2 * y - x)
      let e := x ^ 2 + y ^ 2
      if b then (e, c + e) else (c, e)

theorem fibPairMod_correct (d : ℕ) (bs : List Bool) :
    fibPairMod d bs = ((Nat.fib (bitsValue bs) : ZMod d),
      (Nat.fib (bitsValue bs + 1) : ZMod d)) := by
  induction bs with
  | nil => simp [fibPairMod, bitsValue]
  | cons bit bs ih =>
    cases bit
    · simp [bitsValue, fibPairMod, ih]
      rw [Nat.fib_two_mul, Nat.fib_two_mul_add_one]
      push_cast
      rw [Nat.cast_sub (by have h := Nat.fib_le_fib_succ (n := bitsValue bs); omega)]
      constructor
      · norm_num [Nat.cast_mul]
      · ring_nf
    · simp [bitsValue, fibPairMod, ih]
      rw [Nat.fib_two_mul_add_one, Nat.fib_two_mul_add_two]
      push_cast
      constructor <;> ring_nf

theorem fibPairMod_first_eq_iff (d : ℕ) (bs : List Bool) :
    (fibPairMod d bs).1 = 0 ↔ d ∣ Nat.fib (bitsValue bs) := by
  rw [fibPairMod_correct]
  exact ZMod.natCast_eq_zero_iff _ d

def targetBits : List Bool :=
  [true, false, false, false, false, true, true, false, false, true,
   false, true, true, false, true, false, false, true, false, false,
   true, false, true, false, true, false, false, false, false, false,
   false, false, true, true, true, false, true, false, true, false,
   true, true, true, false, true, false, false, true, true, true]

theorem targetBits_value : bitsValue targetBits = 1010824870255201 := by decide +kernel

theorem largeIndexDvdIff (d : ℕ) :
    d ∣ Nat.fib 1010824870255201 ↔ (fibPairMod d targetBits).1 = 0 := by
  rw [fibPairMod_first_eq_iff,targetBits_value]

theorem largeIndexFirstDvd : 54584542993780853 ∣ Nat.fib 1010824870255201 := by
  apply (largeIndexDvdIff _).mpr
  decide +kernel

theorem largeIndexSecondDvd : 5755636811233114493 ∣ Nat.fib 1010824870255201 := by
  apply (largeIndexDvdIff _).mpr
  decide +kernel

theorem largeIndexThirdDvd : 670170824029976731793 ∣ Nat.fib 1010824870255201 := by
  apply (largeIndexDvdIff _).mpr
  decide +kernel

theorem largeIndexCandidateResidue :
    (fibPairMod 40432994810208041 targetBits).1 = (3925665491575363 : ZMod 40432994810208041) := by
  decide +kernel

theorem largeIndexExcludesForty : ¬ 40432994810208041 ∣ Nat.fib 1010824870255201 := by
  rw [largeIndexDvdIff,largeIndexCandidateResidue]
  decide +kernel

end MathGacha
