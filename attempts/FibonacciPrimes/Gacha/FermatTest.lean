import Gacha.LargePrefix
import Mathlib.FieldTheory.Finite.Basic

namespace MathGacha

/-- Test a base-two Frobenius identity by repeated squaring in natural numbers.
A zero exponent ends the computation. An exhausted budget returns no rejection. -/
def fermatReject (d : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, e, _, c => decide (e=0 ∧ c%d≠2%d)
  | f+1, e, b, c =>
    if e=0 then decide (c%d≠2%d)
    else fermatReject d f (e/2) (b*b%d) (if e%2=0 then c else c*b%d)

theorem fermatRejectFalse {d : ℕ} (fuel e b c : ℕ)
    (h : (c : ZMod d)*(b : ZMod d)^e=2) : fermatReject d fuel e b c = false := by
  have doneCase (n : ℕ) (he : (n : ZMod d)=2) : n%d=2%d :=
    (ZMod.natCast_eq_natCast_iff n 2 d).mp (by simpa using he)
  induction fuel generalizing e b c with
  | zero =>
    by_cases he : e=0
    · subst e
      have hh := doneCase c (by simpa using h)
      simp [fermatReject,hh]
    · simp [fermatReject,he]
  | succ f ih =>
    rw [fermatReject]
    split
    next he =>
      subst e
      have hh := doneCase c (by simpa using h)
      simp [hh]
    next he =>
      apply ih
      by_cases heven : e%2=0
      · rw [if_pos heven]
        simp only [ZMod.natCast_mod, ← pow_two, Nat.cast_pow, ← pow_mul]
        rwa [show 2*(e/2)=e by omega]
      · rw [if_neg heven]
        simp only [ZMod.natCast_mod, ← pow_two, Nat.cast_pow, Nat.cast_mul, ← pow_mul]
        calc
          _ = (c:ZMod d)*(b:ZMod d)^(2*(e/2)+1) := by rw [pow_succ]; ring
          _ = _ := by rwa [show 2*(e/2)+1=e by omega]

/-- A verified rejection is a compositeness certificate regardless of the search budget. -/
theorem nonprimeOfFermatReject {d : ℕ} (fuel : ℕ) (h : fermatReject d fuel d 2 1=true) :
    ¬ d.Prime := by
  intro hp
  have : Fact d.Prime := ⟨hp⟩
  have hf := fermatRejectFalse (d:=d) fuel d 2 1 (by simpa only [Nat.cast_one,Nat.cast_ofNat,one_mul] using ZMod.pow_card (2 : ZMod d))
  simp_all

end MathGacha
