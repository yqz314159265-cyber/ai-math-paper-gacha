import Gacha.FactorRank
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic

namespace MathGacha

/-- If `5` is a square modulo an odd prime `q ≠ 5`, then `q` divides `F_(q-1)`. -/
theorem fib_q_sub_one_dvd_of_five_square {q : ℕ} (hq : q.Prime)
    (h2 : q ≠ 2) (h5 : q ≠ 5) (s : ZMod q) (hs : s ^ 2 = 5) :
    q ∣ Nat.fib (q - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  have cast_ne {k : ℕ} (hk : k.Prime) (hne : q ≠ k) : (k : ZMod q) ≠ 0 := by
    intro hz
    exact hne ((Nat.dvd_prime_two_le hk hq.two_le).mp
      ((CharP.cast_eq_zero_iff (ZMod q) q k).mp hz))
  have htwo : (2 : ZMod q) ≠ 0 := cast_ne Nat.prime_two h2
  have hfive : (5 : ZMod q) ≠ 0 := cast_ne (by decide : Nat.Prime 5) h5
  obtain ⟨a, b, ha, hb, _, hdiff⟩ := fibRootsFromDiscriminant htwo hs
  have hs0 : s ≠ 0 := by
    intro hz
    exact hfive (by simpa [hz] using hs.symm)
  have hne : a - b ≠ 0 := hdiff ▸ hs0
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  have hpowA : a ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have hpowB : b ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb0
  have hbinet := fibPowerDifference ha hb (q - 1)
  have hcast : (Nat.fib (q - 1) : ZMod q) = 0 := by
    have hz : (a - b) * (Nat.fib (q - 1) : ZMod q) = 0 := by
      simpa [hpowA, hpowB] using hbinet
    rcases mul_eq_zero.mp hz with hz | hz
    · exact (hne hz).elim
    · exact hz
  exact (ZMod.natCast_eq_zero_iff (Nat.fib (q - 1)) q).mp hcast

/-- A split prime factor of `F_p` forces the prime index `p` to divide `q-1`.
The witness `s` states that `5` is a quadratic residue modulo `q`. -/
theorem splitPrimeFactorDividesQSubOne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) (s : ZMod q) (hs : s ^ 2 = 5)
    (hdiv : q ∣ Nat.fib p) : p ∣ q - 1 := by
  exact indexDividesFromCommonFactor hp hq.one_lt hdiv
    (fib_q_sub_one_dvd_of_five_square hq hq2 hq5 s hs)

end MathGacha
