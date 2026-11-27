import Gacha.LargeCofactor
import Gacha.DicksonTests
import Mathlib.Tactic

namespace MathGacha

/-- The linear residue constraints leave three candidate divisors in the strict interval. -/
theorem divisor_in_linear_interval
    {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hp4 : p % 4 = 1) (hpmod5 : p % 5 = 1)
    (hq : q.Prime) (hq5 : 5 < q) (hd : q ∣ Nat.fib p)
    (hlower : 35 * p < q) (hupper : q < 54 * p - 1) :
    q = 38 * p - 1 ∨ q = 40 * p + 1 ∨ q = 48 * p + 1 := by
  have hindex : p ∣ neighborIndex q := (primeDivisorIffDickson hp hq hq5).mp hd |>.1
  let k := neighborIndex q / p
  have hk : k * p = neighborIndex q := by
    dsimp [k]
    exact Nat.div_mul_cancel hindex
  have hres := divisorMultiplierResidues hp hp5 hq hq5 hd hk
  have hmul5 : (k * p) % 5 = k % 5 := by
    rw [Nat.mul_mod, hpmod5]
    simp
  rcases hres with hplus | hminus
  · rcases hplus with ⟨hqe, hk4, hkp5⟩
    have hklo : 35 ≤ k := by
      by_contra! h
      have hm := Nat.mul_le_mul_right p h
      rw [Nat.succ_mul] at hm
      nlinarith only [hqe, hlower, hm, hp5]
    have hkhi : k ≤ 53 := by
      by_contra! h
      have hm := Nat.mul_le_mul_right p h
      have hupper' : q + 1 < 54 * p := by omega
      nlinarith only [hqe, hupper', hm]
    have hk5 : k % 5 = 0 ∨ k % 5 = 3 := by rw [← hmul5]; exact hkp5
    have hkval : k = 40 ∨ k = 48 := by omega
    rcases hkval with hk40 | hk48
    · right
      left
      rw [hk40] at hqe
      exact hqe
    · right
      right
      rw [hk48] at hqe
      exact hqe
  · rcases hminus with ⟨hqe, hk4, hkp5⟩
    have hklo : 36 ≤ k := by
      by_contra! h
      have hk35 : k ≤ 35 := by omega
      have hm := Nat.mul_le_mul_right p hk35
      nlinarith only [hqe, hlower, hm, hp5]
    have hkhi : k ≤ 53 := by
      by_contra! h
      have hm := Nat.mul_le_mul_right p h
      have hupper' : q + 1 < 54 * p := by omega
      nlinarith only [hqe, hupper', hm]
    have hk5 : k % 5 = 3 ∨ k % 5 = 4 := by rw [← hmul5]; exact hkp5
    have hk38 : k = 38 := by omega
    left
    rw [hk38] at hqe
    omega

/-- Once all smaller prime divisors are excluded, `54p-1 | F_p` identifies
it as the least prime factor. `h35` is supplied by the existing K=35 bound. -/
theorem effectiveWitnessMinFac
    (hp : Nat.Prime 1010824870255201)
    (h35 : 35 * 1010824870255201 < (Nat.fib 1010824870255201).minFac)
    (hd : (54 * 1010824870255201 - 1) ∣ Nat.fib 1010824870255201)
    (h40 : ¬ (40 * 1010824870255201 + 1) ∣ Nat.fib 1010824870255201) :
    (Nat.fib 1010824870255201).minFac = 54 * 1010824870255201 - 1 := by
  let q := (Nat.fib 1010824870255201).minFac
  have hp5 : 5 < 1010824870255201 := by norm_num
  have hp4 : 1010824870255201 % 4 = 1 := by norm_num
  have hpmod5 : 1010824870255201 % 5 = 1 := by norm_num
  have hFibLower : 1 < Nat.fib 1010824870255201 := by
    have hle := Nat.le_fib_self (n := 1010824870255201) (by norm_num : 5 ≤ 1010824870255201)
    omega
  have hqprime : q.Prime := Nat.minFac_prime (by omega)
  have hqdiv : q ∣ Nat.fib 1010824870255201 := by
    change Nat.minFac (Nat.fib 1010824870255201) ∣ Nat.fib 1010824870255201
    exact Nat.minFac_dvd _
  have hqLower : 35 * 1010824870255201 < q := by
    change 35 * 1010824870255201 < (Nat.fib 1010824870255201).minFac at h35
    exact h35
  have hdpos : 2 ≤ 54 * 1010824870255201 - 1 := by norm_num
  have hqUpper : q ≤ 54 * 1010824870255201 - 1 := Nat.minFac_le_of_dvd hdpos hd
  have hq5 : 5 < q := by omega
  have hge : 54 * 1010824870255201 - 1 ≤ q := by
    by_contra hnot
    have hstrict : q < 54 * 1010824870255201 - 1 := by omega
    rcases divisor_in_linear_interval hp hp5 hp4 hpmod5 hqprime hq5 hqdiv hqLower hstrict with h38 | hrem
    · have h677 : 677 ∣ q := by rw [h38]; norm_num
      have heq : 677 = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hqprime).mp h677
      omega
    · rcases hrem with h40eq | h48
      · apply h40
        simpa [h40eq] using hqdiv
      · have h7 : 7 ∣ q := by rw [h48]; norm_num
        have heq : 7 = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hqprime).mp h7
        omega
  have hqeq : q = 54 * 1010824870255201 - 1 := Nat.le_antisymm hqUpper hge
  simpa only [q] using hqeq

/-- The first prime factor occurs at multiplier 54. -/
theorem largeIndexMinFactorExact :
    (Nat.fib 1010824870255201).minFac=54584542993780853 :=
  effectiveWitnessMinFac effectiveWitnessPrime effectiveWitnessLeastFactor largeIndexFirstDvd
    largeIndexExcludesForty

end MathGacha
