import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

namespace MathGacha

/-- A nonnegative, even when k is even, representative of −k modulo P. -/
def reflectedSlope (P k : ℕ) := k*(2*P-1)

theorem reflectedSlope_add {P : ℕ} (hP : 0<P) (k : ℕ) :
    reflectedSlope P k+k=P*(2*k) := by
  have he : 2*P-1+1=2*P := by omega
  unfold reflectedSlope
  nlinarith only [congrArg (fun n : ℕ => k*n) he]

theorem reflectedSlope_even {P k : ℕ} (hk : 2∣k) : 2∣reflectedSlope P k :=
  dvd_mul_of_dvd_left hk _

theorem dvdReflectedSlopeIff {P r : ℕ} (hP : 0<P) (hr : r∣P) (k : ℕ) :
    r∣reflectedSlope P k ↔ r∣k := by
  have ht : r ∣ reflectedSlope P k+k := reflectedSlope_add hP k ▸ dvd_mul_of_dvd_left hr _
  constructor
  · intro hh; exact (Nat.dvd_add_iff_right hh).mpr ht
  · intro hh; exact (Nat.dvd_add_iff_left hh).mpr ht

theorem minusPairDvdIffPlus {P r k n : ℕ} (hP : 0<P) (hr : r∣P) (hkn : 0<k*n) :
    r∣n*(k*n-1) ↔ r∣n*(reflectedSlope P k*n+1) := by
  have h1 : k*n-1+1=k*n := by omega
  have he : n*(k*n-1)+n*(reflectedSlope P k*n+1)=P*(2*k*n^2) := by
    nlinarith only [congrArg (fun t : ℕ => n*t) h1,
      congrArg (fun t : ℕ => n^2*t) (reflectedSlope_add hP k)]
  have ht : r ∣ n*(k*n-1)+n*(reflectedSlope P k*n+1) := he ▸ dvd_mul_of_dvd_left hr _
  constructor
  · intro hh; exact (Nat.dvd_add_iff_right hh).mpr ht
  · intro hh; exact (Nat.dvd_add_iff_left hh).mpr ht

theorem minusPairCoprimeIffPlus {P k n : ℕ} (hP : 0<P) (hkn : 0<k*n) :
    (n*(k*n-1)).Coprime P ↔ (n*(reflectedSlope P k*n+1)).Coprime P := by
  rw [Nat.coprime_iff_gcd_eq_one,Nat.coprime_iff_gcd_eq_one]
  suffices h : (n*(k*n-1)).gcd P = (n*(reflectedSlope P k*n+1)).gcd P by rw [h]
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right ..)
    exact (minusPairDvdIffPlus hP (Nat.gcd_dvd_right ..) hkn).mp (Nat.gcd_dvd_left ..)
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right ..)
    exact (minusPairDvdIffPlus hP (Nat.gcd_dvd_right ..) hkn).mpr (Nat.gcd_dvd_left ..)

/-- When both entries of the minus pair are prime and exceed y, the reflected
plus polynomial survives the primorial sieve. -/
theorem reflectedPrimePairSurvives {k n y : ℕ} (hn : n.Prime) (hq : (k*n-1).Prime)
    (hny : y<n) (hqy : y<k*n-1) :
    (n*(reflectedSlope (primorial y) k*n+1)).Coprime (primorial y) := by
  have hkn : 0<k*n := by have h := hq.one_lt; omega
  apply (minusPairCoprimeIffPlus (primorial_pos _) hkn).mp
  exact Nat.Coprime.mul_left (hn.coprime_iff_not_dvd.mpr (fun h => hny.not_ge (hn.dvd_primorial_iff.mp h)))
    (hq.coprime_iff_not_dvd.mpr (fun h => hqy.not_ge (hq.dvd_primorial_iff.mp h)))

end MathGacha
