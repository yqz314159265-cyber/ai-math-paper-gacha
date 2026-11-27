import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace MathGacha

/-- Index and divisor pairs from the small-factor screen. -/
def screenWitnesses : List (ℕ × ℕ) := [
  (97, 193), (113, 677), (139, 277), (151, 5737), (157, 313), (163, 977),
  (181, 8689), (199, 397), (223, 4013), (229, 457), (257, 5653), (263, 4733),
  (269, 5381), (307, 613), (313, 1877), (337, 673), (367, 733), (373, 2237),
  (379, 757), (389, 2333), (409, 4909), (439, 877), (443, 8861), (457, 6397),
  (463, 2777), (487, 1949), (499, 997), (521, 9377), (523, 8369), (547, 1093),
  (577, 1153), (593, 3557), (607, 1213), (619, 1237), (727, 1453), (773, 4637),
  (829, 1657), (877, 1753), (883, 5297), (937, 1873), (967, 1933), (983, 5897),
  (997, 1993), (1009, 2017), (1069, 2137), (1087, 4349), (1123, 6737), (1153, 6917),
  (1237, 2473), (1279, 2557), (1297, 2593), (1303, 7817), (1327, 5309), (1399, 2797),
  (1429, 2857), (1459, 2917), (1567, 6269), (1583, 9497), (1609, 3217), (1613, 9677),
  (1627, 3253), (1657, 3313), (1759, 3517), (1777, 7109), (1867, 3733), (2029, 4057),
  (2089, 4177), (2137, 4273), (2179, 4357), (2467, 4933), (2539, 5077), (2557, 5113),
  (2617, 5233), (2707, 5413), (2719, 5437), (3019, 6037), (3037, 6073), (3067, 6133),
  (3109, 6217), (3169, 6337), (3187, 6373), (3319, 6637), (3499, 6997), (3529, 7057),
  (3607, 7213), (3697, 7393), (3709, 7417), (3739, 7477), (3769, 7537), (3877, 7753),
  (3967, 7933), (4027, 8053), (4159, 8317), (4177, 8353), (4339, 8677), (4357, 8713),
  (4447, 8893), (4507, 9013), (4567, 9133), (4639, 9277), (4909, 9817), (4987, 9973)]

theorem screenWitnessesValid :
    ∀ e ∈ screenWitnesses, 1 < e.2 ∧ e.2 < Nat.fib e.1 ∧ e.2 ∣ Nat.fib e.1 := by
  rw [Nat.fib_eq_fastFib]
  decide +kernel

theorem screenTermsComposite {p q : ℕ} (h : (p, q) ∈ screenWitnesses) :
    ¬ (Nat.fib p).Prime := by
  obtain ⟨hlo, hhi, hd⟩ := screenWitnessesValid (p, q) h
  intro hp
  exact hhi.ne ((Nat.dvd_prime_two_le hp hlo).mp hd)

/-- An explicit survivor of the 10,000-factor screen is composite. -/
theorem survivor101Composite : ¬ (Nat.fib 101).Prime :=
  Nat.not_prime_of_mul_eq (show 743519377 * 770857978613 = Nat.fib 101 by decide)
    (by decide) (by decide)

theorem survivor101NoSmallDivisor {d : ℕ} (hd : 1 < d) (hbound : d ≤ 10000) :
    ¬ d ∣ Nat.fib 101 := by
  have hc : Nat.Coprime (Nat.fib 101) (Nat.factorial 10000) := by
    rw [Nat.factorial_eq_factorialBinarySplitting]
    decide +kernel
  intro h
  have h1 : d ∣ 1 := hc.gcd_eq_one ▸ Nat.dvd_gcd h (Nat.dvd_factorial (by omega) hbound)
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd Nat.one_pos h1)) hd

end MathGacha
