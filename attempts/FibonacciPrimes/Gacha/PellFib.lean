import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Gacha.Statement
import Gacha.Index
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option linter.style.haveILetI false

namespace MathGacha

def pellConicPoint (x y : ℕ) : Prop := x^2 + 4 = 5 * y^2

theorem pellConicBase : pellConicPoint 1 1 := by norm_num [pellConicPoint]
theorem pellConicYTwo : pellConicPoint 4 2 := by norm_num [pellConicPoint]

theorem pellConicDescentIdentity (x y u v : ℤ)
    (hu : 2 * u = 3 * x - 5 * y)
    (hv : 2 * v = 3 * y - x)
    (h : x^2 + 4 = 5 * y^2) : u^2 + 4 = 5 * v^2 := by
  have hu2 := congrArg (fun z : ℤ => z^2) hu
  have hv2 := congrArg (fun z : ℤ => z^2) hv
  nlinarith [hu2, hv2]

theorem pellConicAscentIdentity (x y u v : ℤ)
    (hu : 2 * x = 3 * u + 5 * v)
    (hv : 2 * y = u + 3 * v)
    (h : u^2 + 4 = 5 * v^2) : x^2 + 4 = 5 * y^2 := by
  have hu2 := congrArg (fun z : ℤ => z^2) hu
  have hv2 := congrArg (fun z : ℤ => z^2) hv
  nlinarith [hu2, hv2]

lemma pellConicSameParity {x y : ℕ} (h : pellConicPoint x y) : x % 2 = y % 2 := by
  unfold pellConicPoint at h
  have hm := congrArg (fun n : ℕ => n % 4) h
  have hx : x % 4 < 4 := Nat.mod_lt _ (by decide)
  have hy : y % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hxv : x % 4 <;> interval_cases hyv : y % 4 <;>
    simp [hxv, hyv, Nat.mul_mod, Nat.pow_mod] at hm <;> omega

lemma pellConicHalfDivisibility {x y : ℕ} (h : pellConicPoint x y) :
    2 ∣ 3*x - 5*y ∧ 2 ∣ 3*y - x := by
  have he := pellConicSameParity h
  constructor <;> omega

lemma pellConicBounds {x y : ℕ} (h : pellConicPoint x y) (hy : 2 ≤ y) :
    5*y ≤ 3*x ∧ x < 3*y ∧ y ≤ x := by
  unfold pellConicPoint at h
  constructor
  · by_contra hn
    have hlt : 3*x < 5*y := by omega
    nlinarith [sq_nonneg (3*x - 5*y)]
  constructor
  · by_contra hn
    have hge : 3*y ≤ x := by omega
    nlinarith [sq_nonneg (x - 3*y)]
  · by_contra hn
    have hlt : x < y := by omega
    nlinarith [sq_nonneg (y - x)]

lemma pellConicExistsSmaller {x y : ℕ} (h : pellConicPoint x y) (hy : 2 ≤ y) :
    ∃ u v : ℕ, 0 < v ∧ v < y ∧
      2*u = 3*x - 5*y ∧ 2*v = 3*y - x ∧ pellConicPoint u v := by
  obtain ⟨h5, h3, hyx⟩ := pellConicBounds h hy
  obtain ⟨u, hu⟩ := (pellConicHalfDivisibility h).1
  obtain ⟨v, hv⟩ := (pellConicHalfDivisibility h).2
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · unfold pellConicPoint at *
    have huZ : (2 * (u : ℤ)) = 3 * (x : ℤ) - 5 * (y : ℤ) := by
      exact_mod_cast hu.symm
    have hvZ : (2 * (v : ℤ)) = 3 * (y : ℤ) - (x : ℤ) := by
      have hc : (2 * (v : ℤ)) = ((3 * y - x : ℕ) : ℤ) := by
        exact_mod_cast hv.symm
      rw [Nat.cast_sub (by omega)] at hc
      exact hc
    have hInt := pellConicDescentIdentity (x : ℤ) (y : ℤ) (u : ℤ) (v : ℤ)
      huZ hvZ (by exact_mod_cast h)
    exact_mod_cast hInt

def pellConicOddLucas (k : ℕ) : ℕ := Nat.fib (2*k) + Nat.fib (2*k+2)
def pellConicOddFib (k : ℕ) : ℕ := Nat.fib (2*k+1)

lemma pellConicOddLucasStep (k : ℕ) : 2 * pellConicOddLucas (k+1) =
    3 * pellConicOddLucas k + 5 * pellConicOddFib k := by
  dsimp [pellConicOddLucas, pellConicOddFib]
  rw [show 2*(k+1)=2*k+2 by omega]
  rw [show 2*k+2+2=(2*k+2)+2 by omega]
  simp only [Nat.fib_add_two]
  omega

lemma pellConicOddFibStep (k : ℕ) : 2 * pellConicOddFib (k+1) =
    pellConicOddLucas k + 3 * pellConicOddFib k := by
  dsimp [pellConicOddLucas, pellConicOddFib]
  rw [show 2*(k+1)+1=(2*k+1)+2 by omega,
      show 2*k+2=(2*k)+2 by omega]
  simp only [Nat.fib_add_two]
  omega

lemma pellConicOddFibPell (k : ℕ) : pellConicPoint (pellConicOddLucas k) (pellConicOddFib k) := by
  induction k with
  | zero => norm_num [pellConicPoint, pellConicOddLucas, pellConicOddFib]
  | succ k ih =>
    have ha := pellConicOddLucasStep k
    have hb := pellConicOddFibStep k
    have haZ : 2 * (pellConicOddLucas (k+1) : ℤ) =
        3 * (pellConicOddLucas k : ℤ) + 5 * (pellConicOddFib k : ℤ) := by exact_mod_cast ha
    have hbZ : 2 * (pellConicOddFib (k+1) : ℤ) =
        (pellConicOddLucas k : ℤ) + 3 * (pellConicOddFib k : ℤ) := by exact_mod_cast hb
    have ha2 := congrArg (fun z : ℤ => z^2) haZ
    have hb2 := congrArg (fun z : ℤ => z^2) hbZ
    have hi : (pellConicOddLucas k : ℤ)^2 + 4 = 5 * (pellConicOddFib k : ℤ)^2 := by exact_mod_cast ih
    have hInt : (pellConicOddLucas (k+1) : ℤ)^2 + 4 =
        5 * (pellConicOddFib (k+1) : ℤ)^2 := by nlinarith [ha2, hb2, hi]
    exact_mod_cast hInt

lemma pellConicPointsAreOddFibonacci {x y : ℕ} (h : pellConicPoint x y) :
    ∃ k : ℕ, x = pellConicOddLucas k ∧ y = pellConicOddFib k := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases hy : y < 2
    · interval_cases y
      · unfold pellConicPoint at h
        norm_num at h
      · have hx : x = 1 := by
          unfold pellConicPoint at h
          nlinarith
        refine ⟨0, ?_, ?_⟩
        · simpa [pellConicOddLucas] using hx
        · norm_num [pellConicOddFib]
    · have htwo : 2 ≤ y := by omega
      obtain ⟨u, v, hvpos, hvlt, hu, hv, hp⟩ := pellConicExistsSmaller h htwo
      obtain ⟨k, hku, hkv⟩ := ih v hvlt hp
      have h5 : 5*y ≤ 3*x := (pellConicBounds h htwo).1
      have hu' : 2*u + 5*y = 3*x := by omega
      have hv' : 2*v + x = 3*y := by omega
      have hxlin : 2*x = 3*u + 5*v := by omega
      have hylin : 2*y = u + 3*v := by omega
      refine ⟨k+1, ?_, ?_⟩
      · have hxlin' := hxlin
        rw [hku, hkv] at hxlin'
        have hs := pellConicOddLucasStep k
        omega
      · have hylin' := hylin
        rw [hku, hkv] at hylin'
        have hs := pellConicOddFibStep k
        omega

theorem pellConicPrimeIffFibValue {q : ℕ} (hq : Nat.Prime q) (hq3 : 3 < q) :
    (∃ x : ℕ, pellConicPoint x q) ↔ ∃ n : ℕ, Nat.fib n = q := by
  constructor
  · rintro ⟨x, hp⟩
    obtain ⟨k, _, hy⟩ := pellConicPointsAreOddFibonacci hp
    refine ⟨2*k+1, ?_⟩
    simpa [pellConicOddFib] using hy.symm
  · rintro ⟨n, hfib⟩
    have hqfibprime : (Nat.fib n).Prime := by rw [hfib]; exact hq
    have hidx := MathGacha.fib_prime_index_prime_or_four hqfibprime
    rcases hidx with hnp | hn4
    · have hn2 : n ≠ 2 := by
        intro he
        subst n
        norm_num [Nat.fib_add_two] at hfib
        omega
      obtain ⟨k, hk⟩ := hnp.odd_of_ne_two hn2
      have hp := pellConicOddFibPell k
      refine ⟨pellConicOddLucas k, ?_⟩
      rw [hk] at hfib
      simpa [pellConicOddFib, hfib] using hp
    · subst n
      norm_num [Nat.fib_add_two] at hfib
      omega

def pellConicPrimeYUnbounded : Prop :=
  ∀ B : ℕ, ∃ y > B, Nat.Prime y ∧ ∃ x : ℕ, pellConicPoint x y

theorem pellConicOriginalIffPrimeYUnbounded :
    MathGacha.Original ↔ pellConicPrimeYUnbounded := by
  unfold MathGacha.Original pellConicPrimeYUnbounded
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h B
    obtain ⟨q, ⟨⟨n, hfib⟩, hq⟩, hBq⟩ := h (max B 3)
    have hp := (pellConicPrimeIffFibValue hq (by omega : 3 < q)).2 ⟨n, hfib⟩
    exact ⟨q, by omega, hq, hp⟩
  · intro h B
    obtain ⟨q, hBq, hq, ⟨x, hp⟩⟩ := h (max B 3)
    obtain ⟨n, hfib⟩ := (pellConicPrimeIffFibValue hq (by omega : 3 < q)).1 ⟨x, hp⟩
    exact ⟨q, ⟨⟨n, hfib⟩, hq⟩, by omega⟩

/-- The prime y-coordinate of a Pell-conic point greater than three is 1 mod 4. -/
theorem pellConicPrimeYModFour {x q : ℕ} (hp : pellConicPoint x q)
    (hq : q.Prime) (hq3 : 3 < q) : q % 4 = 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hmod : (x : ZMod q)^2 = -4 := by
    have hc := congrArg (fun n : ℕ => (n : ZMod q)) hp
    norm_num [pellConicPoint, ZMod.natCast_self] at hc ⊢
    linear_combination hc
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro he
    have hq2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp he
    have hqle : q ≤ 2 := Nat.le_of_dvd (by decide) hq2
    omega
  have hsquare : IsSquare (-1 : ZMod q) := by
    have hinv : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ h2
    have hz : (-1 : ZMod q) = ((x : ZMod q) * (2 : ZMod q)⁻¹)^2 := calc
      -1 = (-4) * ((2 : ZMod q)⁻¹)^2 := by
        rw [show (-4 : ZMod q) * ((2 : ZMod q)⁻¹)^2 = -((2 : ZMod q) * (2 : ZMod q)⁻¹)^2 by ring,
          hinv]
        norm_num
      _ = (x : ZMod q)^2 * ((2 : ZMod q)⁻¹)^2 := by rw [hmod]
      _ = ((x : ZMod q) * (2 : ZMod q)⁻¹)^2 := by ring
    exact ⟨(x : ZMod q) * (2 : ZMod q)⁻¹, by simpa [pow_two] using hz⟩
  have hnot3 := ZMod.exists_sq_eq_neg_one_iff.mp hsquare
  obtain ⟨k, hk⟩ := hq.odd_of_ne_two (by omega)
  have hcases : q % 4 = 1 ∨ q % 4 = 3 := by omega
  omega
set_option linter.style.haveILetI true

end MathGacha
