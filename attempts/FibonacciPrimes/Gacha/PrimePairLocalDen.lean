import Gacha.ConcretePairCount
import Gacha.CoprimePairMass
import Gacha.SafePairDenominator
import Gacha.TotientHarmonic

open Finset

namespace MathGacha

/-- All prime divisors of a retained squarefree product belong to the
two-root part of the concrete sieve, even when P includes one-root primes. -/
theorem squarefreePairLocalData {k X U a b : ℕ} (hk : 2∣k)
    (ha : a∈(Icc 1 U).filter (fun n => n.Coprime k))
    (hb : b∈(Icc 1 U).filter (fun n => n.Coprime k)) (hsf : Squarefree (a*b)) :
    a*b∣primorial U ∧ a*b≤U^2 ∧ ∀ r∈(a*b).primeFactors, 3≤r ∧
      (pairBoundingSieveEven k (X+1) (primorial U) hk (squarefree_primorial _)).nu r=2/(r:ℝ) := by
  obtain ⟨⟨_,hau⟩,hac⟩ := (show (1≤a ∧ a≤U) ∧ a.Coprime k by simpa using ha)
  obtain ⟨⟨_,hbu⟩,hbc⟩ := (show (1≤b ∧ b≤U) ∧ b.Coprime k by simpa using hb)
  obtain ⟨hcop,hsa,hsb⟩ := Nat.squarefree_mul_iff.mp hsf
  have hd := hcop.mul_dvd_of_dvd_of_dvd (hsa.dvd_primorial.trans (primorial_dvd_primorial hau))
    (hsb.dvd_primorial.trans (primorial_dvd_primorial hbu))
  refine ⟨hd,by simpa only [pow_two] using Nat.mul_le_mul hau hbu,?_⟩
  intro r hr
  have hpr := Nat.prime_of_mem_primeFactors hr
  have hrc := Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hr) (hac.mul_left hbc)
  have hnd := hpr.coprime_iff_not_dvd.mp hrc
  have htwo : r≠2 := by rintro rfl; exact hnd hk
  refine ⟨by have h := hpr.two_le; omega,?_⟩
  change pairSieveNu k r=2/r
  rw [actualPairSieveNu_eq k r hpr,if_neg hnd]


/-- The concrete Selberg denominator is uniformly at least one fourth of
the totient-squared logarithmic scale for every positive even slope. -/
theorem actualPairDenLower {k : ℕ} (hk0 : 0<k) (hk : 2∣k) (X U : ℕ) :
    (1/4:ℝ)*((k.totient:ℝ)/(k:ℝ))^2*(Real.log (U+1:ℕ))^2 ≤ finitePairDen k X U (U^2) hk := by
  let A := (Icc 1 U).filter (fun n => n.Coprime k)
  let H := ∑ a∈A, (a:ℝ)⁻¹
  let s := pairBoundingSieveEven k (X+1) (primorial U) hk (squarefree_primorial _)
  have hlocal := fun {a b} (ha : a∈A) (hb : b∈A) (h : Squarefree (a*b)) =>
    squarefreePairLocalData (X:=X) hk ha hb h
  have hsf : squarefreePairMass A≤pairSelbergDen s (U^2) := by
    apply squarefreePairMass_le_pairSelbergDen
    · intro a ha; exact (mem_Icc.mp (mem_filter.mp ha).1).1
    · intro a ha b hb h; exact (hlocal ha hb h).1
    · intro a ha b hb h; exact (hlocal ha hb h).2.1
    · intro a ha b hb h r hr
      exact ((hlocal ha hb h).2.2 r hr).symm
  have hH : H=coprimeHarmonic U k := by simp [H,A,coprimeHarmonic,Finset.sum_filter]
  have hlog : (k.totient:ℝ)/k*Real.log (U+1:ℕ)≤H := by
    rw [hH,Nat.cast_add,Nat.cast_one]
    exact totientHarmonic_coprime_lower_log hk0
  have hnn : 0≤(k.totient:ℝ)/k*Real.log (U+1:ℕ) := mul_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 U))
  have hl := pow_le_pow_left₀ hnn hlog 2
  calc
    _ = ((k.totient:ℝ)/k*Real.log (U+1:ℕ))^2/4 := by ring
    _ ≤ H^2/4 := div_le_div_of_nonneg_right hl (by norm_num)
    _ ≤ squarefreePairMass A := coprimePairMass_quarter k U hk
    _ ≤ _ := hsf

end MathGacha
