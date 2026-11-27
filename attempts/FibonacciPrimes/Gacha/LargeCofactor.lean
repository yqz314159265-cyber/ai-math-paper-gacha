import Gacha.FastModFib
import Gacha.EffectiveWitness
import Gacha.SixthCubic
import Gacha.Cutoff

namespace MathGacha

/-- A cofactor beyond three simple, pairwise coprime divisors supplies a
prime divisor different from each of them. -/
theorem primeBeyondThreeSimpleDivisors {N a b c : ℕ}
    (hab : a.Coprime b) (habc : (a*b).Coprime c)
    (ha : a ∣ N) (hb : b ∣ N) (hc : c ∣ N)
    (hna : ¬ a^2 ∣ N) (hnb : ¬ b^2 ∣ N) (hnc : ¬ c^2 ∣ N) (hl : a*b*c<N) :
    ∃ r, r.Prime ∧ r ∣ N ∧ r≠a ∧ r≠b ∧ r≠c := by
  obtain ⟨k,hk⟩ := habc.mul_dvd_of_dvd_of_dvd (hab.mul_dvd_of_dvd_of_dvd ha hb) hc
  have hone : k≠1 := by rintro rfl; simp_all
  have hr := Nat.minFac_dvd k
  have hkN : k ∣ N := ⟨a*b*c,by rw [hk]; ring⟩
  refine ⟨k.minFac,Nat.minFac_prime hone,hr.trans hkN,?_,?_,?_⟩
  · rintro he
    rw [he] at hr
    obtain ⟨u,hu⟩ := hr
    exact hna ⟨b*c*u,by rw [hk,hu]; ring⟩
  · rintro he
    rw [he] at hr
    obtain ⟨u,hu⟩ := hr
    exact hnb ⟨a*c*u,by rw [hk,hu]; ring⟩
  · rintro he
    rw [he] at hr
    obtain ⟨u,hu⟩ := hr
    exact hnc ⟨a*b*u,by rw [hk,hu]; ring⟩

/-- All three divisors returned by the multiplier search are primes, each
occurring to exponent exactly one. -/
theorem largeIndexThreeSimplePrimes {d : ℕ}
    (hd : d ∈ [54584542993780853,5755636811233114493,670170824029976731793]) :
    d.Prime ∧ d ∣ Nat.fib 1010824870255201 ∧ ¬ d^2 ∣ Nat.fib 1010824870255201 := by
  have hdiv : d ∣ Nat.fib 1010824870255201 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl
    · exact largeIndexFirstDvd
    · exact largeIndexSecondDvd
    · exact largeIndexThirdDvd
  refine ⟨primeDivisorBelowLinearSquare effectiveWitnessPrime (by decide) ?_ ?_ hdiv,hdiv,?_⟩
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  all_goals rcases hd with rfl|rfl|rfl
  all_goals first | (rw [largeIndexDvdIff]; decide +kernel) | decide +kernel

/-- The term has at least one additional prime divisor outside the three explicit ones. -/
theorem largeIndexHasFourthPrime :
    ∃ r, r.Prime ∧ r ∣ Nat.fib 1010824870255201 ∧
      r≠54584542993780853 ∧ r≠5755636811233114493 ∧ r≠670170824029976731793 := by
  have ha := largeIndexThreeSimplePrimes (d:=54584542993780853) (by decide)
  have hb := largeIndexThreeSimplePrimes (d:=5755636811233114493) (by decide)
  have hc := largeIndexThreeSimplePrimes (d:=670170824029976731793) (by decide)
  apply primeBeyondThreeSimpleDivisors (by decide +kernel) (by decide +kernel)
    ha.2.1 hb.2.1 hc.2.1 ha.2.2 hb.2.2 hc.2.2
  exact lt_of_lt_of_le (by decide +kernel) (fourthPowerBelowFib (n:=1010824870255201) (by decide))

end MathGacha
