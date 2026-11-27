import Gacha.MinusPairBridge
import Gacha.FactorRank
import Mathlib.NumberTheory.SelbergSieve

namespace MathGacha

def evenPairSlopes (K : ℕ) := (Finset.Icc 1 K).filter (fun k => 2∣k)

def largePlusPairIndices (X y k : ℕ) := (Finset.range (X+1)).filter
  (fun n => y<n ∧ y<k*n+1 ∧ n.Prime ∧ (k*n+1).Prime)

def largeMinusPairIndices (X y k : ℕ) := (Finset.range (X+1)).filter
  (fun n => y<n ∧ y<k*n-1 ∧ n.Prime ∧ (k*n-1).Prime)

def smallFactorIndices (X y K : ℕ) := (Finset.range (X+1)).filter
  (fun n => 5<n ∧ y<n ∧ n.Prime ∧ (Nat.fib n).minFac≤K*n)

/-- Every obstruction beyond the sieve cutoff belongs to an even-slope prime pair. -/
theorem smallFactorIndices_covered (X y K : ℕ) : smallFactorIndices X y K ⊆
    (evenPairSlopes K).biUnion (fun k => largePlusPairIndices X y k ∪ largeMinusPairIndices X y k) := by
  intro n hn
  obtain ⟨hnX,h5,hyn,hp,hbound⟩ := Finset.mem_filter.mp hn
  let q := (Nat.fib n).minFac
  have hf := Nat.le_fib_self (show 5≤n by omega)
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hd : q∣Nat.fib n := Nat.minFac_dvd _
  have hl := fibLeastFactorLinearBound hp h5 hq hd
  obtain ⟨k,hk1,hkK,hform⟩ := divisorProgressionUpTo hp h5 hq hd hbound
  have hnodd := hp.eq_two_or_odd.resolve_left (by omega)
  have hqodd := hq.eq_two_or_odd.resolve_left (by omega)
  have hpmod : n%2=1 := hnodd
  have hqmod : q%2=1 := hqodd
  have hkn := Nat.le_mul_of_pos_left n hk1
  have hk2 : 2∣k := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    by_contra! h
    have hko : k%2=1 := by omega
    have hprod : (k*n)%2=1 := by rw [Nat.mul_mod,hko,hpmod]
    rcases hform with hh|hh <;> omega
  refine Finset.mem_biUnion.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1,hkK⟩,hk2⟩,?_⟩
  rcases hform with hh|hh
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnX,hyn,by omega,hp,hh ▸ hq⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnX,hyn,by omega,hp,hh ▸ hq⟩)

theorem smallFactorIndices_card_le (X y K : ℕ) :
    (smallFactorIndices X y K).card ≤ ∑ k ∈ evenPairSlopes K,
    ((largePlusPairIndices X y k).card+(largeMinusPairIndices X y k).card) := by
  apply (Finset.card_le_card (smallFactorIndices_covered ..)).trans
  apply Finset.card_biUnion_le.trans
  exact Finset.sum_le_sum (fun k _ => Finset.card_union_le ..)

/-- Unit-weight sieves dominate the cardinality of any injectively parameterized
subset of the surviving support. -/
theorem count_le_unitSiftedSum (s : BoundingSieve) (A : Finset ℕ) (f : ℕ → ℕ)
    (hinj : Function.Injective f) (hw : ∀ a∈s.support, s.weights a=1)
    (hkeep : ∀ a∈A, f a∈s.support ∧ s.prodPrimes.Coprime (f a)) :
    (A.card:ℝ)≤s.siftedSum := by
  have hsub : A.image f ⊆ s.support.filter (fun d => s.prodPrimes.Coprime d) := by
    intro d hd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_filter.mpr (hkeep a ha)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hc
  have he : s.siftedSum=((s.support.filter (fun d => s.prodPrimes.Coprime d)).card:ℝ) := by
    unfold BoundingSieve.siftedSum
    calc
      _ = ∑ d∈s.support, if s.prodPrimes.Coprime d then (1:ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hw a ha]
      _ = _ := by rw [Finset.sum_boole]
  rw [he]
  exact_mod_cast hc

theorem plusPairCoprime {k n y : ℕ} (hn : n.Prime) (hq : (k*n+1).Prime)
    (hny : y<n) (hqy : y<k*n+1) : (n*(k*n+1)).Coprime (primorial y) :=
  Nat.Coprime.mul_left (hn.coprime_iff_not_dvd.mpr (fun h => hny.not_ge (hn.dvd_primorial_iff.mp h)))
    (hq.coprime_iff_not_dvd.mpr (fun h => hqy.not_ge (hq.dvd_primorial_iff.mp h)))


theorem largePlusPairIndices_le_siftedSum (s : BoundingSieve) (X y k : ℕ)
    (hinj : Function.Injective (fun n : ℕ => n*(k*n+1)))
    (hw : ∀ a∈s.support, s.weights a=1) (hP : s.prodPrimes=primorial y)
    (hs : ∀ n≤X, n*(k*n+1)∈s.support) :
    ((largePlusPairIndices X y k).card:ℝ)≤s.siftedSum := by
  apply count_le_unitSiftedSum s _ _ hinj hw
  intro n hn
  obtain ⟨hnX,hnY,hqY,hp,hq⟩ := Finset.mem_filter.mp hn
  rw [hP]
  exact ⟨hs n (by have hh := Finset.mem_range.mp hnX; omega),
    (plusPairCoprime hp hq hnY hqY).symm⟩

theorem largeMinusPairIndices_le_siftedSum (s : BoundingSieve) (X y k : ℕ)
    (hinj : Function.Injective (fun n : ℕ => n*(reflectedSlope (primorial y) k*n+1)))
    (hw : ∀ a∈s.support, s.weights a=1) (hP : s.prodPrimes=primorial y)
    (hs : ∀ n≤X, n*(reflectedSlope (primorial y) k*n+1)∈s.support) :
    ((largeMinusPairIndices X y k).card:ℝ)≤s.siftedSum := by
  apply count_le_unitSiftedSum s _ _ hinj hw
  intro n hn
  obtain ⟨hnX,hnY,hqY,hp,hq⟩ := Finset.mem_filter.mp hn
  rw [hP]
  exact ⟨hs n (by have hh := Finset.mem_range.mp hnX; omega),
    (reflectedPrimePairSurvives hp hq hnY hqY).symm⟩

end MathGacha
