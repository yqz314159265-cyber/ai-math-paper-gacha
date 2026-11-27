import Gacha.ConcretePairCount
import Gacha.TotientMean

open Finset

namespace MathGacha

/-- Sum the two-sign sieve over all relevant slopes. The second moment of
k/φ(k) is bounded independently of the number of slopes. -/
theorem averagePairBoundFromDen {X U K : ℕ} (hU : 1≤U)
    (hden : ∀ k : ℕ, 0<k → (hk : 2∣k) →
      (1/4:ℝ)*((k.totient:ℝ)/(k:ℝ))^2*(Real.log (U+1:ℕ))^2 ≤
        finitePairDen k X U (U^2) hk) :
    ((smallFactorIndices X U K).card:ℝ) ≤
      8*Real.exp 6*(K:ℝ)*((X:ℝ)+1)/(Real.log (U+1:ℕ))^2 + 2*K*finitePairError (U^2) := by
  let J := evenPairSlopes K
  let G (k : ℕ) := if hk : 2∣k then finitePairDen k X U (U^2) hk else 1
  let A (k : ℕ) := ((largePlusPairIndices X U k).card:ℝ)+(largeMinusPairIndices X U k).card
  let v : ℝ := (U+1:ℕ)
  have hv : 1<v := by dsimp [v]; exact_mod_cast (show 1<U+1 by omega)
  have hJ : J⊆Icc 1 K := filter_subset _ _
  have hnum : ((smallFactorIndices X U K).card:ℝ)≤∑ k∈J, A k := by
    dsimp only [A,J]
    exact_mod_cast smallFactorIndices_card_le X U K
  have hG (k : ℕ) (hk : k∈J) : 1/4*((k.totient:ℝ)/(k:ℝ))^2*(Real.log v)^2≤G k := by
    have hk0 := (mem_Icc.mp (hJ hk)).1
    have hk2 := (mem_filter.mp hk).2
    simpa only [G,dif_pos hk2,v] using hden k hk0 hk2
  have hA (k : ℕ) (hk : k∈J) :
      A k≤(2*((X:ℝ)+1))/G k+2*finitePairError (U^2) := by
    have hk2 := (mem_filter.mp hk).2
    have hh := actualTwoSlopeBound k X U (U^2) hk2 (one_le_pow₀ hU)
    dsimp only [A,G]
    rw [dif_pos hk2]
    push_cast at hh
    exact hh.trans_eq (by ring)
  have herr : 0≤finitePairError (U^2) := by unfold finitePairError; positivity
  have h := sum_pair_upper_on_subset J hJ (2*((X:ℝ)+1)) (1/4) v
    (2*finitePairError (U^2)) G A (by positivity) (by norm_num) hv (by positivity) hG hA
  apply hnum.trans (h.trans_eq ?_)
  dsimp only [v]
  ring

end MathGacha
