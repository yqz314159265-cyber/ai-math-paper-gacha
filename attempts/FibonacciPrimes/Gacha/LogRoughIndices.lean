import Gacha.PrimePairLocalDen
import Gacha.AveragePairCount
import Gacha.ExponentialSieveGap

namespace MathGacha

/-- Uniform finite bound on all obstructions to the moving linear threshold. -/
theorem logSieveBadIndexCount (X U K : ℕ) (hU : 1≤U) :
    ((smallFactorIndices X U K).card:ℝ) ≤
      8*Real.exp 6*(K:ℝ)*((X:ℝ)+1)/(Real.log (U+1:ℕ))^2+
        2*K*finitePairError (U^2) :=
  averagePairBoundFromDen hU (fun _ hk0 hk => actualPairDenLower hk0 hk X U)

/-- Arbitrarily large prime-index Fibonacci numbers have least prime factor
greater than p log(p)/2^30. -/
theorem infinitelyOftenLogRoughFibIndex (B : ℕ) :
    ∃ p>B, p.Prime ∧ (p:ℝ)*Real.log p/1073741824 < ((Nat.fib p).minFac:ℝ) := by
  apply extractLogRoughFibIndices _ B
  intro U K hU
  have hh := logSieveBadIndexCount ((U+1)^64) U K (by omega)
  have hc : (((U+1)^64:ℕ):ℝ)=((U+1:ℕ):ℝ)^64 := Nat.cast_pow ..
  rw [hc] at hh
  exact hh

/-- Equivalently every prime divisor of each selected term obeys the
logarithmic lower bound, irrespective of its multiplicity. -/
theorem allFactorsLogRoughFibIndex (B : ℕ) :
    ∃ p>B, p.Prime ∧ ∀ q : ℕ, q.Prime → q∣Nat.fib p →
      (p:ℝ)*Real.log p/1073741824 < (q:ℝ) := by
  obtain ⟨p,hB,hp,h⟩ := infinitelyOftenLogRoughFibIndex B
  refine ⟨p,hB,hp,?_⟩
  intro q hq hd
  exact h.trans_le (by exact_mod_cast Nat.minFac_le_of_dvd hq.one_lt hd)

end MathGacha
