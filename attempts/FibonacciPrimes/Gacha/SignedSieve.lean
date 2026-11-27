import Gacha.LinearSieve
import Gacha.IndexResidue

namespace MathGacha

/-- A prime index in the residue class `3` modulo `5 * M_K` has a large Fibonacci
prime factor in the negative index residue class. -/
theorem negativeLargeFactorForEveryTail (K B : ℕ) :
    ∃ p > B, p.Prime ∧ ∃ q, q.Prime ∧ q ∣ Nat.fib p ∧ K*p < q ∧ p ∣ q + 1 := by
  let M := linearFormsModulus K
  let N := 5 * M
  have hcop : Nat.Coprime 3 M := linearFormsModulusCoprime K
  have hcopN : Nat.Coprime 3 N := by
    dsimp [N]
    exact Nat.Coprime.mul_right (by decide : Nat.Coprime 3 5) hcop
  have hN : N ≠ 0 := by
    intro hzero
    simp [Nat.Coprime, hzero] at hcopN
  obtain ⟨p, hpbound, hp, hmodN⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B 5) hN hcopN
  have hlarge : 5 < p := by omega
  have hmodM : p ≡ 3 [MOD M] := by
    exact (Nat.ModEq.of_dvd (by dsimp [N]; exact dvd_mul_left M 5) hmodN)
  have hmod5 : p ≡ 3 [MOD 5] := by
    exact (Nat.ModEq.of_dvd (by dsimp [N]; exact dvd_mul_right 5 M) hmodN)
  have : Fact p.Prime := ⟨hp⟩
  have hsign : legendreSym p 5 = -1 :=
    (legendreSym_five_eq_neg_one_iff (by omega)).mpr (Or.inr hmod5)
  obtain ⟨q, hq, hqdiv, hqneg⟩ := exists_prime_factor_eq_neg_one_mod hp hlarge hsign
  have hmin := leastFactorBoundOnClass hp hlarge hmodM
  have hqbound : K*p < q := by
    exact lt_of_lt_of_le hmin (Nat.minFac_le_of_dvd hq.two_le hqdiv)
  exact ⟨p, by omega, hp, q, hq, hqdiv, hqbound, hqneg⟩

end MathGacha
