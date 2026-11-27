import Gacha.FactorRank
import Mathlib.Tactic.NormNum.Prime

namespace MathGacha

/-- A proposed least factor can be certified by testing only multiples of the index plus or minus one. -/
theorem leastFactorCertificate {p D K : ℕ} (hp : p.Prime) (hlarge : 5 < p)
    (hD : 2 ≤ D) (hdiv : D ∣ Nat.fastFib p) (hcut : D ≤ K * p + 1)
    (check : ∀ i : Fin (K+1), 1 ≤ i.val →
      (i.val*p+1 < D → ¬ (i.val*p+1) ∣ Nat.fastFib p) ∧
      (i.val*p-1 < D → ¬ (i.val*p-1) ∣ Nat.fastFib p)) :
    (Nat.fib p).minFac = D := by
  simp only [Nat.fastFib_eq] at hdiv check
  apply Nat.le_antisymm (Nat.minFac_le_of_dvd hD hdiv)
  by_contra! hh
  let q := (Nat.fib p).minFac
  have hlt : q < D := hh
  have hgrowth := Nat.le_fib_self (show 5 ≤ p by omega)
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqdiv : q ∣ Nat.fib p := Nat.minFac_dvd _
  obtain ⟨k, hkpos, hk, hkq⟩ := divisorProgressionUpTo hp hlarge hq hqdiv
    (show q ≤ K*p by omega)
  have c := check ⟨k, by omega⟩ hkpos
  change (k*p+1 < D → ¬ (k*p+1) ∣ Nat.fib p) ∧
      (k*p-1 < D → ¬ (k*p-1) ∣ Nat.fib p) at c
  rcases hkq with he | he
  · exact c.1 (he ▸ hlt) (he ▸ hqdiv)
  · exact c.2 (he ▸ hlt) (he ▸ hqdiv)

set_option maxRecDepth 4096 in
/-- A prime-index composite whose first prime factor exceeds 300 times the index. -/
theorem leastFactor881 : (Nat.fib 881).minFac = 264301 := by
  apply leastFactorCertificate (K := 300) (by norm_num) (by decide) (by decide)
    (by decide +kernel) (by decide) (by decide +kernel)

set_option maxRecDepth 4096 in
/-- A second example with a larger index and the opposite congruence sign. -/
theorem leastFactor17209 : (Nat.fib 17209).minFac = 5197117 := by
  apply leastFactorCertificate (K := 302) (by norm_num) (by decide) (by decide)
    (by decide +kernel) (by decide) (by decide +kernel)

end MathGacha
