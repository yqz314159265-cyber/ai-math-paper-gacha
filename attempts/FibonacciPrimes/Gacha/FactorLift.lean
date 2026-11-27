import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.ModEq

import Gacha.FactorRank

namespace MathGacha

/-- First-order expansions of the two adjacent values modulo the square of the original term. -/
theorem fibMulFirstOrder (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    Nat.fib (k * p) ≡ k * Nat.fib (p + 1) ^ (k - 1) * Nat.fib p [MOD Nat.fib p ^ 2] ∧
    Nat.fib (k * p + 1) ≡ Nat.fib (p + 1) ^ k [MOD Nat.fib p ^ 2] := by
  let A := Nat.fib (p + 1)
  let B := Nat.fib p
  have hrec : A = Nat.fib (p - 1) + B := Nat.fib_add_one (by omega)
  induction k with
  | zero =>
    constructor <;> simp [Nat.ModEq, Nat.fib_zero]
  | succ k ih =>
    have hidx : (k + 1) * p = k * p + p := by ring
    have hx : Nat.fib ((k + 1) * p) =
        Nat.fib (k * p) * Nat.fib (p - 1) + Nat.fib (k * p + 1) * Nat.fib p := by
      rw [hidx]
      simpa [Nat.sub_add_cancel hp, Nat.add_assoc] using Nat.fib_add (k * p) (p - 1)
    have hy : Nat.fib ((k + 1) * p + 1) =
        Nat.fib (k * p) * Nat.fib p + Nat.fib (k * p + 1) * Nat.fib (p + 1) := by
      rw [hidx]
      simpa [Nat.add_assoc] using Nat.fib_add (k * p) p
    rcases ih with ⟨hX, hY⟩
    constructor
    · rw [hx]
      have hXC := hX.mul_right (Nat.fib (p - 1))
      have hYB := hY.mul_right B
      have hCB : B * Nat.fib (p - 1) ≡ B * A [MOD B ^ 2] := by
        rw [hrec, Nat.mul_add]
        simp [Nat.ModEq, pow_two]
      have hC := hCB.mul_left (k * A ^ (k - 1))
      have hsum := hXC.add hYB
      have hgoal :
          (k * A ^ (k - 1) * B) * Nat.fib (p - 1) + A ^ k * B ≡
            (k + 1) * A ^ k * B [MOD B ^ 2] := by
        have hC' :
            (k * A ^ (k - 1) * B) * Nat.fib (p - 1) ≡
              (k * A ^ (k - 1) * B) * A [MOD B ^ 2] := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hC
        calc
          _ ≡ (k * A ^ (k - 1) * B) * A + A ^ k * B [MOD B ^ 2] := hC'.add (Nat.ModEq.rfl)
          _ ≡ (k + 1) * A ^ k * B [MOD B ^ 2] := by
            apply congrArg (fun z : ℕ => z % (B ^ 2))
            cases k with
            | zero => simp
            | succ j => simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, pow_succ]; ring
      exact hsum.trans hgoal
    · rw [hy]
      have hXB := hX.mul_right B
      have hYA := hY.mul_right A
      have hz : (k * A ^ (k - 1) * B) * B ≡ 0 [MOD B ^ 2] := by
        apply Nat.modEq_zero_iff_dvd.mpr
        refine ⟨k * A ^ (k - 1), ?_⟩
        simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hsum := hXB.add hYA
      have hgoal :
          (k * A ^ (k - 1) * B) * B + A ^ k * A ≡ A ^ (k + 1) [MOD B ^ 2] := by
        calc
          _ ≡ 0 + A ^ k * A [MOD B ^ 2] := hz.add (Nat.ModEq.rfl)
          _ ≡ A ^ (k + 1) [MOD B ^ 2] := by
            simpa [pow_succ] using (Nat.ModEq.rfl : A ^ k * A ≡ A ^ k * A [MOD B ^ 2])
      exact hsum.trans hgoal

/-- The old term and the new cofactor share exactly the factors contributed by the multiplier. -/
theorem fibQuotientGcd {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (Nat.fib (k*p) / Nat.fib p).gcd (Nat.fib p) = k.gcd (Nat.fib p) := by
  have hd := Nat.fib_dvd p (k*p) (dvd_mul_left p k)
  have h := (fibMulFirstOrder p hp k).1
  have hc : Nat.fib (k*p) / Nat.fib p ≡ k * Nat.fib (p+1) ^ (k-1) [MOD Nat.fib p] := by
    apply Nat.ModEq.mul_right_cancel' (Nat.fib_pos.mpr hp).ne'
    rw [Nat.div_mul_cancel hd]
    simpa only [pow_two] using h
  rw [hc.gcd_eq]
  simpa only [Nat.gcd_comm (Nat.fib p), Nat.mul_comm (Nat.fib (p+1) ^ (k-1))] using
    ((Nat.fib_coprime_fib_succ p).symm.pow_left (k-1)).gcd_mul_left_cancel_right k

/-- A multiplier coprime to q preserves every q-power divisor of a term already divisible by q. -/
theorem fibPrimePowerAtMultiple {p q k e : ℕ} (hp : 0 < p) (hq : q.Prime)
    (hd : q ∣ Nat.fib p) (hk : ¬ q ∣ k) :
    q^e ∣ Nat.fib (k*p) ↔ q^e ∣ Nat.fib p := by
  let c := Nat.fib (k*p) / Nat.fib p
  have hf := Nat.fib_dvd p (k*p) (dvd_mul_left p k)
  have hc : ¬ q ∣ c := by
    intro h
    have hcg := Nat.dvd_gcd h hd
    change q ∣ (Nat.fib (k*p) / Nat.fib p).gcd (Nat.fib p) at hcg
    rw [fibQuotientGcd hp k] at hcg
    exact hk (hcg.trans (Nat.gcd_dvd_left _ _))
  have hcop := (hq.coprime_iff_not_dvd.mpr hc).pow_left e
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left (by simpa [c, Nat.div_mul_cancel hf] using h), fun h => h.trans hf⟩

/-- For a prime factor at a prime index, its multiplicity can be read off the two neighbors. -/
theorem fibPrimePowerAtNeighbors {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hq : q.Prime)
    (hd : q ∣ Nat.fib p) (e : ℕ) :
    q^e ∣ Nat.fib p ↔ q^e ∣ Nat.fib (q-1) ∨ q^e ∣ Nat.fib (q+1) := by
  constructor
  · intro he
    exact (fibPrimeFactorCongruence hp hp5 hq hd).imp
      (fun h => he.trans (Nat.fib_dvd _ _ h)) (fun h => he.trans (Nat.fib_dvd _ _ h))
  · cases e with
    | zero => simp
    | succ e =>
      have descend (t : ℕ) (ht : ¬ q ∣ t) (he : q^(e+1) ∣ Nat.fib t) : q^(e+1) ∣ Nat.fib p := by
        have hqt : q ∣ Nat.fib t := dvd_trans (dvd_pow_self q (by omega : e+1 ≠ 0)) he
        obtain ⟨k, hk⟩ := indexDividesFromCommonFactor hp hq.one_lt hd hqt
        have hqk : ¬ q ∣ k := fun h => ht (hk ▸ (h.trans (dvd_mul_left k p)))
        rw [hk, Nat.mul_comm p k] at he
        exact (fibPrimePowerAtMultiple hp.pos hq hd hqk).mp he
      have hq2 := hq.two_le
      have hminus : ¬ q ∣ q-1 := by
        intro h
        have := Nat.le_of_dvd (by omega : 0 < q-1) h
        omega
      have hplus : ¬ q ∣ q+1 := by
        intro h
        exact hq.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp h)
      exact fun h => h.elim (descend _ hminus) (descend _ hplus)
end MathGacha
