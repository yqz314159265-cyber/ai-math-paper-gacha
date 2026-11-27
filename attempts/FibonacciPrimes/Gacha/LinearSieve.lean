import Gacha.FactorRank
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace MathGacha

/-- Freeze each of the two linear forms at the residue 3. -/
def linearFormsModulus (K : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 K, (3*k+1)*(3*k-1)

theorem linearFormsModulusCoprime (K : ℕ) : Nat.Coprime 3 (linearFormsModulus K) := by
  apply Nat.Coprime.prod_right
  intro k hk
  have hkpos := (Finset.mem_Icc.mp hk).1
  have hthree : Nat.Prime 3 := by decide
  apply Nat.Coprime.mul_right
  · exact hthree.coprime_iff_not_dvd.mpr (by omega)
  · exact hthree.coprime_iff_not_dvd.mpr (by omega)

/-- The proper factors work for every index in the class above 3. -/
theorem compositeLinearFormsOnClass {p K : ℕ} (hgt : 3 < p)
    (hmod : p ≡ 3 [MOD linearFormsModulus K]) :
    ∀ k : ℕ, 1 ≤ k → k ≤ K → ¬ (k*p+1).Prime ∧ ¬ (k*p-1).Prime := by
  let S := Finset.Icc 1 K
  let f (k : ℕ) := (3*k+1)*(3*k-1)
  let M := linearFormsModulus K
  intro k hkpos hkK
  have hkM : f k ∣ M := Finset.dvd_prod_of_mem f (Finset.mem_Icc.mpr ⟨hkpos,hkK⟩)
  have hdiv : f k ∣ k*(p-3) :=
    dvd_mul_of_dvd_right (hkM.trans hmod.symm.dvd') _
  have he : k*p = 3*k+k*(p-3) := by
    calc k*p = k*(3+(p-3)) := congrArg (k*·) (by omega)
         _ = _ := by ring
  have hless : 3*k < k*p := by
    rw [Nat.mul_comm 3 k]
    exact Nat.mul_lt_mul_of_pos_left (by omega) hkpos
  have hplus : 3*k+1 ∣ k*p+1 := by
    rw [show k*p+1 = (3*k+1)+k*(p-3) by omega]
    exact dvd_add dvd_rfl ((dvd_mul_right (3*k+1) (3*k-1)).trans hdiv)
  have hminus : 3*k-1 ∣ k*p-1 := by
    rw [show k*p-1 = (3*k-1)+k*(p-3) by omega]
    exact dvd_add dvd_rfl ((dvd_mul_left (3*k-1) (3*k+1)).trans hdiv)
  constructor
  · intro prime
    have heq := (Nat.dvd_prime_two_le prime (by omega : 2 ≤ 3*k+1)).mp hplus
    omega
  · intro prime
    have heq := (Nat.dvd_prime_two_le prime (by omega : 2 ≤ 3*k-1)).mp hminus
    omega

/-- Dirichlet primes in the class of 3 force an entire finite collection of linear forms
to have explicit proper divisors, namely the values of those forms at 3. -/
theorem arbitrarilyLargePrimeWithCompositeLinearForms (K B : ℕ) :
    ∃ p > B, p.Prime ∧ ∀ k : ℕ, 1 ≤ k → k ≤ K →
      ¬ (k*p+1).Prime ∧ ¬ (k*p-1).Prime := by
  have hcop := linearFormsModulusCoprime K
  have hM : linearFormsModulus K ≠ 0 := by intro hzero; simp [hzero] at hcop
  obtain ⟨p, hgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max B 3) hM hcop
  exact ⟨p, by omega, hp, compositeLinearFormsOnClass (by omega) hmod⟩

/-- All prime indices in this class above five escape the moving cutoff. -/
theorem leastFactorBoundOnClass {p K : ℕ} (hp : p.Prime) (hlarge : 5 < p)
    (hmod : p ≡ 3 [MOD linearFormsModulus K]) : K*p < (Nat.fib p).minFac := by
  have hterm := Nat.le_fib_self hlarge.le
  exact noSmallFactorFromCompositeForms hp hlarge (compositeLinearFormsOnClass (by omega) hmod)
    (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)

/-- The least prime factor divided by the prime index is unbounded, even on every tail. -/
theorem unboundedLeastFactorOverIndex (K B : ℕ) :
    ∃ p > B, p.Prime ∧ K*p < (Nat.fib p).minFac := by
  obtain ⟨p, hlarge, hp, hforms⟩ := arbitrarilyLargePrimeWithCompositeLinearForms K (max B 5)
  have h5 : 5 < p := by omega
  have hterm := Nat.le_fib_self h5.le
  exact ⟨p, by omega, hp, noSmallFactorFromCompositeForms hp h5 hforms
    (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)⟩

end MathGacha
