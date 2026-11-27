import Gacha.DicksonSieve
import Gacha.DicksonTests
import Gacha.Drobot
import Gacha.FactorRank
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

open Finset

namespace MathGacha

def maskedResidueProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if (i + 1).Prime ∧ (i + 1) % 4 = 1 then i + 1 else 1

def maskedModulus (n : ℕ) : ℕ := maskedResidueProduct n * primorial (Nat.sqrt n)

noncomputable def thetaOneModFour (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    if (i + 1).Prime ∧ (i + 1) % 4 = 1 then Real.log ((i + 1 : ℕ) : ℝ) else 0

theorem maskedResidueProduct_pos (n : ℕ) : 0 < maskedResidueProduct n := by
  apply Finset.prod_pos
  intro i hi
  split <;> positivity

theorem maskedModulus_log_bound (n : ℕ) :
    Real.log (maskedModulus n : ℝ) ≤ thetaOneModFour n +
      Real.sqrt (n : ℝ) * Real.log 4 := by
  have hApos : 0 < maskedResidueProduct n := maskedResidueProduct_pos n
  have hBpos : 0 < primorial (Nat.sqrt n) := primorial_pos _
  have hlogA : Real.log (maskedResidueProduct n : ℝ) = thetaOneModFour n := by
    change Real.log ((∏ i ∈ Finset.range n,
      if (i + 1).Prime ∧ (i + 1) % 4 = 1 then i + 1 else 1 : ℕ) : ℝ) = _
    rw [Nat.cast_prod, Real.log_prod]
    · unfold thetaOneModFour
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    · intro i hi
      have : 0 < (if (i + 1).Prime ∧ (i + 1) % 4 = 1 then i + 1 else 1 : ℕ) := by
        split_ifs <;> positivity
      exact_mod_cast this.ne'
  have hsmallNat := primorial_le_four_pow (Nat.sqrt n)
  have hsmall : (primorial (Nat.sqrt n) : ℝ) ≤ (4 : ℝ) ^ Nat.sqrt n := by exact_mod_cast hsmallNat
  have hlogSmall := Real.log_le_log (by exact_mod_cast hBpos) hsmall
  rw [Real.log_pow] at hlogSmall
  have hroot : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' n
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hsmall' : (Nat.sqrt n : ℝ) * Real.log 4 ≤ Real.sqrt (n : ℝ) * Real.log 4 :=
    mul_le_mul_of_nonneg_right hroot hlog4
  have hmul : Real.log (maskedModulus n : ℝ) =
      Real.log (maskedResidueProduct n : ℝ) +
      Real.log (primorial (Nat.sqrt n) : ℝ) := by
    rw [maskedModulus, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rw [hmul, hlogA]
  linarith

/-- Every prime in the mask divides the modulus. -/
theorem maskedPrime_dvd_modulus {n r : ℕ} (hr : r.Prime) (hrle : r ≤ n)
    (hmask : r % 4 = 1 ∨ r ^ 2 ≤ n) : r ∣ maskedModulus n := by
  rcases hmask with hfour | hsmall
  · have hi : r - 1 ∈ Finset.range n := by simp; omega
    have hdiv : (if ((r - 1) + 1).Prime ∧ ((r - 1) + 1) % 4 = 1
        then (r - 1) + 1 else 1) ∣ maskedResidueProduct n := by
      unfold maskedResidueProduct
      exact Finset.dvd_prod_of_mem _ hi
    have hterm : (if ((r - 1) + 1).Prime ∧ ((r - 1) + 1) % 4 = 1
        then (r - 1) + 1 else 1) = r := by
      rw [Nat.sub_add_cancel hr.one_le]
      simp [hr, hfour]
    have hrA : r ∣ maskedResidueProduct n := by simpa [hterm] using hdiv
    exact dvd_mul_of_dvd_left hrA _
  · have hrleSqrt : r ≤ Nat.sqrt n := Nat.le_sqrt'.2 hsmall
    have hrB : r ∣ primorial (Nat.sqrt n) := hr.dvd_primorial_iff.mpr hrleSqrt
    exact dvd_mul_of_dvd_right hrB _

/-- The sparse prime mask excludes every prime Fibonacci divisor up to `Kp`.
The modulus contains primes `r ≤ K+1` with `r ≡ 1 mod 4` or `r² ≤ K+1`. -/
theorem leastFactorBoundOnMaskedClass {p K : ℕ} (hK : 4 ≤ K) (hp : p.Prime)
    (hp5 : 5 < p)
    (hmod : p ≡ 1 [MOD maskedModulus (K + 1)]) :
    K * p < (Nat.fib p).minFac := by
  have h5divA : 5 ∣ maskedResidueProduct (K + 1) := by
    unfold maskedResidueProduct
    have hmem : 4 ∈ Finset.range (K + 1) := by simp; omega
    have hdvd := Finset.dvd_prod_of_mem
      (fun i => if (i + 1).Prime ∧ (i + 1) % 4 = 1 then i + 1 else 1) hmem
    norm_num at hdvd
    exact hdvd
  have hMdiv : maskedModulus (K + 1) ∣ p - 1 := hmod.symm.dvd'
  have h5p : 5 ∣ p - 1 := h5divA.trans (dvd_mul_of_dvd_left (dvd_refl _) _) |>.trans hMdiv
  have hpmod5 : p % 5 = 1 := by omega
  let q := (Nat.fib p).minFac
  have hterm : 1 < Nat.fib p := by
    have := Nat.le_fib_self hp5.le
    omega
  have hq : q.Prime := Nat.minFac_prime (by
    have : Nat.fib p ≠ 1 := by omega
    exact this)
  have hqdiv : q ∣ Nat.fib p := by
    dsimp [q]
    exact Nat.minFac_dvd _
  have hgap : 4 * p + 1 ≤ q := by
    have hg : 4 * p + 1 ≤ (Nat.fib p).minFac :=
      (leastFactorGap hp hp5).mpr (by
        intro hx
        rcases hx with ⟨_, hx⟩
        omega)
    exact hg
  by_contra! hbad
  have hq5 : 5 < q := by omega
  have hindex : p ∣ neighborIndex q := (primeDivisorIffDickson hp hq hq5).mp hqdiv |>.1
  let j := neighborIndex q / p
  have hj : j * p = neighborIndex q := by
    dsimp [j]
    exact Nat.div_mul_cancel hindex
  have hjle : j ≤ K := by
    have hN : neighborIndex q ≤ q + 1 := by
      unfold neighborIndex
      split <;> omega
    by_contra! h
    have hm := Nat.mul_le_mul_right p h
    rw [Nat.succ_mul] at hm
    rw [← hj] at hN
    omega
  have hres := divisorMultiplierResidues hp hp5 hq hq5 hqdiv hj
  rcases hres with hplus | hminus
  · rcases hplus with ⟨hqform, hj4, _⟩
    let n := j + 1
    have hnmod : n % 4 = 1 := by
      dsimp [n]
      rw [Nat.add_mod, hj4]
    have hjlarge : 4 ≤ j := by
      by_contra! h
      have hm := Nat.mul_le_mul_right p (show j ≤ 3 by omega)
      rw [hqform] at hgap
      omega
    have hnle : n ≤ K + 1 := by
      dsimp [n]
      exact Nat.add_le_add_right hjle 1
    have hnn : 1 < n := by dsimp [n]; omega
    have hrprime : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hrdivn : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hrle : Nat.minFac n ≤ n := Nat.minFac_le (by omega)
    have hrmask : (Nat.minFac n) % 4 = 1 ∨ (Nat.minFac n) ^ 2 ≤ K + 1 := by
      by_cases hnprime : n.Prime
      · have hrEq : Nat.minFac n = n :=
          (Nat.prime_dvd_prime_iff_eq hrprime hnprime).mp hrdivn
        left
        rw [hrEq]
        exact hnmod
      · right
        exact (Nat.minFac_sq_le_self (by omega) hnprime).trans hnle
    have hrM := maskedPrime_dvd_modulus hrprime (hrle.trans hnle) hrmask
    have hrp : Nat.minFac n ∣ p - 1 := hrM.trans hMdiv
    have hrq : Nat.minFac n ∣ q := by
      have hident : q = n + j * (p - 1) := by
        have hpdecomp : p = 1 + (p - 1) := by omega
        have hmulid : j * p = j + j * (p - 1) := by
          calc
            j * p = j * (1 + (p - 1)) := congrArg (fun x : ℕ => j * x) hpdecomp
            _ = j + j * (p - 1) := by ring
        have hqeq := hqform
        rw [hmulid] at hqeq
        dsimp [n]
        omega
      rw [hident]
      exact dvd_add hrdivn (dvd_mul_of_dvd_right hrp j)
    have hp3 : 3 ≤ p := by omega
    have hmul3 : 3 * j ≤ j * p := by
      calc
        3 * j = j * 3 := by ring
        _ ≤ j * p := Nat.mul_le_mul_left j hp3
    have hrLt : Nat.minFac n < q := by
      rw [hqform]
      dsimp [n] at hrle
      nlinarith only [hrle, hmul3, hjlarge]
    have hrEq : Nat.minFac n = q :=
      (Nat.prime_dvd_prime_iff_eq hrprime hq).mp hrq
    omega
  · rcases hminus with ⟨hqform, hj4, _⟩
    have hjlarge : 5 ≤ j := by
      by_contra! h
      have hm := Nat.mul_le_mul_right p (show j ≤ 4 by omega)
      have hqlo : 4 * p + 2 ≤ q + 1 := by omega
      rw [hqform] at hqlo
      nlinarith only [hqlo, hm]
    let n := j - 1
    have hnmod : n % 4 = 1 := by
      have hjdecomp : j = 4 * (j / 4) + 2 := by
        have h := Nat.mod_add_div j 4
        rw [hj4] at h
        omega
      rw [show n = 4 * (j / 4) + 1 by dsimp [n]; omega]
      norm_num [Nat.add_mod, Nat.mul_mod]
    have hnle : n ≤ K + 1 := by
      dsimp [n]
      exact (Nat.sub_le j 1).trans (by omega : j ≤ K + 1)
    have hnn : 1 < n := by dsimp [n]; omega
    have hrprime : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hrdivn : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hrle : Nat.minFac n ≤ n := Nat.minFac_le (by omega)
    have hrmask : (Nat.minFac n) % 4 = 1 ∨ (Nat.minFac n) ^ 2 ≤ K + 1 := by
      by_cases hnprime : n.Prime
      · have hrEq : Nat.minFac n = n :=
          (Nat.prime_dvd_prime_iff_eq hrprime hnprime).mp hrdivn
        left
        rw [hrEq]
        exact hnmod
      · right
        exact (Nat.minFac_sq_le_self (by omega) hnprime).trans hnle
    have hrM := maskedPrime_dvd_modulus hrprime (hrle.trans hnle) hrmask
    have hrp : Nat.minFac n ∣ p - 1 := hrM.trans hMdiv
    have hrq : Nat.minFac n ∣ q := by
      have hident : q = n + j * (p - 1) := by
        have hpdecomp : p = 1 + (p - 1) := by omega
        have hmulid : j * p = j + j * (p - 1) := by
          calc
            j * p = j * (1 + (p - 1)) := congrArg (fun x : ℕ => j * x) hpdecomp
            _ = j + j * (p - 1) := by ring
        have hqeq := hqform
        rw [hmulid] at hqeq
        dsimp [n] at hqeq ⊢
        omega
      rw [hident]
      exact dvd_add hrdivn (dvd_mul_of_dvd_right hrp j)
    have hp3 : 3 ≤ p := by omega
    have hmul3 : 3 * j ≤ j * p := by
      calc
        3 * j = j * 3 := by ring
        _ ≤ j * p := Nat.mul_le_mul_left j hp3
    have hrLt : Nat.minFac n < q := by
      have hqeq : q + 1 = j * p := hqform
      dsimp [n] at hrle
      have hqmin : 3 * j - 1 ≤ q := by omega
      change (j - 1).minFac < q
      omega
    have hrEq : Nat.minFac n = q :=
      (Nat.prime_dvd_prime_iff_eq hrprime hq).mp hrq
    omega

end MathGacha
