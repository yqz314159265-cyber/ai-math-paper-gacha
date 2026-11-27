import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Gacha.Reduction
open GaussianInt
namespace MathGacha

def gaussianFibPair (a b : ℕ) : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩

def gaussianFibValue (k : ℕ) : GaussianInt := gaussianFibPair (Nat.fib (k + 1)) (Nat.fib k)

theorem gaussianFibOddEqSqAdd (k : ℕ) : Nat.fib (2 * k + 1) = Nat.fib (k + 1)^2 + Nat.fib k^2 := by
  rw [show 2 * k + 1 = k + k + 1 by omega, Nat.fib_add]
  ring

theorem gaussianFibSuccessorCoprime (k : ℕ) : Nat.Coprime (Nat.fib k) (Nat.fib (k + 1)) := by
  simpa using Nat.fib_coprime_fib_succ k

theorem gaussianFibPairNorm (a b : ℕ) : (gaussianFibPair a b).norm.natAbs = a^2+b^2 := by
  simp only [gaussianFibPair, Zsqrtd.norm_def]
  rw [show (a:ℤ)*(a:ℤ) - -1*(b:ℤ)*(b:ℤ) = (a:ℤ)*(a:ℤ)+(b:ℤ)*(b:ℤ) by ring]
  apply Int.ofNat_injective
  calc
    _ = (a:ℤ)*(a:ℤ)+(b:ℤ)*(b:ℤ) := Int.natAbs_of_nonneg (by positivity)
    _ = ↑(a^2+b^2) := by push_cast; ring

theorem gaussianFibValueNorm (k : ℕ) : (gaussianFibValue k).norm.natAbs = Nat.fib (2*k+1) := by
  rw [gaussianFibOddEqSqAdd]
  simpa [gaussianFibValue] using gaussianFibPairNorm (Nat.fib (k+1)) (Nat.fib k)

theorem gaussianFibIrreducibleOfPrimeNorm {z : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hn : z.norm.natAbs = p) : Irreducible z := by
  rw [irreducible_iff]
  constructor
  · intro hz
    have hunit : z.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hz
    rw [hn] at hunit
    exact hp.ne_one hunit
  · intro a b hab
    have hnorm : p = a.norm.natAbs * b.norm.natAbs := by
      rw [← hn, hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rcases hp.eq_one_or_self_of_dvd (a.norm.natAbs) ⟨b.norm.natAbs, hnorm⟩ with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : b.norm.natAbs = 1 :=
        (Nat.mul_eq_left hp.ne_zero).mp (by simpa [ha] using hnorm.symm)
      exact Zsqrtd.norm_eq_one_iff.mp hb

theorem gaussianFibPrimeDivisorOfNatDivisor {z : GaussianInt} (hz : Prime z)
    {n : ℕ} (hn : 1 < n) (hzn : z ∣ (n : GaussianInt)) :
    ∃ q : ℕ, q.Prime ∧ z ∣ (q : GaussianInt) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hprime : n.Prime
    · exact ⟨n, hprime, hzn⟩
    · obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hn)
      obtain ⟨m, rfl⟩ := hqdiv
      have hmpos : 0 < m := by
        by_contra hm
        simp at hm
        simp [hm] at hn
      have hmlt : m < q * m := by
        calc
          m = 1 * m := by simp
          _ < q * m := Nat.mul_lt_mul_of_pos_right hq.one_lt hmpos
      have hmul : z ∣ (q : GaussianInt) * (m : GaussianInt) := by
        simpa only [Nat.cast_mul] using hzn
      rcases hz.dvd_mul.mp hmul with hqz | hmz
      · exact ⟨q, hq, hqz⟩
      · have hmne1 : m ≠ 1 := by
          intro hm
          apply hprime
          subst m
          simpa using hq
        have hmgt1 : 1 < m := by omega
        exact ih m hmlt hmgt1 hmz

theorem gaussianFibPairIrreducibleIffNormPrime {a b : ℕ}
    (hab : Nat.Coprime a b) (hN : 1 < a^2+b^2) :
    Irreducible (gaussianFibPair a b) ↔ Nat.Prime (a^2+b^2) := by
  let z := gaussianFibPair a b
  have hn : z.norm.natAbs = a^2+b^2 := gaussianFibPairNorm a b
  constructor
  · intro hirr
    have hprimeZ : Prime z := (irreducible_iff_prime).mp hirr
    have hnormInt : z.norm = (a^2+b^2 : ℕ) := by
      have h := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)
      rw [hn] at h
      exact h.symm
    have hzdvd : z ∣ ((a^2+b^2 : ℕ) : GaussianInt) := by
      have hzNormDvd : z ∣ z.norm := ⟨star z, Zsqrtd.norm_eq_mul_conj z⟩
      simpa [hnormInt] using hzNormDvd
    obtain ⟨q, hq, hzq⟩ := gaussianFibPrimeDivisorOfNatDivisor hprimeZ hN hzdvd
    obtain ⟨w, hw⟩ := hzq
    have hprod : (a^2+b^2) * w.norm.natAbs = q^2 := by
      calc
        (a^2+b^2) * w.norm.natAbs = z.norm.natAbs * w.norm.natAbs := by rw [hn]
        _ = (z*w).norm.natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = ((q:GaussianInt).norm).natAbs := by rw [← hw]
        _ = q^2 := by
          have hcast : ((q:GaussianInt).norm).natAbs = q^2 := by
            rw [Zsqrtd.norm_natCast]
            apply Int.ofNat_injective
            calc
              _ = (q:ℤ) * q := Int.natAbs_of_nonneg (by positivity)
              _ = ↑(q^2) := by push_cast; ring
          exact hcast
    have hdivpow : a^2+b^2 ∣ q^2 := ⟨w.norm.natAbs, hprod.symm⟩
    obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow hq).mp hdivpow
    interval_cases i
    · simp at hni
      omega
    · simpa [hni] using hq
    · simp only [pow_two] at hni
      have hNq : a^2+b^2 = q^2 := by simpa [pow_two] using hni
      have hwone : w.norm.natAbs = 1 := by
        rw [hNq] at hprod
        exact (Nat.mul_eq_left (pow_ne_zero 2 hq.ne_zero)).mp hprod
      have hwunit : IsUnit w := Zsqrtd.norm_eq_one_iff.mp hwone
      obtain ⟨v, hv⟩ := (isUnit_iff_dvd_one.mp hwunit)
      have hzqmul : z = (q:GaussianInt) * v := by
        calc
          z = z * 1 := by simp
          _ = z * (w * v) := by rw [← hv]
          _ = (z*w) * v := by ac_rfl
          _ = (q:GaussianInt) * v := by rw [← hw]
      have hcoords : q ∣ a ∧ q ∣ b := by
        have h' : (q:ℤ) ∣ z.re ∧ (q:ℤ) ∣ z.im :=
          (Zsqrtd.intCast_dvd q z).mp ⟨v, hzqmul⟩
        constructor
        · exact Int.natCast_dvd_natCast.mp (by simpa [z, gaussianFibPair] using h'.1)
        · exact Int.natCast_dvd_natCast.mp (by simpa [z, gaussianFibPair] using h'.2)
      exact False.elim ((Nat.not_coprime_of_dvd_of_dvd hq.one_lt hcoords.1 hcoords.2) hab)
  · intro hp
    apply gaussianFibIrreducibleOfPrimeNorm hp
    exact hn
theorem gaussianFibPrimeIff (k : ℕ) (hp : 5 ≤ 2*k+1) :
    Irreducible (gaussianFibValue k) ↔ Nat.Prime (Nat.fib (2*k+1)) := by
  have hN : 1 < Nat.fib (2*k+1) := by
    have hidx : 1 < 2*k+1 := by omega
    exact lt_of_lt_of_le hidx (Nat.le_fib_self hp)
  have hcop : Nat.Coprime (Nat.fib (k+1)) (Nat.fib k) :=
    (gaussianFibSuccessorCoprime k).symm
  have hNsum : 1 < Nat.fib (k+1)^2 + Nat.fib k^2 := by
    rw [← gaussianFibOddEqSqAdd]
    exact hN
  have hiff := gaussianFibPairIrreducibleIffNormPrime hcop hNsum
  rw [gaussianFibValue, gaussianFibOddEqSqAdd]
  exact hiff

def pellForm (x y : ℕ) : ℤ := (x:ℤ)^2 - (x:ℤ)*(y:ℤ) - (y:ℤ)^2

theorem gaussianFibPellIdentity (k : ℕ) : |pellForm (Nat.fib (k+1)) (Nat.fib k)| = 1 := by
  have hsign : pellForm (Nat.fib (k+1)) (Nat.fib k) = (-1:ℤ)^k := by
    induction k with
    | zero => norm_num [pellForm]
    | succ k ih =>
      change pellForm (Nat.fib (k+2)) (Nat.fib (k+1)) = (-1:ℤ)^(k+1)
      rw [show Nat.fib (k+2) = Nat.fib k + Nat.fib (k+1) by rw [Nat.fib_add_two]]
      rw [pow_succ]
      dsimp [pellForm] at ih ⊢
      nlinarith [ih]
  rw [hsign]
  simp [abs_pow]

theorem pellPairIsFibonacci (X Y : ℕ) (hYX : Y ≤ X)
    (hP : |pellForm X Y| = 1) :
    ∃ k, X = Nat.fib (k+1) ∧ Y = Nat.fib k := by
  induction X using Nat.strong_induction_on generalizing Y with
  | h X ih =>
    by_cases hy0 : Y = 0
    · subst Y
      have hXsq : (X:ℤ)^2 = 1 := by
        have hh : |(X:ℤ)^2| = 1 := by simpa [pellForm] using hP
        rw [abs_of_nonneg (sq_nonneg _)] at hh
        exact hh
      have hXint : (X:ℤ) = 1 := by
        have hn : 0 ≤ (X:ℤ) := by positivity
        nlinarith
      have hX : X = 1 := by exact_mod_cast hXint
      exact ⟨0, by simp [hX], by simp⟩
    · by_cases hXY : X = Y
      · subst Y
        have hform : pellForm X X = -(X:ℤ)^2 := by dsimp [pellForm]; ring
        rw [hform] at hP
        have hh : |-(X:ℤ)^2| = 1 := hP
        have hXsq : (X:ℤ)^2 = 1 := by
          rw [abs_neg, abs_of_nonneg (sq_nonneg _)] at hh
          exact hh
        have hXint : (X:ℤ) = 1 := by
          have hn : 0 ≤ (X:ℤ) := by positivity
          nlinarith
        have hX : X = 1 := by exact_mod_cast hXint
        exact ⟨1, by simp [hX], by simp [hX]⟩
      · have hXYlt : Y < X := by omega
        have hYpos : 0 < Y := Nat.pos_of_ne_zero hy0
        have hDupper : pellForm X Y ≤ 1 := by
          by_cases hnonneg : 0 ≤ pellForm X Y
          · rw [abs_of_nonneg hnonneg] at hP
            omega
          · omega
        have hbound : X ≤ 2*Y := by
          by_contra hnot
          have hXbig : 2*Y < X := by omega
          have hprod : 0 < ((X:ℤ)-2*(Y:ℤ))*((X:ℤ)+(Y:ℤ)) := by
            apply mul_pos
            · have hh : 2*(Y:ℤ) < (X:ℤ) := by exact_mod_cast hXbig
              linarith
            · positivity
          have hformula : pellForm X Y = ((X:ℤ)-2*(Y:ℤ))*((X:ℤ)+(Y:ℤ))+(Y:ℤ)^2 := by
            dsimp [pellForm]
            ring
          have hYsq : (1:ℤ) ≤ (Y:ℤ)^2 := by
            have hy : (1:ℤ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
            nlinarith
          rw [hformula] at hDupper
          nlinarith
        let X' := Y
        let Y' := X-Y
        have hY'le : Y' ≤ X' := by dsimp [X',Y']; omega
        have hflip : pellForm X' Y' = - pellForm X Y := by
          dsimp [X',Y',pellForm]
          rw [Int.ofNat_sub hXYlt.le]
          ring
        have hP' : |pellForm X' Y'| = 1 := by rw [hflip, abs_neg]; exact hP
        obtain ⟨k, hkX, hkY⟩ := ih Y hXYlt Y' hY'le hP'
        refine ⟨k+1, ?_, hkX⟩
        dsimp [X',Y'] at hkY
        calc
          X = Y + (X-Y) := by omega
          _ = Nat.fib (k+1) + Nat.fib k := by omega
          _ = Nat.fib (k+2) := by rw [Nat.fib_add_two]; omega

theorem pellPairIffFibonacci (X Y : ℕ) (hYX : Y ≤ X) :
    |pellForm X Y| = 1 ↔ ∃ k, X = Nat.fib (k+1) ∧ Y = Nat.fib k := by
  constructor
  · exact pellPairIsFibonacci X Y hYX
  · rintro ⟨k, rfl, rfl⟩
    exact gaussianFibPellIdentity k
theorem pellPairIffGaussianFibValue (X Y : ℕ) (hYX : Y ≤ X) :
    |pellForm X Y| = 1 ↔ ∃ k, gaussianFibPair X Y = gaussianFibValue k := by
  rw [pellPairIffFibonacci X Y hYX]
  constructor
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, h⟩
    have hre := congrArg Zsqrtd.re h
    have him := congrArg Zsqrtd.im h
    simp [gaussianFibValue, gaussianFibPair] at hre him
    exact ⟨k, hre, him⟩


/-- The original infinitude assertion is equivalent to unbounded Gaussian Fibonacci primes. -/
theorem originalIffUnboundedGaussianFibPrimes :
    Original ↔ ∀ B : ℕ, ∃ k > B, Nat.Prime (2*k+1) ∧
      Irreducible (gaussianFibValue k) := by
  rw [originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p, hpgt, hp, hFib⟩ := h (max (2*B+1) 5)
    have hp5 : 5 ≤ p := by omega
    have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
    let k := p / 2
    have hindex : p = 2*k+1 := by
      dsimp [k]
      have hdiv := Nat.mod_add_div p 2
      omega
    have hkB : B < k := by omega
    refine ⟨k, hkB, ?_, ?_⟩
    · rw [← hindex]
      exact hp
    · have hFib' : Nat.Prime (Nat.fib (2*k+1)) := by rw [← hindex]; exact hFib
      have hk5 : 5 ≤ 2*k+1 := by omega
      exact (gaussianFibPrimeIff k hk5).2 hFib'
  · intro h B
    obtain ⟨k, hk, hp, hG⟩ := h (max B 2)
    have hp5 : 5 ≤ 2*k+1 := by omega
    refine ⟨2*k+1, ?_, hp, ?_⟩
    · omega
    · exact (gaussianFibPrimeIff k hp5).1 hG

end MathGacha