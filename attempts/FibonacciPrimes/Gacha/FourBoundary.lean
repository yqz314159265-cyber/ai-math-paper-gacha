import Gacha.DicksonSieve
import Gacha.Drobot
import Gacha.Frobenius
import Gacha.IndexResidue
import Gacha.SharpRank
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace MathGacha

/-- If the two roots exist, then the Fibonacci value vanishes exactly when
`a` is a nonsquare. -/
theorem fourBoundaryFibDvdIffNonsquare {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 < p) (hqp : q = 4 * p + 1)
    (a b : ZMod q) (ha : a ^ 2 = a + 1) (hb : b ^ 2 = b + 1)
    (hsum : a + b = 1) (hab : a * b = -1) (ha0 : a ≠ 0) (_hb0 : b ≠ 0) :
    q ∣ Nat.fib p ↔ ¬ IsSquare a := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : Fact q.Prime := ⟨hq⟩
  have hq5 : 5 < q := by omega
  have hne : a ≠ b := by
    intro heq
    have hsum' : a + a = 1 := by simpa [heq] using hsum
    have htwo : 2 * a = 1 := by simpa [two_mul] using hsum'
    have hfirst : 4 * a ^ 2 = 1 := by
      calc
        4 * a ^ 2 = (2 * a) ^ 2 := by ring
        _ = 1 := by rw [htwo]; norm_num
    have hsecond : 4 * a ^ 2 = 6 := by
      calc
        4 * a ^ 2 = 4 * (a + 1) := by rw [ha]
        _ = 2 * (2 * a) + 4 := by ring
        _ = 6 := by rw [htwo]; norm_num
    have h5zero : (5 : ZMod q) = 0 := by
      calc
        (5 : ZMod q) = 6 - 1 := by norm_num
        _ = 4 * a ^ 2 - 1 := by rw [hsecond.symm]
        _ = 0 := by rw [hfirst]; ring
    have hdiv : q ∣ 5 := (ZMod.natCast_eq_zero_iff 5 q).mp h5zero
    have hle : q ≤ 5 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hBinet : (Nat.fib p : ZMod q) * (a-b) = a^p-b^p := by
    calc
      _ = (a-b) * (Nat.fib p : ZMod q) := by ring
      _ = _ := fibPowerDifference ha hb p
  have hfib : (Nat.fib p : ZMod q) = 0 ↔ a ^ p = b ^ p := by
    constructor
    · intro hzero
      have hpowdiff : a ^ p - b ^ p = 0 := by simpa [hzero] using hBinet.symm
      exact sub_eq_zero.mp hpowdiff
    · intro hpow
      have hmul : (Nat.fib p : ZMod q) * (a - b) = 0 := by
        calc
          (Nat.fib p : ZMod q) * (a - b) = a ^ p - b ^ p := hBinet
          _ = 0 := by rw [hpow]; ring
      rcases mul_eq_zero.mp hmul with hf | hd
      · exact hf
      · exact False.elim (hne (sub_eq_zero.mp hd))
  have hbInv : b = -a⁻¹ := by
    calc
      b = (1 : ZMod q) * b := by ring
      _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel₀ ha0]
      _ = a⁻¹ * (a * b) := by ring
      _ = -a⁻¹ := by rw [hab]; ring
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hpRelation : a ^ p = b ^ p ↔ a ^ (2 * p) = -1 := by
    rw [hbInv, hpOdd.neg_pow]
    constructor
    · intro h
      calc
        a ^ (2 * p) = a ^ p * a ^ p := by rw [two_mul, pow_add]
        _ = - ((a⁻¹ ^ p) * a ^ p) := by rw [h]; ring
        _ = -1 := by rw [← mul_pow, inv_mul_cancel₀ ha0, one_pow]
    · intro h
      have hsq : a ^ p * a ^ p = -1 := by
        simpa [two_mul, pow_add] using h
      have hinv : (a⁻¹ ^ p) * a ^ p = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ ha0, one_pow]
      have hmul : a ^ p * a ^ p = (-(a⁻¹ ^ p)) * a ^ p := by
        calc
          _ = -1 := hsq
          _ = - ((a⁻¹ ^ p) * a ^ p) := by rw [hinv]
          _ = (-(a⁻¹ ^ p)) * a ^ p := by ring
      exact mul_right_cancel₀ (pow_ne_zero _ ha0) hmul
  have hqsub : q - 1 = 4 * p := by omega
  have hqdiv : q / 2 = 2 * p := by omega
  have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hEuler : IsSquare a ↔ a ^ (2 * p) = 1 := by
    rw [FiniteField.isSquare_iff hchar ha0, ZMod.card, hqdiv]
  have hfermat := ZMod.pow_card_sub_one_eq_one (p := q) (a := a) ha0
  have hpow2 : (a ^ (2 * p)) * (a ^ (2 * p)) = 1 := by
    calc
      _ = a ^ ((2 * p) * 2) := by rw [← pow_add]; congr 1; omega
      _ = a ^ (4 * p) := by congr 1; omega
      _ = a ^ (q - 1) := by rw [hqsub]
      _ = 1 := hfermat
  have hsign : a ^ (2 * p) = 1 ∨ a ^ (2 * p) = -1 := by
    apply mul_self_eq_one_iff.mp
    simpa [pow_two] using hpow2
  have hnegOne : (-1 : ZMod q) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod q) = 0 := by calc
      (2 : ZMod q) = 1 - (-1) := by norm_num
      _ = 0 := by rw [h]; ring
    have hqdiv2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h2
    have hqle2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) hqdiv2
    omega
  have hpowNonsquare : a ^ (2 * p) = -1 ↔ ¬ IsSquare a := by
    constructor
    · intro h hsq
      have heq := hEuler.mp hsq
      rw [h] at heq
      exact hnegOne heq
    · intro hnot
      have hneOne : a ^ (2 * p) ≠ 1 := fun heq => hnot (hEuler.mpr heq)
      rcases hsign with hOne | hNeg
      · exact False.elim (hneOne hOne)
      · exact hNeg
  have hcast := ZMod.natCast_eq_zero_iff (Nat.fib p) q
  exact hcast.symm.trans (hfib.trans (hpRelation.trans hpowNonsquare))

/-- The prime relation forces `q ≡ 5 mod 8`. -/
theorem fourBoundaryQModEight {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hqp : q = 4 * p + 1) : q % 8 = 5 := by
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  rcases hpOdd with ⟨k, hk⟩
  rw [hqp, hk]
  omega

/-- The explicit root condition supplies the companion root required by the
Binet criterion. -/
theorem fourBoundaryFibDvdOfNonsquare {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 < p) (hqp : q = 4*p+1)
    (a : ZMod q) (ha : a^2 = a+1) (hna : ¬ IsSquare a) : q ∣ Nat.fib p := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : Fact q.Prime := ⟨hq⟩
  let b : ZMod q := 1-a
  have hb : b^2 = b+1 := by
    dsimp [b]
    calc
      (1-a)^2 = 1-2*a+a^2 := by ring
      _ = 1-a+1 := by rw [ha]; ring
  have hsum : a+b=1 := by dsimp [b]; ring
  have hab : a*b=-1 := by
    dsimp [b]
    linear_combination a*hsum - ha
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz] at ha
    norm_num at ha
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz] at hab
    norm_num at hab
  exact (fourBoundaryFibDvdIffNonsquare hp hq hp5 hqp a b ha hb hsum hab ha0 hb0).mpr hna

/-- A boundary-size Fibonacci divisor is prime: every prime divisor has size
at least 2p−1, so a composite divisor would be at least (2p−1)². -/
theorem fourBoundaryPrimeOfDvd {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hqp : q = 4*p+1) (hd : q ∣ Nat.fib p) : q.Prime := by
  by_contra hc
  have hminPrime := Nat.minFac_prime (by omega : q ≠ 1)
  have hlow := fibLeastFactorLinearBound hp hp5 hminPrime ((Nat.minFac_dvd q).trans hd)
  have hsq := Nat.minFac_sq_le_self (by omega) hc
  have hle : 2*p-1 ≤ q.minFac := by omega
  have hh : (2*p-1)^2 ≤ q.minFac^2 := by gcongr
  have hupper : q < (2*p-1)^2 := by
    rw [hqp]
    nlinarith [Nat.zero_le ((2*p-1)*(2*p-1-4)),
      Nat.mul_le_mul_left (2*p-1) (show 5 ≤ 2*p-1 by omega)]
  omega

/-- Exact characterization of divisibility at the boundary q=4p+1. -/
theorem fourBoundaryCriterion {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hqp : q = 4*p+1) :
    q ∣ Nat.fib p ↔ q.Prime ∧ p % 5 = 2 ∧
      ∃ a : ZMod q, a^2 = a+1 ∧ ¬ IsSquare a := by
  constructor
  · intro hd
    have hq : q.Prime := fourBoundaryPrimeOfDvd hp hp5 hqp hd
    have hq5 : 5 < q := by omega
    let : Fact q.Prime := ⟨hq⟩
    have hDick := (primeDivisorIffDickson hp hq hq5).mp hd
    have hbranch : neighborIndex q = q-1 ∨ neighborIndex q=q+1 := by
      unfold neighborIndex
      split <;> simp
    have hnotPlus : neighborIndex q ≠ q+1 := by
      intro he
      have hdiv2 : p ∣ 2 := by
        have hdvd : p ∣ 2 + 4*p := by
          have h := hDick.1
          rw [he, hqp] at h
          convert h using 1; omega
        have hdiv := Nat.dvd_sub hdvd (dvd_mul_left p 4)
        simpa using hdiv
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv2
      omega
    have hminus : neighborIndex q=q-1 := hbranch.resolve_right hnotPlus
    have hqmodne : q%5 ≠ 2 ∧ q%5 ≠ 3 := by
      constructor
      · intro heq
        unfold neighborIndex at hminus
        simp [heq] at hminus
        omega
      · intro heq
        unfold neighborIndex at hminus
        simp [heq] at hminus
        omega
    have hqclass : q%5=1 ∨ q%5=4 := by
      have hlt : q%5 < 5 := Nat.mod_lt _ (by norm_num)
      have hqmodne0 : q%5≠0 := by
        intro hz
        have hdiv5 : 5∣q := Nat.dvd_of_mod_eq_zero hz
        have heq : q=5 := (((Nat.dvd_prime hq).mp hdiv5).resolve_left (by norm_num)).symm
        omega
      interval_cases h : q%5 <;> omega
    have hpmod : p%5=2 := by
      have hlt : p%5<5 := Nat.mod_lt _ (by norm_num)
      have hrelation : q%5 = (4*(p%5)+1)%5 := by rw [hqp]; omega
      have hp5ne : p%5 ≠ 0 := by
        intro hzero
        have hdiv5 : 5∣p := Nat.dvd_of_mod_eq_zero hzero
        have heq : p=5 := (((Nat.dvd_prime hp).mp hdiv5).resolve_left (by norm_num)).symm
        omega
      interval_cases h : p%5 <;> norm_num [h] at hrelation <;> omega
    have hfive : (5 : ZMod q) ≠ 0 := by
      intro hz
      have hd5 : q ∣ 5 := (ZMod.natCast_eq_zero_iff 5 q).mp hz
      have := Nat.le_of_dvd (by norm_num : 0 < 5) hd5
      omega
    have hchar := legendreSym.eq_one_or_neg_one q (a:=5) (by exact_mod_cast hfive)
    have hpos : legendreSym q 5=1 := by
      rcases hchar with h | h
      · exact h
      · have hbad := (legendreSym_five_eq_neg_one_iff (by omega)).mp h
        rcases hbad with heq | heq
        · exact False.elim (hqmodne.1 heq)
        · exact False.elim (hqmodne.2 heq)
    have hfiveZ : (5 : ZMod q) ≠ 0 := by exact_mod_cast hfive
    have hsquare : IsSquare (5 : ZMod q) := by
      simpa using (legendreSym.eq_one_iff (p:=q) (a:=(5:ℤ)) (by exact_mod_cast hfiveZ)).mp hpos
    obtain ⟨s, hs⟩ := hsquare
    have hsPrime : s^2=5 := by simpa [pow_two] using hs.symm
    have htwo : (2 : ZMod q) ≠ 0 := by
      intro hz
      have hd2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hd2
      omega
    obtain ⟨a,b,ha,hb,hsum,_⟩ := fibRootsFromDiscriminant htwo hsPrime
    have hab : a*b=-1 := by linear_combination a*hsum-ha
    have ha0 : a≠0 := by intro hz; rw [hz] at ha; norm_num at ha
    have hb0 : b≠0 := by intro hz; rw [hz] at hb; norm_num at hb
    have hna : ¬ IsSquare a := (fourBoundaryFibDvdIffNonsquare hp hq hp5 hqp a b ha hb hsum hab ha0 hb0).mp hd
    exact ⟨hq,hpmod,a,ha,hna⟩
  · rintro ⟨hq,hpmod,a,ha,hna⟩
    exact fourBoundaryFibDvdOfNonsquare hp hq hp5 hqp a ha hna

end MathGacha
