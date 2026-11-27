import Gacha.DicksonTests
import Mathlib.Data.Nat.Factorization.Basic

namespace MathGacha
open Polynomial

/-- An order divides p when its divisibility survives deletion of each primary
component of k from p*k. -/
theorem dvdIffDeletePrimeComponents {n p k : ℕ} (hn : n≠0) (hp : p≠0) (hk : k≠0)
    (hd : n ∣ p*k) : n ∣ p ↔ ∀ r ∈ k.primeFactors, n ∣ p*(ordCompl[r] k) := by
  constructor
  · intro h r _
    exact h.trans (dvd_mul_right _ _)
  · intro h
    apply (Nat.factorization_le_iff_dvd hn hp).mp
    intro r
    by_cases hr : r ∈ k.primeFactors
    · have hc := (Nat.ordCompl_pos r hk).ne'
      have hb := (Nat.factorization_le_iff_dvd hn (mul_ne_zero hp hc)).mpr (h r hr) r
      simpa [Nat.factorization_mul hp hc,Nat.factorization_ordCompl] using hb
    · have hv : k.factorization r=0 := by simpa [← Nat.support_factorization] using hr
      have hb := (Nat.factorization_le_iff_dvd hn (mul_ne_zero hp hk)).mpr hd r
      simpa [Nat.factorization_mul hp hk,hv] using hb

/-- A composite multiplier can be tested one maximal prime-power divisor at
a time; each test still uses the same fixed target in the prime field. -/
theorem fibDivisorIffPrimePowerTests {p q k : ℕ} (hp : 0<p) (hq : q.Prime) (hq5 : 5<q)
    (he : k*p=neighborIndex q) :
    q ∣ Nat.fib p ↔ ∀ r ∈ k.primeFactors, hasDicksonRoot q (r^k.factorization r) := by
  have : Fact q.Prime := ⟨hq⟩
  have hb : neighborIndex q=q-1 ∨ neighborIndex q=q+1 := by unfold neighborIndex; split <;> simp
  have hpos : 0<neighborIndex q := by rcases hb with h|h <;> omega
  have hk : k≠0 := by rintro rfl; simp at he; omega
  have hbase : q ∣ Nat.fib (neighborIndex q) := primeDvdNeighborFib hq hq5
  obtain ⟨u,_,_,_,hu⟩ := fibRatioData (q:=q) (by omega) (by omega)
  have horder (i : ℕ) : q ∣ Nat.fib i ↔ orderOf u ∣ i := (hu i).trans orderOf_dvd_iff_pow_eq_one.symm
  have ho := (horder _).mp hbase
  rw [← he,Nat.mul_comm k p] at ho
  have hn := (Nat.pos_of_dvd_of_pos ho (Nat.mul_pos hp (Nat.pos_of_ne_zero hk))).ne'
  rw [horder,dvdIffDeletePrimeComponents hn hp.ne' hk ho]
  refine forall_congr' (fun r => imp_congr_right (fun hr => ?_))
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hshape : (r^k.factorization r)*(p*(ordCompl[r] k))=neighborIndex q := by
    calc
      _ = ((r^k.factorization r)*(ordCompl[r] k))*p := by ring
      _ = _ := (congrArg (·*p) (Nat.ordProj_mul_ordCompl_eq_self k r)).trans he
  rw [← horder]
  exact fibDivisorIffDicksonRootOfBranch (by omega) (by omega)
    (pow_pos hrp.pos _) hb hshape hbase

/-- The original statement is equivalent to finding a failed prime-power
test for every potential small factor at arbitrarily large prime indices. -/
theorem originalIffPrimePowerObstructions :
    Original ↔ ∀ B : ℕ, ∃ p > max B 5, p.Prime ∧ ∀ q : ℕ, q.Prime → 5 < q →
      q ≤ 2^(p/2) → p ∣ neighborIndex q →
      ∃ r ∈ (neighborIndex q/p).primeFactors,
        IsCoprime (dickson 1 (1 : ZMod q) (r^(neighborIndex q/p).factorization r)+3)
          (X^q-X) := by
  rw [originalIffAvoidsDicksonRoots]
  apply forall_congr'
  intro B
  apply exists_congr
  intro p
  apply and_congr_right
  intro hlarge
  apply and_congr_right
  intro hp
  apply forall_congr'
  intro q
  repeat' apply imp_congr_right; intro
  rename_i hq hq5 hcut hd
  have : Fact q.Prime := ⟨hq⟩
  have hdec := fibDivisorIffPrimePowerTests hp.pos hq hq5 (Nat.div_mul_cancel hd)
  have hmain := primeDivisorIffDickson hp hq hq5
  rw [and_iff_right hd] at hmain
  rw [← hmain,hdec]
  push Not
  apply exists_congr
  intro r
  exact and_congr_right (fun _ => avoidsDicksonIffCoprime)

end MathGacha
