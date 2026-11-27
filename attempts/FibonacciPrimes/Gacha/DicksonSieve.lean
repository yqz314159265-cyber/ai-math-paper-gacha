import Gacha.DicksonFactors
import Gacha.SharpRank
import Gacha.FactorRank
import Gacha.Reduction
import Mathlib.Data.Nat.Sqrt

namespace MathGacha

/-- A prime-index primality cutoff expressed solely in terms of the index. -/
theorem oddIndexDyadicCutoff {p : ℕ} (hp : Odd p) (h : 5 < p) :
    (Nat.fib p).sqrt ≤ 2^(p/2) ∧ 2^(p/2) < Nat.fib p := by
  obtain ⟨m, hm⟩ := hp
  have he : p=2*m+1 := by omega
  have hu (n : ℕ) : Nat.fib (n+1) ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih =>
      have hmono := Nat.fib_le_fib_succ (n:=n)
      rw [Nat.fib_add_two, pow_succ]
      omega
  have hlow (j : ℕ) : 2^(j+3) < Nat.fib (2*(j+3)+1) := by
    induction j with
    | zero => decide
    | succ j ih =>
      let t := 2*(j+3)+1
      have hadd : 2*(j+1+3)+1 = t+2 := by dsimp [t]; omega
      have hm := Nat.fib_le_fib_succ (n:=t)
      rw [hadd, Nat.fib_add_two, show j+1+3=(j+3)+1 by omega, pow_succ]
      change 2^(j+3) < Nat.fib t at ih
      omega
  have hex : p/2=m := by omega
  rw [hex,he]
  constructor
  · have heq : (2:ℕ)^(2*m)=(2^m)^2 := by rw [← pow_mul, Nat.mul_comm]
    simpa [heq] using Nat.sqrt_le_sqrt (hu (2*m))
  · simpa [show m-3+3=m by omega] using hlow (m-3)

/-- The neighbor q−(5/q), evaluated using residues modulo five. -/
def neighborIndex (q : ℕ) : ℕ := if q%5=2 ∨ q%5=3 then q+1 else q-1

/-- The fixed target −3 occurs in the image of the multiplier's Dickson polynomial. -/
def hasDicksonRoot (q k : ℕ) : Prop :=
  ∃ x : ZMod q, (Polynomial.dickson 1 1 k).eval x = -3

/-- The neighbor and its Dickson value determine divisibility at a prime index. -/
theorem primeDivisorIffDickson {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq5 : 5 < q) :
    q ∣ Nat.fib p ↔ p ∣ neighborIndex q ∧ hasDicksonRoot q (neighborIndex q / p) := by
  have : Fact q.Prime := ⟨hq⟩
  have hqt : q ∣ Nat.fib (neighborIndex q) := primeDvdNeighborFib hq hq5
  have ht : neighborIndex q = q-1 ∨ neighborIndex q=q+1 := by unfold neighborIndex; split <;> simp
  have iffRoot (hd : p ∣ neighborIndex q) :
      q ∣ Nat.fib p ↔ hasDicksonRoot q (neighborIndex q / p) := by
    have hs := Nat.div_mul_cancel hd
    have hk : 0 < neighborIndex q / p := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, zero_mul] at hs
      rcases ht with ht | ht <;> omega
    exact fibDivisorIffDicksonRootOfBranch (by omega) (by omega) hk ht hs hqt
  constructor
  · intro h
    have hd := indexDividesFromCommonFactor hp hq.one_lt h hqt
    exact ⟨hd,(iffRoot hd).mp h⟩
  · rintro ⟨hd,hr⟩
    exact (iffRoot hd).mpr hr

/-- Exact reformulation with solely prime indices, a dyadic cutoff, and finite-field polynomial tests. -/
theorem originalIffAvoidsDicksonRoots :
    Original ↔ ∀ B : ℕ, ∃ p > max B 5, p.Prime ∧ ∀ q : ℕ, q.Prime → 5 < q →
      q ≤ 2^(p/2) → p ∣ neighborIndex q → ¬ hasDicksonRoot q (neighborIndex q / p) := by
  rw [originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p,hpB,hp,hf⟩ := h (max B 5)
    refine ⟨p,hpB,hp,?_⟩
    intro q hq hq5 hcut hd hr
    have hdiv := (primeDivisorIffDickson hp hq hq5).mpr ⟨hd,hr⟩
    have he := (Nat.dvd_prime_two_le hf hq.two_le).mp hdiv
    have hg := (oddIndexDyadicCutoff (hp.odd_of_ne_two (by omega)) (by omega)).2
    omega
  · intro h B
    obtain ⟨p,hpB,hp,hs⟩ := h B
    refine ⟨p,by omega,hp,?_⟩
    by_contra hn
    have hg := Nat.le_fib_self (by omega : 5 ≤ p)
    let q := (Nat.fib p).minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hdiv : q ∣ Nat.fib p := Nat.minFac_dvd _
    have hsize := fibLeastFactorLinearBound hp (by omega) hq hdiv
    have hq5 : 5 < q := by omega
    have hcut := (oddIndexDyadicCutoff (hp.odd_of_ne_two (by omega)) (by omega)).1
    have hsmall : q ≤ (Nat.fib p).sqrt := Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hn)
    obtain ⟨hd,hr⟩ := (primeDivisorIffDickson hp hq hq5).mp hdiv
    exact hs q hq hq5 (hsmall.trans hcut) hd hr


end MathGacha
