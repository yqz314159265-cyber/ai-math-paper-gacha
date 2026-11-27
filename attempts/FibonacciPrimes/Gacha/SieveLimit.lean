import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Gacha.Reduction

namespace MathGacha

def candidateA : Finset ℕ := {0}

def candidateT (n : ℕ) : Finset ℕ := {0} ∪ Finset.Icc (n + 1) (2 * n + 1)

def candidateL (n : ℕ) : Set ℕ := {0} ∪ {x | n < x}

theorem candidateA_subset_T (n : ℕ) : candidateA ⊆ candidateT n := by
  intro x hx
  simp only [candidateA, Finset.mem_singleton] at hx
  subst x
  simp [candidateT]

theorem candidateT_subset_L (n : ℕ) : ↑(candidateT n) ⊆ candidateL n := by
  intro x hx
  have hx' : x ∈ ({0} : Finset ℕ) ∪ Finset.Icc (n + 1) (2 * n + 1) := by
    simpa [candidateT] using hx
  rcases Finset.mem_union.mp hx' with hx0 | hxI
  · have : x = 0 := Finset.mem_singleton.mp hx0
    subst x
    simp [candidateL]
  · rcases Finset.mem_Icc.mp hxI with ⟨hlo, hhi⟩
    simp only [candidateL, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact Or.inr (by omega)

theorem candidateT_eventually_eq_A_pointwise (x : ℕ) :
    ∃ N, ∀ n ≥ N, (x ∈ candidateT n ↔ x ∈ candidateA) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, fun n hn => by simp [candidateT, candidateA]⟩
  · refine ⟨x, fun n hn => ?_⟩
    have hxT : x ∉ Finset.Icc (n + 1) (2 * n + 1) := by
      simp only [Finset.mem_Icc]
      omega
    simp [candidateT, candidateA, hx, hxT]

theorem candidateT_card (n : ℕ) : (candidateT n).card = n + 2 := by
  rw [candidateT, Finset.card_union_of_disjoint]
  · simp
    omega
  · apply Finset.disjoint_left.mpr
    intro x hx0 hxI
    have : x = 0 := Finset.mem_singleton.mp hx0
    subst x
    simp only [Finset.mem_Icc] at hxI
    omega

/-- The upper bound on the index is chosen before the factor cutoff. -/
def UniformFiniteSieve : Prop :=
  ∀ B : ℕ, ∃ N : ℕ, ∀ K : ℕ, ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧
    ∀ q : ℕ, q.Prime → q < Nat.fib p → q ≤ K → ¬ q ∣ Nat.fib p

/-- A bounded index window surviving every proper-prime-factor cutoff is the exact criterion. -/
theorem originalIffUniformFiniteSieve : Original ↔ UniformFiniteSieve := by
  rw [originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p, hpB, hp, hfp⟩ := h B
    refine ⟨p, fun K => ⟨p, hpB, le_rfl, hp, ?_⟩⟩
    intro q hq hlt _ hd
    exact hlt.ne ((Nat.dvd_prime_two_le hfp hq.two_le).mp hd)
  · intro h B
    obtain ⟨N, hN⟩ := h (max B 5)
    obtain ⟨p, hpB, hpN, hp, hs⟩ := hN (Nat.fib N)
    refine ⟨p, by omega, hp, ?_⟩
    have hg := Nat.le_fib_self (by omega : 5 ≤ p)
    by_contra hn
    have hq := (Nat.not_prime_iff_minFac_lt (by omega : 2 ≤ Nat.fib p)).mp hn
    exact hs _ (Nat.minFac_prime (by omega)) hq (hq.le.trans (Nat.fib_mono hpN)) (Nat.minFac_dvd _)

end MathGacha
