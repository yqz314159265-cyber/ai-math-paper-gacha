import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace MathGacha

/-- The two consecutive Fibonacci residues form the finite-state orbit. -/
def fibState (m n : ℕ) : ZMod m × ZMod m :=
  ((Nat.fib n : ℕ), (Nat.fib (n + 1) : ℕ))

/-- Two of the first `m^2+1` Fibonacci states coincide modulo `m`. -/
theorem fibState_collision (m : ℕ) (hm : 1 < m) :
    ∃ i j : ℕ, i < j ∧ j ≤ m ^ 2 ∧ fibState m i = fibState m j := by
  have : NeZero m := ⟨by omega⟩
  let f : Fin (m ^ 2 + 1) → ZMod m × ZMod m := fun k => fibState m k.val
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    simp [pow_two])
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨i.val, j.val, hlt, by omega, heq⟩
  · exact ⟨j.val, i.val, hgt, by omega, heq.symm⟩

/-- One transition advances the Fibonacci state. -/
theorem fibState_succ (m n : ℕ) :
    fibState m (n + 1) = ((fibState m n).2, (fibState m n).1 + (fibState m n).2) := by
  simp only [fibState, Nat.fib_add_two]
  simp [Nat.cast_add]

/-- The state transition is injective: its predecessor is `(b-a,a)`. -/
theorem fibState_step_injective (m : ℕ) :
    Function.Injective (fun x : ZMod m × ZMod m => (x.2, x.1 + x.2)) := by
  intro a b h
  apply Prod.ext
  · have hsum := congrArg Prod.snd h
    have hsecond := congrArg Prod.fst h
    change a.1 + a.2 = b.1 + b.2 at hsum
    change a.2 = b.2 at hsecond
    calc
      a.1 = (a.1 + a.2) - a.2 := by ring
      _ = (b.1 + b.2) - b.2 := by rw [hsum, hsecond]
      _ = b.1 := by ring
  · exact congrArg Prod.fst h

/-- A repeated Fibonacci state can be pulled back to a return to the initial state. -/
theorem fibState_collision_returns (m : ℕ) :
    ∀ i j : ℕ, i < j → fibState m i = fibState m j →
      fibState m 0 = fibState m (j - i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro j hij hstates
    by_cases hzero : i = 0
    · subst i
      simpa only [Nat.sub_zero] using hstates
    · have hi : 0 < i := Nat.pos_of_ne_zero hzero
      have hj : 0 < j := by omega
      have hprev : fibState m (i - 1) = fibState m (j - 1) := by
        have hi' : i = (i - 1) + 1 := by omega
        have hj' : j = (j - 1) + 1 := by omega
        rw [hi', hj', fibState_succ, fibState_succ] at hstates
        exact fibState_step_injective m hstates
      have hrec := ih (i - 1) (by omega) (j - 1) (by omega) hprev
      have hsub : j - i = (j - 1) - (i - 1) := by omega
      rw [hsub]
      exact hrec

/-- For every modulus above one, a positive Fibonacci index at most `m^2`
produces a term divisible by `m`. -/
theorem exists_fib_dvd (m : ℕ) (hm : 1 < m) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ^ 2 ∧ m ∣ Nat.fib t := by
  obtain ⟨i, j, hij, hjbound, hstates⟩ := fibState_collision m hm
  have hreturn := fibState_collision_returns m i j hij hstates
  refine ⟨j - i, by omega, ?_, ?_⟩
  · omega
  · have hfirst := congrArg Prod.fst hreturn
    have hzero : (Nat.fib (j - i) : ZMod m) = 0 := by
      simpa [fibState] using hfirst.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero

/-- Above the square of a nontrivial modulus, prime indices cannot have that
modulus as a Fibonacci divisor. -/
theorem no_fib_factor_at_prime_above_square {m p : ℕ} (hm : 1 < m)
    (hp : p.Prime) (hbound : m ^ 2 < p) : ¬ m ∣ Nat.fib p := by
  obtain ⟨t, htpos, htbound, hmt⟩ := exists_fib_dvd m hm
  intro hmp
  have htp : t < p := by omega
  have hnot : ¬ p ∣ t := by
    intro hdiv
    have hp_le_t : p ≤ t := Nat.le_of_dvd (by omega) hdiv
    omega
  have hcop : Nat.Coprime t p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hgcd : Nat.gcd t p = 1 := hcop.gcd_eq_one
  have hdg : m ∣ Nat.gcd (Nat.fib t) (Nat.fib p) := Nat.dvd_gcd hmt hmp
  rw [← Nat.fib_gcd, hgcd, Nat.fib_one] at hdg
  have hmle := Nat.le_of_dvd (by norm_num : 0 < 1) hdg
  omega

/-- A fixed finite factor set is eliminated past the largest squared modulus in the set. -/
theorem finite_factors_avoid_square_bound (s : Finset ℕ) :
    ∀ p : ℕ, s.sup (fun r => r ^ 2) < p → p.Prime →
      ∀ r ∈ s, 1 < r → ¬ r ∣ Nat.fib p := by
  intro p hpbound hp r hr hrlarge
  have hrle : r ^ 2 ≤ s.sup (fun x => x ^ 2) := Finset.le_sup (f := fun x : ℕ => x^2) hr
  exact no_fib_factor_at_prime_above_square hrlarge hp (lt_of_le_of_lt hrle hpbound)

end MathGacha
