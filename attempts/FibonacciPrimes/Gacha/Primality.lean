import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

namespace MathGacha

/-- Recover every prime divisor from an explicit prime factorization. -/
theorem primeMemProduct {q : ℕ} (hq : q.Prime) (f : List ℕ)
    (hf : ∀ r ∈ f, Nat.Prime r) (hd : q ∣ f.prod) : q ∈ f := by
  induction f with
  | nil => exact (hq.not_dvd_one hd).elim
  | cons r rest ih =>
    rcases hq.dvd_mul.mp hd with hr | ht
    · exact List.mem_cons.mpr (Or.inl ((Nat.dvd_prime_two_le (hf r (by simp)) hq.two_le).mp hr))
    · exact List.mem_cons_of_mem r (ih (fun t ht => hf t (List.mem_cons_of_mem r ht)) ht)

/-- Lucas's criterion with an explicit factor list for p-1. -/
theorem lucasList (p : ℕ) (a : ZMod p) (f : List ℕ) (hprod : p - 1 = f.prod)
    (hf : ∀ r ∈ f, Nat.Prime r) (ha : a ^ (p - 1) = 1)
    (hd : ∀ q ∈ f, a ^ ((p - 1) / q) ≠ 1) : p.Prime :=
  lucas_primality p a ha fun q hq h => hd q (primeMemProduct hq f hf (hprod ▸ h))

theorem auxiliaryLucasPrime : Nat.Prime 370248451 := by
  apply lucasList 370248451 3 [2, 3, 5, 5, 11, 13, 41, 421] (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

theorem primeValue43 : Nat.Prime 433494437 := by
  apply lucasList 433494437 2 [2, 2, 29, 89, 199, 211] (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

theorem primeValue47 : Nat.Prime 2971215073 := by
  apply lucasList 2971215073 5 [2, 2, 2, 2, 2, 3, 3, 7, 23, 139, 461] (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

theorem primeValue83 : Nat.Prime 99194853094755497 := by
  apply lucasList 99194853094755497 3 [2, 2, 2, 13, 29, 211, 421, 370248451] (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact auxiliaryLucasPrime | norm_num
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

end MathGacha
