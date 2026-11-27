import Gacha.Boundary
import Gacha.Index
import Gacha.Primality

namespace MathGacha

/-- Complete finite classification. Large prime values use explicit Lucas certificates. -/
theorem fib_prime_indices_through_93 (n : ℕ) (h : n ≤ 93) :
    (Nat.fib n).Prime ↔ n ∈ [3, 4, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83] := by
  by_cases small : n ≤ 30
  · rw [fib_prime_indices_through_30 n small]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  by_cases prime : n.Prime
  · have possible : ∀ i : Fin 94, 30 < i.val → i.val.Prime →
        i.val ∈ [31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] := by decide
    have hn := possible ⟨n, by omega⟩ (show 30 < n by omega) prime
    change n ∈ [31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hc : ¬ (Nat.fib 31).Prime := Nat.not_prime_of_mul_eq
          (show 557 * 2417 = Nat.fib 31 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 37).Prime := Nat.not_prime_of_mul_eq
          (show 73 * 330929 = Nat.fib 37 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 41).Prime := Nat.not_prime_of_mul_eq
          (show 2789 * 59369 = Nat.fib 41 by decide) (by decide) (by decide)
      simp [hc]
    · have hp : (Nat.fib 43).Prime := primeValue43
      simp [hp]
    · have hp : (Nat.fib 47).Prime := primeValue47
      simp [hp]
    · have hc : ¬ (Nat.fib 53).Prime := Nat.not_prime_of_mul_eq
          (show 953 * 55945741 = Nat.fib 53 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 59).Prime := Nat.not_prime_of_mul_eq
          (show 353 * 2710260697 = Nat.fib 59 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 61).Prime := Nat.not_prime_of_mul_eq
          (show 4513 * 555003497 = Nat.fib 61 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 67).Prime := Nat.not_prime_of_mul_eq
          (show 269 * 167083904137 = Nat.fib 67 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 71).Prime := Nat.not_prime_of_mul_eq
          (show 6673 * 46165371073 = Nat.fib 71 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 73).Prime := Nat.not_prime_of_mul_eq
          (show 9375829 * 86020717 = Nat.fib 73 by decide) (by decide) (by decide)
      simp [hc]
    · have hc : ¬ (Nat.fib 79).Prime := Nat.not_prime_of_mul_eq
          (show 157 * 92180471494753 = Nat.fib 79 by decide) (by decide) (by decide)
      simp [hc]
    · have hp : (Nat.fib 83).Prime := primeValue83
      simp [hp]
    · have hc : ¬ (Nat.fib 89).Prime := Nat.not_prime_of_mul_eq
          (show 1069 * 1665088321800481 = Nat.fib 89 by decide) (by decide) (by decide)
      simp [hc]
  · constructor
    · intro hp
      rcases fib_prime_index_prime_or_four hp with hprime | heq
      · exact (prime hprime).elim
      · omega
    · intro hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have ht : n = 43 ∨ n = 47 ∨ n = 83 := by omega
      rcases ht with rfl | rfl | rfl <;> exact (prime (by decide)).elim

end MathGacha
