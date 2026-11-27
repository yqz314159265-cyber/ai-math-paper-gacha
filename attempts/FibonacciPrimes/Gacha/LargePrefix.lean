import Gacha.Certificates

namespace MathGacha

theorem factors_131_prime (r : ℕ) (hr : r ∈
    [2, 2, 2, 11, 131, 89, 199, 19801, 2081, 521, 24571, 9901]) : Nat.Prime r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem fib_131_value : Nat.fib 131 = 1066340417491710595814572169 := by
  norm_num [Nat.fib]

theorem fib_131_prime : Nat.Prime (Nat.fib 131) := by
  rw [fib_131_value]
  apply lucasList 1066340417491710595814572169 3
    [2, 2, 2, 11, 131, 89, 199, 19801, 2081, 521, 24571, 9901] (by decide)
  · exact factors_131_prime
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

theorem factors_137_prime (r : ℕ) (hr : r ∈
    [2, 2, 3, 67, 3571, 461, 139, 1597, 691, 1485571, 63443]) : Nat.Prime r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem fib_137_value : Nat.fib 137 = 19134702400093278081449423917 := by
  norm_num [Nat.fib]

theorem fib_137_prime : Nat.Prime (Nat.fib 137) := by
  rw [fib_137_value]
  apply lucasList 19134702400093278081449423917 2
    [2, 2, 3, 67, 3571, 461, 139, 1597, 691, 1485571, 63443] (by decide)
  · exact factors_137_prime
  · simp only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

def prefixDivisorProduct : ℕ :=
  389 * 743519377 * 519121 * 1247833 * 827728777 * 677 * 27941

theorem sieve_gcd_bounds : ∀ i : Fin 138, 93 < i.val → i.val.Prime →
    i.val ≠ 131 → i.val ≠ 137 →
    1 < Nat.gcd (Nat.fastFib i.val) prefixDivisorProduct ∧
      Nat.gcd (Nat.fastFib i.val) prefixDivisorProduct < Nat.fastFib i.val := by
  decide +kernel

theorem fib_prime_index_excluded_by_sieve {n : ℕ} (hn : 93 < n) (hbound : n ≤ 137)
    (hpidx : n.Prime) (h131 : n ≠ 131) (h137 : n ≠ 137) : ¬ (Nat.fib n).Prime := by
  let i : Fin 138 := ⟨n, by omega⟩
  have hs := sieve_gcd_bounds i (by simpa using hn) hpidx h131 h137
  change 1 < Nat.gcd (Nat.fastFib n) prefixDivisorProduct ∧
    Nat.gcd (Nat.fastFib n) prefixDivisorProduct < Nat.fastFib n at hs
  have hd : Nat.gcd (Nat.fastFib n) prefixDivisorProduct ∣ Nat.fib n := by
    rw [← Nat.fastFib_eq]
    exact Nat.gcd_dvd_left _ _
  intro hprime
  have heq := (Nat.dvd_prime_two_le hprime hs.1).mp hd
  rw [Nat.fastFib_eq] at hs
  rw [Nat.fastFib_eq] at heq
  exact (Nat.ne_of_lt hs.2) heq

theorem old_index_le_93 {n : ℕ}
    (hn : n ∈ [3, 4, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83]) : n ≤ 93 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  omega

theorem fib_prime_indices_through_137 (n : ℕ) (h : n ≤ 137) :
    (Nat.fib n).Prime ↔
      n ∈ [3, 4, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83] ∨ n = 131 ∨ n = 137 := by
  by_cases h93 : n ≤ 93
  · rw [fib_prime_indices_through_93 n h93]
    constructor
    · intro hn
      exact Or.inl hn
    · rintro (hn | rfl | rfl)
      · exact hn
      · omega
      · omega
  · have hnlo : 93 < n := by omega
    have hindex := @fib_prime_index_prime_or_four n
    constructor
    · intro hp
      have hnpOr := hindex hp
      rcases hnpOr with hnp | heq
      · by_cases h131 : n = 131
        · exact Or.inr (Or.inl h131)
        · by_cases h137 : n = 137
          · exact Or.inr (Or.inr h137)
          · exact (fib_prime_index_excluded_by_sieve hnlo (by omega) hnp h131 h137 hp).elim
      · omega
    · rintro (hn | rfl | rfl)
      · have hsmall := old_index_le_93 hn
        omega
      · exact fib_131_prime
      · exact fib_137_prime

end MathGacha
