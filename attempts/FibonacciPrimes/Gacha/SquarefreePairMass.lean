import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

open Finset

namespace MathGacha

noncomputable def squarefreePairMass (A : Finset ℕ) : ℝ :=
  ∑ a∈A, ∑ b∈A, if Squarefree (a*b) then (a:ℝ)⁻¹*(b:ℝ)⁻¹ else 0

noncomputable def divisorReciprocal (d a : ℕ) : ℝ := if d∣a then (a:ℝ)⁻¹ else 0

noncomputable def squareObstructionMass (r a b : ℕ) : ℝ :=
  divisorReciprocal (r^2) a*(b:ℝ)⁻¹ + (a:ℝ)⁻¹*divisorReciprocal (r^2) b +
    divisorReciprocal r a*divisorReciprocal r b

theorem divisorReciprocal_nonneg (d a : ℕ) : 0≤divisorReciprocal d a := by
  unfold divisorReciprocal
  split <;> positivity

theorem squareObstructionMass_nonneg (r a b : ℕ) : 0≤squareObstructionMass r a b := by
  unfold squareObstructionMass
  exact add_nonneg (add_nonneg (mul_nonneg (divisorReciprocal_nonneg ..) (by positivity))
    (mul_nonneg (by positivity) (divisorReciprocal_nonneg ..)))
    (mul_nonneg (divisorReciprocal_nonneg ..) (divisorReciprocal_nonneg ..))

theorem oddSquareReciprocalSum_le (N : ℕ) :
    4*(∑ i∈range N, 1/(2*(i:ℝ)+3)^2)+1/((N:ℝ)+1)≤1 := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ,Nat.cast_succ]
    have he : 4/(2*(n:ℝ)+3)^2≤1/((n:ℝ)+1)-1/((n:ℝ)+1+1) := by
      have h1 : (0:ℝ)<n+1 := by positivity
      have h2 : (0:ℝ)<n+1+1 := by positivity
      have h3 : (0:ℝ)<(2*(n:ℝ)+3)^2 := by positivity
      rw [div_sub_div _ _ h1.ne' h2.ne',div_le_div_iff₀ h3 (mul_pos h1 h2)]
      nlinarith
    rw [mul_add,show 4*(1/(2*(n:ℝ)+3)^2)=4/(2*(n:ℝ)+3)^2 by ring]
    linarith

theorem nonSquarefreePair_hasOddWitness {U a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hau : a≤U) (hbu : b≤U) (hao : ¬2∣a) (hbo : ¬2∣b)
    (hs : ¬Squarefree (a*b)) : ∃ i<U,
    (2*i+3)^2∣a ∨ (2*i+3)^2∣b ∨ ((2*i+3)∣a ∧ (2*i+3)∣b) := by
  have hex : ∃ r, r.Prime ∧ (r^2∣a ∨ r^2∣b ∨ (r∣a ∧ r∣b)) := by
    by_contra! h
    apply hs
    rw [Nat.squarefree_mul_iff,Nat.squarefree_iff_prime_squarefree,Nat.squarefree_iff_prime_squarefree]
    refine ⟨?_,?_,?_⟩
    · by_contra hc
      obtain ⟨r,hr,hr1,hr2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      exact (h r hr).2.2 hr1 hr2
    · intro r hr hsq
      exact (h r hr).1 (by simpa [pow_two] using hsq)
    · intro r hr hsq
      exact (h r hr).2.1 (by simpa [pow_two] using hsq)
  obtain ⟨r,hr,hdiv⟩ := hex
  have hrone := hr.two_le
  have hrq : r∣r^2 := by simp [pow_two]
  have hrab : r∣a ∨ r∣b := hdiv.elim (fun h => Or.inl (hrq.trans h))
    (fun h => h.elim (fun h => Or.inr (hrq.trans h)) (fun h => Or.inl h.1))
  have hru := hrab.elim (fun h => (Nat.le_of_dvd ha h).trans hau) (fun h => (Nat.le_of_dvd hb h).trans hbu)
  have hodd := hr.eq_two_or_odd.resolve_left (by rintro rfl; exact hrab.elim hao hbo)
  refine ⟨r/2-1,by omega,?_⟩
  rwa [show 2*(r/2-1)+3=r by omega]

theorem squareObstructionCovers {U a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hau : a≤U) (hbu : b≤U) (hao : ¬2∣a) (hbo : ¬2∣b) :
    (if Squarefree (a*b) then (a:ℝ)⁻¹*(b:ℝ)⁻¹ else 0) +
      (∑ i∈range U, squareObstructionMass (2*i+3) a b) ≥ (a:ℝ)⁻¹*(b:ℝ)⁻¹ := by
  by_cases hs : Squarefree (a*b)
  · rw [if_pos hs]
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ => squareObstructionMass_nonneg ..)
  rw [if_neg hs,zero_add]
  obtain ⟨i,hi,hr⟩ := nonSquarefreePair_hasOddWitness ha hb hau hbu hao hbo hs
  apply le_trans _ (single_le_sum (f:=fun i => squareObstructionMass (2*i+3) a b)
    (fun _ _ => squareObstructionMass_nonneg ..) (mem_range.mpr hi))
  let r := 2*i+3
  change r^2∣a ∨ r^2∣b ∨ r∣a ∧ r∣b at hr
  change _ ≤ squareObstructionMass r a b
  have h1 := mul_nonneg (divisorReciprocal_nonneg (r^2) a) (show 0≤(b:ℝ)⁻¹ by positivity)
  have h2 := mul_nonneg (show 0≤(a:ℝ)⁻¹ by positivity) (divisorReciprocal_nonneg (r^2) b)
  have h3 := mul_nonneg (divisorReciprocal_nonneg r a) (divisorReciprocal_nonneg r b)
  unfold squareObstructionMass
  rcases hr with h|h|⟨h,h'⟩
  · rw [show divisorReciprocal (r^2) a=(a:ℝ)⁻¹ by simp [divisorReciprocal,h]]
    linarith
  · rw [show divisorReciprocal (r^2) b=(b:ℝ)⁻¹ by simp [divisorReciprocal,h]]
    linarith
  · rw [show divisorReciprocal r a=(a:ℝ)⁻¹ by simp [divisorReciprocal,h],
      show divisorReciprocal r b=(b:ℝ)⁻¹ by simp [divisorReciprocal,h']]
    linarith


theorem squareObstructionMass_sum (A : Finset ℕ) (r : ℕ) :
    ∑ a∈A, ∑ b∈A, squareObstructionMass r a b =
      2*(∑ a∈A, divisorReciprocal (r^2) a)*(∑ a∈A, (a:ℝ)⁻¹) +
      (∑ a∈A, divisorReciprocal r a)^2 := by
  simp only [squareObstructionMass,Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  ring

theorem squareObstructionMass_sum_bound (A : Finset ℕ) {r : ℕ} (hr : 0<r)
    (hdiv : ∀ d : ℕ, 0<d → ∑ a∈A, divisorReciprocal d a ≤ (∑ a∈A, (a:ℝ)⁻¹)/(d:ℝ)) :
    ∑ a∈A, ∑ b∈A, squareObstructionMass r a b ≤
      3*(∑ a∈A, (a:ℝ)⁻¹)^2 / (r:ℝ)^2 := by
  rw [squareObstructionMass_sum]
  let H := ∑ a∈A, (a:ℝ)⁻¹
  have hH : 0≤H := sum_nonneg (fun a ha => by positivity)
  have h1 := hdiv r hr
  have h2 := hdiv (r^2) (pow_pos hr _)
  rw [Nat.cast_pow] at h2
  have h1' : (∑ a∈A, divisorReciprocal r a)^2 ≤ (H/(r:ℝ))^2 :=
    pow_le_pow_left₀ (sum_nonneg fun _ _ => divisorReciprocal_nonneg ..) h1 2
  have h2' := mul_le_mul_of_nonneg_right h2 hH
  change 2*(∑ a∈A, divisorReciprocal (r^2) a)*H + _ ≤ 3*H^2/(r:ℝ)^2
  calc
    _ ≤ 2*(H/(r:ℝ)^2*H)+(H/(r:ℝ))^2 := by dsimp only [H] at *; linarith
    _ = _ := by ring

/-- Restricting a pair of odd, harmonically weighted integers to squarefree
product retains at least one fourth of the original weight. -/
theorem squarefreePairMass_quarter {U : ℕ} (A : Finset ℕ)
    (hA : ∀ a∈A, 0<a ∧ a≤U ∧ ¬2∣a)
    (hdiv : ∀ d : ℕ, 0<d → ∑ a∈A, divisorReciprocal d a ≤ (∑ a∈A, (a:ℝ)⁻¹)/(d:ℝ)) :
    (∑ a∈A, (a:ℝ)⁻¹)^2/4 ≤ squarefreePairMass A := by
  let H := ∑ a∈A, (a:ℝ)⁻¹
  let obs := fun i a b : ℕ => squareObstructionMass (2*i+3) a b
  have hcover : H^2 ≤ squarefreePairMass A + ∑ a∈A, ∑ b∈A, ∑ i∈range U, obs i a b := by
    rw [squarefreePairMass,← Finset.sum_add_distrib]
    calc
      _ = ∑ a∈A, ∑ b∈A, (a:ℝ)⁻¹*(b:ℝ)⁻¹ := by dsimp only [H]; simp_rw [← Finset.mul_sum,← Finset.sum_mul]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro a ha
        rw [← Finset.sum_add_distrib]
        apply sum_le_sum
        intro b hb
        exact squareObstructionCovers (hA a ha).1 (hA b hb).1 (hA a ha).2.1
          (hA b hb).2.1 (hA a ha).2.2 (hA b hb).2.2
  have hswap : (∑ a∈A, ∑ b∈A, ∑ i∈range U, obs i a b) =
      ∑ i∈range U, ∑ a∈A, ∑ b∈A, obs i a b := by
    calc
      _ = ∑ a∈A, ∑ i∈range U, ∑ b∈A, obs i a b := by
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
      _ = _ := sum_comm
  have htotal : (∑ i∈range U, ∑ a∈A, ∑ b∈A, obs i a b) ≤ 3*H^2/4 := by
    calc
      _ ≤ ∑ i∈range U, 3*H^2/(2*(i:ℝ)+3)^2 := by
        apply sum_le_sum
        intro i _
        simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
          (squareObstructionMass_sum_bound A (r:=2*i+3) (by omega) hdiv)
      _ = (3*H^2)*(∑ i∈range U, 1/(2*(i:ℝ)+3)^2) := by rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ _ := by
        have ht := oddSquareReciprocalSum_le U
        have hh : 0≤1/((U:ℝ)+1) := by positivity
        have hb : (∑ i∈range U, 1/(2*(i:ℝ)+3)^2)≤1/4 := by linarith
        calc
          _ ≤ (3*H^2)*(1/4) := mul_le_mul_of_nonneg_left hb (by positivity)
          _ = _ := by ring
  rw [hswap] at hcover
  change H^2/4≤squarefreePairMass A
  linarith

end MathGacha
