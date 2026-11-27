import Gacha.FermatTest

namespace MathGacha

set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

/-- Prospective prime indices beyond the initial segment classified through 137. -/
def furtherPrimeCandidates : List ℕ := [359,431,433,449,509,569,571]

def passesRangeScreen (n : ℕ) : Bool :=
  if n.Prime ∧ n ∉ furtherPrimeCandidates then
    let f := Nat.fastFib n
    fermatReject f n f 2 1
  else true

/-- At every other prime index from 138 to 1000 the base-two Frobenius test fails. -/
theorem fermatScreenTo1000 : ∀ j : Fin 863, passesRangeScreen (j.val+138)=true := by
  have blocks (k : Fin 27) :
      (List.range 32).all (fun i => passesRangeScreen (138+32*k.val+i))=true := by
    rcases k with ⟨k,hk⟩
    change (List.range 32).all (fun i => passesRangeScreen (138+32*k+i))=true
    interval_cases k <;> decide +kernel
  intro j
  have h := List.all_eq_true.mp (blocks ⟨j.val/32,by omega⟩) (j.val%32)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  change passesRangeScreen (138+32*(j.val/32)+j.val%32)=true at h
  rwa [show 138+32*(j.val/32)+j.val%32=j.val+138 by omega] at h

theorem fibPrimeCandidatesThrough1000 {n : ℕ} (hn : 137<n) (hu : n≤1000)
    (hf : (Nat.fib n).Prime) : n ∈ furtherPrimeCandidates := by
  by_contra hx
  have hpi := (fib_prime_index_prime_or_four hf).resolve_right (by omega)
  have h := fermatScreenTo1000 ⟨n-138,by omega⟩
  change passesRangeScreen (n-138+138) = true at h
  rw [Nat.sub_add_cancel (by omega), passesRangeScreen,if_pos ⟨hpi,hx⟩] at h
  exact nonprimeOfFermatReject n h (by rwa [Nat.fastFib_eq])

theorem noFibPrimeFrom138Through358 {n : ℕ} (hn : 138≤n) (hu : n≤358) :
    ¬ (Nat.fib n).Prime := by
  intro hp
  have hv := fibPrimeCandidatesThrough1000 (by omega) (by omega) hp
  simp [furtherPrimeCandidates] at hv
  omega

end MathGacha
