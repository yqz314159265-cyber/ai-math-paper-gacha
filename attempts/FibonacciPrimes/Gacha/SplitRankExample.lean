import Gacha.SplitRankCubic
import Gacha.ResidueCertificate
import Gacha.CertifiedPrefix

namespace MathGacha

def split359Order : ℕ := 21831311678171160001969
def split359Modulus : ℕ := 475420437734698220747368027166749382927701417016557193662268716376935476241
def split359Witness : ℕ :=
  53846701002818712355219886408203076977142641597181549015094981413804302104
def split359Factors : List ℕ := [1066737847220321,541,181,19,11]

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

local instance splitFactPrime359 : Fact (Nat.Prime 359) := ⟨by norm_num⟩

theorem split359Certificate : largeOrderCertificate split359Modulus split359Order := by
  apply largeOrderOfResidueTests (w:=split359Witness) (f:=96) (by decide +kernel)
    split359Factors (by decide +kernel)
  · change Nat.Prime 1066737847220321 ∧ Nat.Prime 541 ∧ Nat.Prime 181 ∧ Nat.Prime 19 ∧ Nat.Prime 11
    refine ⟨lucasCertificateTargets_sound _ lucasNodeBatch01_sound _ (by decide +kernel), ?_⟩
    norm_num
  · decide +kernel
  · decide +kernel

/-- The cube of the certified order alone is over forty-five million times too small. -/
theorem splitRankCubicExample359 : (Nat.fib 359).Prime ∧
    Nat.fib 359/split359Order^3=45691809 := by
  have he : Nat.fib 359=split359Modulus := by rw [← Nat.fastFib_eq]; decide +kernel
  refine ⟨?_,he ▸ (by decide +kernel)⟩
  apply fibPrimeSplitRankCubic (d:=split359Order) (by decide) (by decide +kernel) (by decide +kernel)
  · rw [he]; decide +kernel
  · rw [he]; exact split359Certificate
  · rw [he]; decide +kernel
  · rw [he]; decide +kernel
  · rw [he]; decide +kernel
  · rw [he]; exact (classNonsquareTest_iff ..).mp (by decide +kernel)
  · rw [he]; exact (classNonsquareTest_iff ..).mp (by decide +kernel)

end MathGacha
