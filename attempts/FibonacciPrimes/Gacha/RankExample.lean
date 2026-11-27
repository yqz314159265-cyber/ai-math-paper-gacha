import Gacha.RankCubic
import Gacha.ResidueCertificate

namespace MathGacha

def rank433Order : ℕ := 20354267268086208338686180768
def rank433Cofactor : ℕ := 68156574222640700861996309910567001399825804743671019267047589
def rank433Modulus : ℕ := 1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353
def rank433Witness : ℕ := 516859110310328804224754560038126725996899503791648457957326724712375241759415338571008566
def rank433Factors : List ℕ := [109,5779,11128427,103681,125024551,7,2,2,2,2,2]

set_option maxRecDepth 14000
set_option maxHeartbeats 4000000

local instance : Fact (Nat.Prime 433) := ⟨by norm_num⟩

theorem rank433Certificate : largeOrderCertificate rank433Modulus rank433Order := by
  apply largeOrderOfResidueTests (w:=rank433Witness) (f:=112) (by decide +kernel) rank433Factors (by decide +kernel)
  · change Nat.Prime 109 ∧ Nat.Prime 5779 ∧ Nat.Prime 11128427 ∧ Nat.Prime 103681 ∧
      Nat.Prime 125024551 ∧ Nat.Prime 7 ∧ Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 2
    norm_num
  · decide +kernel
  · decide +kernel

/-- Here the Fibonacci value exceeds 164511 times the cube of the certified order. -/
theorem rankCubicExample433 : (Nat.fib 433).Prime ∧
    164511*rank433Order^3 ≤ Nat.fib 433 ∧ Nat.fib 433 < 164512*rank433Order^3 := by
  have he : Nat.fib 433=rank433Modulus := by rw [← Nat.fastFib_eq]; decide +kernel
  refine ⟨?_,he ▸ (by decide +kernel),he ▸ (by decide +kernel)⟩
  apply fibPrimeOfRankCubic (d:=rank433Order) (c:=rank433Cofactor) (by decide) (by decide +kernel) (by decide +kernel)
  · rw [he]; decide +kernel
  · rw [he]; exact rank433Certificate
  · rw [he]; decide +kernel
  · rw [he]; decide +kernel
  · let a := (rank433Cofactor%(rank433Order*433))^2
    let b := 4*433*(rank433Cofactor/(rank433Order*433))
    have h : (Nat.sqrt (a-b))^2≠a-b := by decide +kernel
    rintro ⟨u,hu⟩
    change a=u^2+b at hu
    have heq : a-b=u^2 := by omega
    rw [heq,Nat.sqrt_eq'] at h
    exact h rfl

end MathGacha
