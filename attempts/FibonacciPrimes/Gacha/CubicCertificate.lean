import Gacha.CubicOrder
import Gacha.LucasChecker

namespace MathGacha

/-- A prime-power order test reduced to a gcd of ordinary integers. -/
def orderUnitCheck (N w d r : ℕ) : Bool :=
  let z := lucasPowBits (w : ZMod N) (d/r).bits - 1
  decide (z.val.Coprime N)

theorem orderUnitCheck_sound {N w d r : ℕ} (hN : 0<N)
    (h : orderUnitCheck N w d r=true) : IsUnit ((w:ZMod N)^(d/r)-1) := by
  let z := lucasPowBits (w:ZMod N) (d/r).bits-1
  have hcp : z.val.Coprime N := of_decide_eq_true h
  have : NeZero N := ⟨hN.ne'⟩
  simpa [z,ZMod.natCast_zmod_val,lucasPowBits_nat_correct] using
    ((ZMod.isUnit_iff_coprime z.val N).mpr hcp)

/-- A prime divisor of the test modulus sees exact multiplicative order d. -/
theorem largeOrderCertificateOfChecks {N w d : ℕ} (hN : 1<N) (f : List ℕ)
    (hprod : d=f.prod) (hf : ∀ r ∈ f, Nat.Prime r)
    (hw : (lucasPowBits (w:ZMod N) d.bits).val=1)
    (hunit : ∀ r ∈ f,orderUnitCheck N w d r=true) : largeOrderCertificate N d := by
  refine ⟨w,?_,?_⟩
  · have : NeZero N := ⟨by omega⟩
    apply ZMod.val_injective N
    rw [← lucasPowBits_nat_correct,hw,@ZMod.val_one N ⟨hN⟩]
  · intro r hr hrd
    exact orderUnitCheck_sound (by omega) (hunit r (primeMemProduct hr f hf (hprod ▸ hrd)))

end MathGacha
