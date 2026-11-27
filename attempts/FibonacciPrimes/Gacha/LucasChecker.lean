import Gacha.Primality
import Gacha.FastModFib
import Mathlib.Data.Nat.Bits

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace MathGacha

theorem lucasBitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit _ _ hn]
      cases b
      · simp [bitsValue, ih, Nat.bit]
      · simp [bitsValue, ih, Nat.bit]

/-- Binary square-and-multiply directly in the residue ring. The list is
low-bit-first, so each recursive step squares the accumulated higher-bit power. -/
def lucasPowBits {d : ℕ} (a : ZMod d) : List Bool → ZMod d
  | [] => 1
  | b :: bs =>
      let y := lucasPowBits a bs
      if b then y * y * a else y * y

theorem lucasPowBits_correct {d : ℕ} (a : ZMod d) (bs : List Bool) :
    lucasPowBits a bs = a ^ bitsValue bs := by
  induction bs with
  | nil => simp [lucasPowBits, bitsValue]
  | cons b bs ih =>
      cases b
      · simp [lucasPowBits, bitsValue, ih, two_mul, pow_add]
      · simp [lucasPowBits, bitsValue, ih, two_mul, pow_add]

theorem lucasPowBits_nat_correct {d a e : ℕ} :
    lucasPowBits (a : ZMod d) e.bits = (a : ZMod d) ^ e := by
  rw [lucasPowBits_correct, lucasBitsValue_bits]

/-- One Lucas certificate: a witness and a complete factor list for n-1. -/
structure LucasCertificate where
  modulus : ℕ
  witness : ℕ
  factors : List ℕ
  deriving Repr, Inhabited

/-- Executable Boolean check for one Lucas certificate. -/
def lucasStepCheck (known : List ℕ) (c : LucasCertificate) : Bool :=
  decide (2 ≤ c.modulus) &&
  decide (c.modulus - 1 = c.factors.prod) &&
  c.factors.all (fun q => decide (q ∈ known)) &&
  decide ((lucasPowBits (c.witness : ZMod c.modulus) (c.modulus - 1).bits).val = 1) &&
  c.factors.all (fun q => decide
    ((lucasPowBits (c.witness : ZMod c.modulus) ((c.modulus - 1) / q).bits).val ≠ 1))

/-- Check a topologically ordered list; each accepted modulus becomes known to
subsequent entries. `small` is the finite table of base primes. -/
def lucasCertificatesCheckAux (small known : List ℕ) : List LucasCertificate → Bool
  | [] => true
  | c :: cs =>
      lucasStepCheck (small ++ known) c &&
        lucasCertificatesCheckAux small (c.modulus :: known) cs

def lucasCertificatesCheck (small : List ℕ) (cs : List LucasCertificate) : Bool :=
  lucasCertificatesCheckAux small [] cs

theorem lucasStepCheck_sound (small known : List ℕ) (c : LucasCertificate)
    (hsmall : ∀ q ∈ small, q.Prime)
    (hknown : ∀ q ∈ known, q.Prime)
    (hcheck : lucasStepCheck (small ++ known) c = true) : c.modulus.Prime := by
  change ((((decide (2 ≤ c.modulus) && decide (c.modulus - 1 = c.factors.prod)) &&
      c.factors.all (fun q => decide (q ∈ small ++ known))) &&
      decide ((lucasPowBits (c.witness : ZMod c.modulus) (c.modulus - 1).bits).val = 1)) &&
      c.factors.all (fun q => decide
        ((lucasPowBits (c.witness : ZMod c.modulus) ((c.modulus - 1) / q).bits).val ≠ 1))) = true at hcheck
  rcases Bool.and_eq_true_iff.mp hcheck with ⟨hprefix, hdiff⟩
  rcases Bool.and_eq_true_iff.mp hprefix with ⟨hprefix, hpow⟩
  rcases Bool.and_eq_true_iff.mp hprefix with ⟨hprefix, hmem⟩
  rcases Bool.and_eq_true_iff.mp hprefix with ⟨hge, hprod⟩
  have hge : 2 ≤ c.modulus := of_decide_eq_true hge
  have hprod : c.modulus - 1 = c.factors.prod := of_decide_eq_true hprod
  have hpow : (lucasPowBits (c.witness : ZMod c.modulus)
      (c.modulus - 1).bits).val = 1 := of_decide_eq_true hpow
  have hmod0 : c.modulus ≠ 0 := by omega
  have hmod1 : 1 < c.modulus := by omega
  have hvalOne : (1 : ZMod c.modulus).val = 1 := @ZMod.val_one c.modulus ⟨hmod1⟩
  apply lucasList c.modulus (c.witness : ZMod c.modulus) c.factors hprod
  · intro q hq
    have hqknown : q ∈ small ++ known := by
      have hall := (List.all_eq_true.mp hmem) q hq
      exact of_decide_eq_true hall
    have hqknown := hqknown
    rcases List.mem_append.mp hqknown with hs | hk
    · exact hsmall q hs
    · exact hknown q hk
  · apply @ZMod.val_injective c.modulus ⟨hmod0⟩
    have hpow' : ((c.witness : ZMod c.modulus) ^ (c.modulus - 1)).val = 1 := by
      simpa only [lucasPowBits_nat_correct] using hpow
    simpa [hvalOne] using hpow'
  · intro q hq
    have hqdiff := (List.all_eq_true.mp hdiff) q hq
    have hne : (lucasPowBits (c.witness : ZMod c.modulus)
        ((c.modulus - 1) / q).bits).val ≠ 1 := of_decide_eq_true hqdiff
    have hnePow : ((c.witness : ZMod c.modulus) ^ ((c.modulus - 1) / q)).val ≠ 1 := by
      simpa only [lucasPowBits_nat_correct] using hne
    intro heq
    apply hnePow
    simpa [hvalOne] using congrArg ZMod.val heq

theorem lucasCertificatesCheckAux_sound (small known : List ℕ)
    (cs : List LucasCertificate)
    (hsmall : ∀ q ∈ small, q.Prime)
    (hknown : ∀ q ∈ known, q.Prime)
    (hcheck : lucasCertificatesCheckAux small known cs = true) :
    ∀ c ∈ cs, c.modulus.Prime := by
  induction cs generalizing known with
  | nil => simp
  | cons c cs ih =>
      simp only [lucasCertificatesCheckAux, Bool.and_eq_true] at hcheck
      have hc : c.modulus.Prime := lucasStepCheck_sound small known c hsmall hknown hcheck.1
      have hknown' : ∀ q ∈ c.modulus :: known, q.Prime := by
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hc
        · exact hknown q hq
      have hrest := ih (c.modulus :: known) hknown' hcheck.2
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hc
      · exact hrest d hd

theorem lucasCertificatesCheck_sound (small : List ℕ) (cs : List LucasCertificate)
    (hsmall : ∀ q ∈ small, q.Prime)
    (hcheck : lucasCertificatesCheck small cs = true) :
    ∀ c ∈ cs, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound small [] cs hsmall (by simp) hcheck

def cert7 : LucasCertificate :=
  ⟨7, 3, [2, 3]⟩

theorem lucasCheck7 : lucasCertificatesCheck [2, 3] [cert7] = true := by
  decide

theorem lucasCheck7_prime : Nat.Prime cert7.modulus := by
  have hsmall : ∀ q ∈ ([2, 3] : List ℕ), q.Prime := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  have h := lucasCertificatesCheck_sound [2, 3] [cert7] hsmall lucasCheck7
  exact h cert7 (by simp [cert7])
end MathGacha
