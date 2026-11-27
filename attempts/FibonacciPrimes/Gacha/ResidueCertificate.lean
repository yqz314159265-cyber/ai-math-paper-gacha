import Gacha.CubicCertificate

namespace MathGacha

/-- Tail-recursive modular exponentiation. Fuel exhaustion reports no result. -/
def residuePower (N : ℕ) : ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, e, _, c => if e=0 then some (c%N) else none
  | f+1, e, b, c =>
    if e=0 then some (c%N)
    else residuePower N f (e/2) (b*b%N) (if e%2=0 then c else c*b%N)

theorem residuePower_sound {N v : ℕ} (f e b c : ℕ) (h : residuePower N f e b c=some v) :
    (v:ZMod N)=(c:ZMod N)*(b:ZMod N)^e := by
  induction f generalizing e b c with
  | zero =>
    by_cases he : e=0
    · subst e
      simp [residuePower] at h
      simp [← h]
    · simp [residuePower,he] at h
  | succ f ih =>
    rw [residuePower] at h
    split at h
    next he =>
      subst e
      simp only [Option.some.injEq] at h
      simp [← h]
    next he =>
      have hh := ih _ _ _ h
      by_cases hv : e%2=0
      · rw [if_pos hv] at hh
        simp only [ZMod.natCast_mod,Nat.cast_mul] at hh
        rw [← pow_two (b:ZMod N),← pow_mul] at hh
        rwa [show 2*(e/2)=e by omega] at hh
      · rw [if_neg hv] at hh
        simp only [ZMod.natCast_mod,Nat.cast_mul] at hh
        rw [← pow_two (b:ZMod N),← pow_mul] at hh
        calc
          _ = _ := hh
          _ = (c:ZMod N)*(b:ZMod N)^(2*(e/2)+1) := by rw [pow_succ]; ring
          _ = _ := by rw [show 2*(e/2)+1=e by omega]

/-- Ordinary-integer gcd test for the unit condition in an order certificate. -/
def residueUnitTest (N f e b : ℕ) : Bool :=
  match residuePower N f e b 1 with
  | none => false
  | some v => decide ((v+N-1).Coprime N)

theorem residueUnitTest_sound {N f e b : ℕ} (hn : 0<N) (h : residueUnitTest N f e b=true) :
    IsUnit ((b:ZMod N)^e-1) := by
  unfold residueUnitTest at h
  split at h
  next => contradiction
  next v he =>
    have hz := residuePower_sound _ _ _ _ he
    have hcp : (v+N-1).Coprime N := of_decide_eq_true h
    have hu := (ZMod.isUnit_iff_coprime (v+N-1) N).mpr hcp
    rw [Nat.cast_sub (by omega : 1≤v+N),Nat.cast_add,ZMod.natCast_self,Nat.cast_one,add_zero] at hu
    rw [hz] at hu
    simpa using hu

theorem largeOrderOfResidueTests {N f w d : ℕ} (hn : 0<N) (qs : List ℕ)
    (hprod : d=qs.prod) (hqs : qs.Forall Nat.Prime)
    (hw : residuePower N f d w 1=some 1)
    (hu : qs.Forall (fun r => residueUnitTest N f (d/r) w=true)) : largeOrderCertificate N d := by
  refine ⟨w,?_,?_⟩
  · simpa using (residuePower_sound _ _ _ _ hw).symm
  · intro r hr hrd
    exact residueUnitTest_sound hn (List.forall_iff_forall_mem.mp hu r
      (primeMemProduct hr qs (List.forall_iff_forall_mem.mp hqs) (hprod ▸ hrd)))

end MathGacha
