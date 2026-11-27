import Gacha.RankOrder

namespace MathGacha

/-- Bounded opposite rank residues allow the two factor multipliers to be
recovered from an integer quotient and remainder modulo d*p. -/
theorem fibPrimeOfRankCubic {p d c : ℕ} [Fact p.Prime] (hp5 : 5<p) (hd : 0<d)
    (hc : ¬p∣d) (hform : Nat.fib p=d*c+1) (cert : largeOrderCertificate (Nat.fib p) d)
    (hinert : (Nat.fib p:ZMod p) = -1)
    (hsize : Nat.fib p + d^2*(negativeRankMultiplier p d)^2 <
      1+d^2*p+d^3*p*negativeRankMultiplier p d)
    (hdisc : ¬ ∃ u : ℕ, (c%(d*p))^2 = u^2+4*p*(c/(d*p))) : (Nat.fib p).Prime := by
  by_contra hh
  let j := negativeRankMultiplier p d
  have hj : j≤p := (ZMod.val_lt ((-2:ZMod p)/(d:ZMod p))).le
  have hdN : d∣Nat.fib p-1 := ⟨c,by omega⟩
  obtain ⟨x,y,hpx,hjy,hdiv,he⟩ := inertCompositeRankFactors hp5 hd hc hdN cert hinert hh
  change j≤y at hjy
  change Nat.fib p+d^2*j^2 < 1+d^2*p+d^3*p*j at hsize
  have hjx := hj.trans hpx
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le hjx
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hjy
  have hprod : j*(x+y)≤x*y+j^2 := by rw [hu,hv]; nlinarith
  have hs : x+y<d*p := by
    by_contra! h
    have hjh := Nat.mul_le_mul_left j h
    have ha := Nat.mul_le_mul_left (d^2) (hjh.trans hprod)
    have hb := Nat.mul_le_mul_left d h
    nlinarith only [ha,hb,he,hsize]
  obtain ⟨k,hk⟩ := hdiv
  have hcform : c=x+y+(d*p)*(k*y) := by
    apply Nat.eq_of_mul_eq_mul_left hd
    rw [hk] at he ⊢
    nlinarith only [hform,he]
  have hdp : 0<d*p := Nat.mul_pos hd (by omega)
  have hm : c%(d*p)=x+y := by rw [hcform,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hs]
  have ht : c/(d*p)=k*y := by rw [hcform,Nat.add_mul_div_left _ _ hdp,Nat.div_eq_of_lt hs,Nat.zero_add]
  apply hdisc
  rw [hm,ht,show 4*p*(k*y)=4*(x*y) by rw [hk]; ring]
  rcases le_total x y with h|h
  · exact ⟨y-x,by have hz := Nat.sub_add_cancel h; nlinarith only [congrArg (fun z : ℕ => z^2) hz,congrArg (fun z : ℕ => x*z) hz]⟩
  · exact ⟨x-y,by have hz := Nat.sub_add_cancel h; nlinarith only [congrArg (fun z : ℕ => z^2) hz,congrArg (fun z : ℕ => y*z) hz]⟩

end MathGacha
