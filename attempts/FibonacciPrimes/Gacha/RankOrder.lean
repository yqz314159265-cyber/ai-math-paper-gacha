import Gacha.CubicCertificate
import Gacha.FactorRank
import Gacha.QuarticForm

namespace MathGacha

/-- The negative rank residue, expressed in the multiplier of a certified order. -/
def negativeRankMultiplier (p d : ℕ) [Fact p.Prime] : ℕ :=
  ((-2:ZMod p)/(d:ZMod p)).val

/-- For a certified order prime to the index, each possible prime factor
starts in one of two explicit multiplier classes. -/
theorem rankOrderFactorClasses {p d q : ℕ} [Fact p.Prime] (hp5 : 5<p) (hd : 0<d)
    (hc : ¬ p∣d) (cert : largeOrderCertificate (Nat.fib p) d)
    (hq : q.Prime) (hdiv : q∣Nat.fib p) :
    ∃ x>0, q=d*x+1 ∧ (x%p=0 ∨ x%p=negativeRankMultiplier p d) := by
  have hp : p.Prime := Fact.out
  have hq1 := hq.one_lt
  obtain ⟨x,hx⟩ := orderDividesPrimeFactorSubOne hd cert hq hdiv
  have he : q=d*x+1 := by omega
  have hxpos : 0<x := by
    by_contra! hz
    have heq : x=0 := by omega
    simp [heq] at he
    omega
  refine ⟨x,hxpos,he,?_⟩
  have hd0 : (d:ZMod p)≠0 := fun h => hc ((ZMod.natCast_eq_zero_iff d p).mp h)
  rcases fibPrimeFactorCongruence hp hp5 hq hdiv with h|h
  · rw [hx] at h
    exact Or.inl (Nat.mod_eq_zero_of_dvd ((hp.dvd_mul.mp h).resolve_left hc))
  · have hzero := (ZMod.natCast_eq_zero_iff (q+1) p).mpr h
    rw [he] at hzero
    push_cast at hzero
    have hz : (x:ZMod p)=(-2:ZMod p)/(d:ZMod p) := by
      apply (eq_div_iff hd0).mpr
      linear_combination hzero
    exact Or.inr (by simpa only [ZMod.val_natCast,negativeRankMultiplier] using congrArg ZMod.val hz)

/-- A small partial factor of F_p−1 can suffice when the index forces a
large first possible multiplier. -/
theorem fibPrimeOfRankOrderSize {p d : ℕ} [Fact p.Prime] (hp5 : 5<p) (hd : 0<d)
    (hc : ¬ p∣d) (cert : largeOrderCertificate (Nat.fib p) d)
    (hsize : Nat.fib p < (d*negativeRankMultiplier p d+1)^2) : (Nat.fib p).Prime := by
  have hp : p.Prime := Fact.out
  have hn := Nat.le_fib_self (show 5≤p by omega)
  by_contra hh
  let q := (Nat.fib p).minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  obtain ⟨x,hx,he,hr⟩ := rankOrderFactorClasses hp5 hd hc cert hq (Nat.minFac_dvd _)
  have hqbound : q^2≤Nat.fib p := Nat.minFac_sq_le_self (by omega) hh
  have hj : negativeRankMultiplier p d≤x := by
    rcases hr with hr|hr
    · have hpx := Nat.le_of_dvd hx (Nat.dvd_of_mod_eq_zero hr)
      exact (ZMod.val_lt ((-2:ZMod p)/(d:ZMod p))).le.trans hpx
    · exact hr ▸ Nat.mod_le x p
  have hlow : d*negativeRankMultiplier p d+1≤q := by rw [he]; gcongr
  exact (Nat.not_lt_of_ge (Nat.le_trans (Nat.pow_le_pow_left hlow 2) hqbound)) hsize

/-- In the inert index classes the two factors have opposite rank residues. -/
theorem inertCompositeRankFactors {p d : ℕ} [Fact p.Prime] (hp5 : 5<p) (hd : 0<d)
    (hc : ¬ p∣d) (hdN : d∣Nat.fib p-1)
    (cert : largeOrderCertificate (Nat.fib p) d)
    (hinert : (Nat.fib p : ZMod p) = -1)
    (hh : ¬ (Nat.fib p).Prime) : ∃ x y : ℕ, p≤x ∧ negativeRankMultiplier p d≤y ∧ p∣x ∧ Nat.fib p=(d*x+1)*(d*y+1) := by
  have hp : p.Prime := Fact.out
  have hn := Nat.le_fib_self (show 5≤p by omega)
  let q := (Nat.fib p).minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hq1 := hq.one_lt
  obtain ⟨b,hb⟩ := Nat.minFac_dvd (Nat.fib p)
  change Nat.fib p=q*b at hb
  have hb1 : 1<b := by
    by_contra! h
    interval_cases b
    · simp at hb
      omega
    · simp at hb
      exact hh (hb ▸ hq)
  obtain ⟨x,hx,he,hr⟩ := rankOrderFactorClasses hp5 hd hc cert hq (Nat.minFac_dvd _)
  have hqmod : 1 ≡ q [MOD d] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨x,by omega⟩
  have hnmod : 1 ≡ Nat.fib p [MOD d] := (Nat.modEq_iff_dvd' (by omega)).mpr hdN
  have hbmod : 1 ≡ b [MOD d] := by
    rw [hb] at hnmod
    simpa using hnmod.trans (hqmod.mul_right b).symm
  obtain ⟨y,hy⟩ := (Nat.modEq_iff_dvd' (by omega)).mp hbmod
  have hbe : b=d*y+1 := by omega
  have hypos : 0<y := by
    by_contra! hz
    have hy0 : y=0 := by omega
    simp [hy0] at hbe
    omega
  have hd0 : (d:ZMod p)≠0 := fun h => hc ((ZMod.natCast_eq_zero_iff d p).mp h)
  rw [hb,he,hbe] at hinert
  push_cast at hinert
  have hxform : Nat.fib p=(d*x+1)*(d*y+1) := by rw [hb,he,hbe]
  rcases hr with hh0|hhj
  · have hpx := Nat.dvd_of_mod_eq_zero hh0
    have hx0 := (ZMod.natCast_eq_zero_iff x p).mpr hpx
    simp [hx0] at hinert
    have hyz : (y:ZMod p)=(-2:ZMod p)/(d:ZMod p) := by
      apply (eq_div_iff hd0).mpr
      linear_combination hinert
    have hyval : y%p=negativeRankMultiplier p d := by
      simpa only [ZMod.val_natCast,negativeRankMultiplier] using congrArg ZMod.val hyz
    have hpx' := Nat.le_of_dvd hx hpx
    have hjy := hyval ▸ Nat.mod_le y p
    exact ⟨x,y,hpx',hjy,hpx,hxform⟩
  · have hxe : (x:ZMod p)=(-2:ZMod p)/(d:ZMod p) := by
      apply ZMod.val_injective p
      simpa only [ZMod.val_natCast,negativeRankMultiplier] using hhj
    have hdx := (eq_div_iff hd0).mp hxe
    have hsign : (d:ZMod p)*x+1 = -1 := by linear_combination hdx
    rw [hsign] at hinert
    have hdy : (d:ZMod p)*y=0 := by linear_combination -hinert
    have hpy := (ZMod.natCast_eq_zero_iff y p).mp ((mul_eq_zero.mp hdy).resolve_left hd0)
    have hy' := Nat.le_of_dvd hypos hpy
    have hx' := hhj ▸ Nat.mod_le x p
    exact ⟨y,x,hy',hx',hpy,hxform.trans (Nat.mul_comm _ _)⟩

/-- In the inert index class the two factors of any putative factorisation have
opposite signs modulo p. The two different first multipliers can both be used. -/
theorem fibPrimeOfOppositeRankOrders {p d : ℕ} [Fact p.Prime] (hp5 : 5<p) (hd : 0<d)
    (hc : ¬ p∣d) (hdN : d∣Nat.fib p-1)
    (cert : largeOrderCertificate (Nat.fib p) d)
    (hinert : (Nat.fib p : ZMod p) = -1)
    (hsize : Nat.fib p < (d*p+1)*(d*negativeRankMultiplier p d+1)) : (Nat.fib p).Prime := by
  by_contra hh
  obtain ⟨x,y,hx,hy,_,he⟩ := inertCompositeRankFactors hp5 hd hc hdN cert hinert hh
  rw [he] at hsize
  exact (Nat.not_lt_of_ge (show (d*p+1)*(d*negativeRankMultiplier p d+1)≤(d*x+1)*(d*y+1) by gcongr)) hsize

/-- Frobenius on the difference of the two characteristic roots evaluates the
entire Fibonacci value modulo its prime index. -/
theorem fibAtIndexLegendre {p : ℕ} [Fact p.Prime] (hp5 : 5<p) :
    (Nat.fib p:ZMod p)=(legendreSym p 5:ZMod p) := by
  let E := AlgebraicClosure (ZMod p)
  obtain ⟨a,b,ha,hb,_,hs,hne⟩ := fibRootsAtPrime (q:=p) (by omega) (by omega)
  have hp : p.Prime := Fact.out
  obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
  have he : (Nat.fib p:E)=(5:E)^(p/2) := by
    apply mul_left_cancel₀ hne
    calc
      (a-b)*(Nat.fib p:E) = a^p-b^p := fibPowerDifference ha hb p
      _ = (a-b)^p := (sub_pow_char a b).symm
      _ = (a-b)*(5:E)^(p/2) := by
        rw [← hs,← pow_mul,← pow_succ']
        congr 1
        omega
  rw [legendreSym.eq_pow]
  apply (algebraMap (ZMod p) E).injective
  norm_num [map_ofNat] at *
  exact he

/-- The two inert congruence classes of the prime index select the stronger
opposite-factor test without any further calculation modulo p. -/
theorem fibPrimeOfInertIndexOrder {p d : ℕ} [Fact p.Prime] (hp5 : 5<p)
    (hpmod : p%5=2 ∨ p%5=3) (hd : 0<d) (hc : ¬p∣d)
    (hdN : d∣Nat.fib p-1) (cert : largeOrderCertificate (Nat.fib p) d)
    (hsize : Nat.fib p < (d*p+1)*(d*negativeRankMultiplier p d+1)) : (Nat.fib p).Prime := by
  apply fibPrimeOfOppositeRankOrders hp5 hd hc hdN cert _ hsize
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hleg : legendreSym p 5 = -1 := by
    rw [show (5:ℤ)=(5:ℕ) by norm_num,legendreSym.quadratic_reciprocity_one_mod_four (p:=5) (q:=p) (by decide) (by omega)]
    rw [jacobiSym.legendreSym.to_jacobiSym,jacobiAtFive]
    rcases hpmod with h|h <;> simp [h]
  rw [fibAtIndexLegendre hp5,hleg]
  norm_num

end MathGacha
