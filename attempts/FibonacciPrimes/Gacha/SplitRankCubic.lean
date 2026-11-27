import Gacha.RankCubic

namespace MathGacha

/-- Sum and product recovered from a putative factor pair in a self-inverse
residue class b modulo T. -/
def classQuotient (N T b : ℕ) := (N-b^2)/T
def classMultiplierSum (N T b : ℕ) := (b*classQuotient N T b)%T
def classMultiplierProduct (N T b : ℕ) :=
  (classQuotient N T b-b*classMultiplierSum N T b)/T

def classSquareDiscriminant (N T b : ℕ) : Prop :=
  ∃ u : ℕ, (classMultiplierSum N T b)^2=u^2+4*classMultiplierProduct N T b

/-- If both nontrivial factors lie in the same self-inverse residue class,
the cube-root bound recovers both multipliers up to their order. -/
theorem sameClassForcesSquare {N T b x y : ℕ} (hT : 0<T) (hb : 0<b)
    (hinv : b^2 ≡ 1 [MOD T]) (hx : 0<x) (hy : 0<y)
    (he : N=(b+T*x)*(b+T*y)) (hsize : N<T^3) : classSquareDiscriminant N T b := by
  have hxy : x+y≤x*y+1 := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero hx.ne'
    obtain ⟨c,hc⟩ := Nat.exists_eq_succ_of_ne_zero hy.ne'
    rw [ha,hc]
    nlinarith
  have hs : x+y<T := by
    by_contra! hh
    have h1 := Nat.mul_le_mul_left (T^2) (hh.trans hxy)
    have h2 := Nat.mul_le_mul_left T hh
    have h3 : T*(x+y)≤b*(T*(x+y)) := Nat.le_mul_of_pos_left _ hb
    nlinarith only [h1,h2,h3,he,hsize]
  have hsub : N=b^2+T*(b*(x+y)+T*(x*y)) := by rw [he]; ring
  have hc : classQuotient N T b=b*(x+y)+T*(x*y) := by
    unfold classQuotient
    rw [hsub,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ hT]
  have hz : b*classQuotient N T b ≡ x+y [MOD T] := calc
    _ = b^2*(x+y)+T*(b*(x*y)) := by rw [hc]; ring
    _ ≡ b^2*(x+y) [MOD T] := by unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]
    _ ≡ _ [MOD T] := by simpa using hinv.mul_right (x+y)
  have hsum : classMultiplierSum N T b=x+y := by
    exact Eq.trans hz (Nat.mod_eq_of_lt hs)
  have hpr : classMultiplierProduct N T b=x*y := by
    unfold classMultiplierProduct
    rw [hsum,hc,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ hT]
  unfold classSquareDiscriminant
  rw [hsum,hpr]
  rcases le_total x y with h|h
  · exact ⟨y-x,by have hz := Nat.sub_add_cancel h; nlinarith only [congrArg (fun z : ℕ => z^2) hz,congrArg (fun z : ℕ => x*z) hz]⟩
  · exact ⟨x-y,by have hz := Nat.sub_add_cancel h; nlinarith only [congrArg (fun z : ℕ => z^2) hz,congrArg (fun z : ℕ => y*z) hz]⟩

/-- A fixed residue class is impossible below the cubic bound if its
integer discriminant is nonsquare and its least representative is handled. -/
theorem excludeEqualClassFactorization {N T b q v : ℕ} (hT : 1<T)
    (hb : 0<b) (hbt : b<T) (hb2 : b^2 ≡ 1 [MOD T]) (hN : N ≡ 1 [MOD T])
    (he : N=q*v) (hq : 1<q) (hv : 1<v) (hr : q ≡ b [MOD T])
    (hbase : b=1 ∨ ¬b∣N) (hsize : N<T^3) (hnosq : ¬classSquareDiscriminant N T b) : False := by
  have hqz : (q:ZMod T)=(b:ZMod T) := (ZMod.natCast_eq_natCast_iff ..).mpr hr
  have hbz : (b:ZMod T)^2=1 := by
    simpa using (ZMod.natCast_eq_natCast_iff ..).mpr hb2
  have hnz : (q:ZMod T)*(v:ZMod T)=1 := by
    rw [he] at hN
    simpa using (ZMod.natCast_eq_natCast_iff ..).mpr hN
  have hvz : (v:ZMod T)=(q:ZMod T) := calc
    _ = (q:ZMod T)^2*v := by rw [hqz,hbz,one_mul]
    _ = (q:ZMod T)*(q*v) := by ring
    _ = _ := by rw [hnz,mul_one]
  have hvr := (ZMod.natCast_eq_natCast_iff ..).mp (hvz.trans hqz)
  have hqr : q%T=b := Eq.trans hr (Nat.mod_eq_of_lt hbt)
  have hvr' : v%T=b := Eq.trans hvr (Nat.mod_eq_of_lt hbt)
  have hqe := Nat.mod_add_div q T
  have hve := Nat.mod_add_div v T
  rw [hqr] at hqe
  rw [hvr'] at hve
  have hqdiv : 0<q/T := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,Nat.mul_zero,Nat.add_zero] at hqe
    rcases hbase with h|h
    · omega
    · exact h ⟨v,by rwa [hqe]⟩
  have hvdiv : 0<v/T := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,Nat.mul_zero,Nat.add_zero] at hve
    rcases hbase with h|h
    · omega
    · exact h ⟨q,by rw [hve,Nat.mul_comm]; exact he⟩
  exact hnosq (sameClassForcesSquare (by omega) hb hb2 hqdiv hvdiv (by rw [hqe,hve,he]) hsize)

def negativeRankBase (p d : ℕ) [Fact p.Prime] : ℕ :=
  (d*negativeRankMultiplier p d+1)%(d*p)

/-- In a split prime-index class, the combined modulus d*p gives a
cubic-range primality test with a discriminant for each of two residues. -/
theorem fibPrimeSplitRankCubic {p d : ℕ} [Fact p.Prime] (hp5 : 5<p) (hd : 0<d)
    (hc : ¬p∣d) (hdN : d∣Nat.fib p-1) (cert : largeOrderCertificate (Nat.fib p) d)
    (hsplit : (Nat.fib p:ZMod p)=1) (hsize : Nat.fib p<(d*p)^3)
    (hbase : ¬ negativeRankBase p d ∣ Nat.fib p)
    (hpos : ¬classSquareDiscriminant (Nat.fib p) (d*p) 1)
    (hneg : ¬classSquareDiscriminant (Nat.fib p) (d*p) (negativeRankBase p d)) :
    (Nat.fib p).Prime := by
  have hp : p.Prime := Fact.out
  let T := d*p
  let j := negativeRankMultiplier p d
  let b := negativeRankBase p d
  have hT : 1<T := (show 1<p by omega).trans_le (Nat.le_mul_of_pos_left _ hd)
  have hT0 : 0<T := by omega
  have hn := Nat.le_fib_self (show 5≤p by omega)
  have hnD : Nat.fib p ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' (by omega)).mpr hdN).symm
  have hnP : Nat.fib p ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using hsplit)
  have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hc).symm
  have hNT : Nat.fib p ≡ 1 [MOD T] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hnD,hnP⟩
  have hbaseT : b ≡ d*j+1 [MOD T] := Nat.mod_modEq _ _
  have hbD : d*j+1 ≡ 1 [MOD d] := Nat.modulus_mul_add_modEq_iff.mpr (Nat.ModEq.refl _)
  have hD0 : (d:ZMod p)≠0 := fun h => hc ((ZMod.natCast_eq_zero_iff d p).mp h)
  have hjz : (j:ZMod p)=(-2:ZMod p)/(d:ZMod p) := ZMod.natCast_zmod_val _
  have hbpz : (d:ZMod p)*j+1= -1 := by linear_combination (eq_div_iff hD0).mp hjz
  have hbP : (d*j+1)^2 ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff ..).mp (by push_cast; rw [hbpz]; norm_num)
  have hbT : b^2 ≡ 1 [MOD T] := (hbaseT.pow 2).trans ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨by simpa using hbD.pow 2,hbP⟩)
  have hbt : b<T := Nat.mod_lt _ hT0
  have hb0 : 0<b := by
    by_contra! h
    have hz : b=0 := by omega
    change b^2%T=1%T at hbT
    simp [hz,Nat.mod_eq_of_lt hT] at hbT
  by_contra hh
  let q := (Nat.fib p).minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  obtain ⟨v,he⟩ := Nat.minFac_dvd (Nat.fib p)
  change Nat.fib p=q*v at he
  have hv1 : 1<v := by
    by_contra! h
    interval_cases v
    · simp at he
      omega
    · simp at he
      exact hh (he ▸ hq)
  obtain ⟨x,_,hqx,hxc⟩ := rankOrderFactorClasses hp5 hd hc cert hq (Nat.minFac_dvd _)
  have hxv := Nat.mod_add_div x p
  rcases hxc with hx|hx
  · have hqT : q ≡ 1 [MOD T] := by
      rw [hx] at hxv
      simp only [zero_add] at hxv
      rw [hqx,← hxv,← Nat.mul_assoc]
      exact Nat.modulus_mul_add_modEq_iff.mpr (Nat.ModEq.refl _)
    exact excludeEqualClassFactorization hT (by decide) hT (by rfl) hNT he hq.one_lt hv1 hqT (Or.inl rfl) hsize hpos
  · have hqT : q ≡ b [MOD T] := by
      rw [hx] at hxv
      change j+p*(x/p)=x at hxv
      have hval : q=(d*j+1)+T*(x/p) := calc
        _ = d*(j+p*(x/p))+1 := hqx.trans (congrArg (fun t : ℕ => d*t+1) hxv.symm)
        _ = _ := by dsimp [T]; ring
      rw [hval]
      exact (Nat.modEq_add_modulus_mul_iff.mpr (Nat.ModEq.refl _)).symm.trans hbaseT.symm
    exact excludeEqualClassFactorization hT hb0 hbt hbT hNT he hq.one_lt hv1 hqT (Or.inr hbase) hsize hneg

/-- Executable test for excluding the square forced by a same-class factor pair. -/
def classNonsquareTest (N T b : ℕ) : Bool :=
  let a := (classMultiplierSum N T b)^2
  let c := 4*classMultiplierProduct N T b
  decide (a<c ∨ (Nat.sqrt (a-c))^2≠a-c)

theorem classNonsquareTest_iff (N T b : ℕ) :
    classNonsquareTest N T b=true ↔ ¬classSquareDiscriminant N T b := by
  let a := (classMultiplierSum N T b)^2
  let c := 4*classMultiplierProduct N T b
  change decide (a<c ∨ (Nat.sqrt (a-c))^2≠a-c)=true ↔ ¬∃ u : ℕ, a=u^2+c
  rw [decide_eq_true_eq]
  constructor
  · rintro (h|h) ⟨u,hu⟩
    · omega
    · have e : a-c=u^2 := by omega
      rw [e,Nat.sqrt_eq'] at h
      exact h rfl
  · intro hh
    by_contra! h
    exact hh ⟨Nat.sqrt (a-c), by omega⟩

end MathGacha
