import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

namespace MathGacha

/-- A nonzero affine linear form has exactly one zero among units of a prime field. -/
theorem multiCRTCardAffineUnitAvoiders {r : ℕ} (hr : r.Prime)
    [NeZero r] (k c : ZMod r) (hk : k ≠ 0) (hc : c ≠ 0) :
    Fintype.card {x : (ZMod r)ˣ // k * (x : ZMod r) + c ≠ 0} = r - 2 := by
  have hfact : Fact r.Prime := ⟨hr⟩
  classical
  let rootVal : ZMod r := -(k⁻¹ * c)
  have hrootVal : rootVal ≠ 0 := by
    intro hz
    have hz' : k⁻¹ * c = 0 := by simpa [rootVal] using hz
    rcases mul_eq_zero.mp hz' with hi | hci
    · exact hk (inv_eq_zero.mp hi)
    · exact hc hci
  let root : (ZMod r)ˣ := Units.mk0 rootVal hrootVal
  have hroot : k * (root : ZMod r) + c = 0 := by
    calc
      k * (root : ZMod r) + c = -(k * (k⁻¹ * c)) + c := by simp [root, rootVal]
      _ = 0 := by rw [← mul_assoc, mul_inv_cancel₀ hk, one_mul]; ring
  let bad : (ZMod r)ˣ → Prop := fun x => k * (x : ZMod r) + c = 0
  have hbad : ∀ x, bad x ↔ x = root := by
    intro x
    constructor
    · intro hx
      apply Units.ext
      have hdiff : k * ((x : ZMod r) - (root : ZMod r)) = 0 := by
        calc
          k * ((x : ZMod r) - (root : ZMod r)) =
              (k * (x : ZMod r) + c) - (k * (root : ZMod r) + c) := by ring
          _ = 0 := by rw [hx, hroot]; ring
      rcases mul_eq_zero.mp hdiff with hz | hdiff
      · exact False.elim (hk hz)
      · exact sub_eq_zero.mp hdiff
    · rintro rfl
      exact hroot
  have hbadcard : Fintype.card {x : (ZMod r)ˣ // bad x} = 1 := by
    let e : {x : (ZMod r)ˣ // bad x} ≃ {x : (ZMod r)ˣ // x = root} :=
      Equiv.subtypeEquivRight hbad
    calc
      _ = Fintype.card {x : (ZMod r)ˣ // x = root} := Fintype.card_congr e
      _ = 1 := Fintype.card_subtype_eq root
  change Fintype.card {x : (ZMod r)ˣ // ¬ bad x} = r - 2
  rw [Fintype.card_subtype_compl, hbadcard, Fintype.card_units, ZMod.card]
  omega

abbrev multiCRTIndex (s : Finset ℕ) := {r // r ∈ s}
abbrev multiCRTModulus (s : Finset ℕ) := ∏ r : multiCRTIndex s, r.1

/-- The CRT equivalence on unit groups for a finite set of distinct primes. -/
noncomputable def multiCRTCrtUnitEquiv (s : Finset ℕ) (hp : ∀ r ∈ s, r.Prime) :
    (ZMod (multiCRTModulus s))ˣ ≃* ∀ r : multiCRTIndex s, (ZMod r.1)ˣ := by
  have hcop : Pairwise (fun i j : multiCRTIndex s => Nat.Coprime i.1 j.1) := by
    intro i j hij
    apply (Nat.coprime_primes (hp i.1 i.2) (hp j.1 j.2)).2
    intro heq
    exact hij (Subtype.ext heq)
  exact (Units.mapEquiv (ZMod.prodEquivPi (fun r : multiCRTIndex s => r.1) hcop).toMulEquiv).trans
    MulEquiv.piUnits

/-- Under CRT, imposing one nonzero affine exclusion independently at each prime
leaves the product of the local counts. -/
theorem multiCRTCardCrtAffineAvoiders (s : Finset ℕ)
    [NeZero (multiCRTModulus s)] [∀ r : multiCRTIndex s, NeZero r.1] [∀ r : multiCRTIndex s, Fact r.1.Prime]
    (hp : ∀ r ∈ s, r.Prime)
    (k c : ∀ r : multiCRTIndex s, ZMod r.1)
    (hk : ∀ r, k r ≠ 0) (hc : ∀ r, c r ≠ 0) :
    Fintype.card
      {x : (ZMod (multiCRTModulus s))ˣ //
        ∀ r : multiCRTIndex s, k r * ((multiCRTCrtUnitEquiv s hp x) r : ZMod r.1) + c r ≠ 0} =
      ∏ r : multiCRTIndex s, (r.1 - 2) := by
  classical
  let I := multiCRTIndex s
  let e := multiCRTCrtUnitEquiv s hp
  let P : ∀ r : I, (ZMod r.1)ˣ → Prop := fun r x =>
    k r * (x : ZMod r.1) + c r ≠ 0
  let eSub : {x : (ZMod (multiCRTModulus s))ˣ // ∀ r : I, P r (e x r)} ≃
      ∀ r : I, {x : (ZMod r.1)ˣ // P r x} := {
    toFun := fun x r => ⟨e x.1 r, x.2 r⟩
    invFun := fun x => ⟨e.symm (fun r => (x r).1), by
      intro r
      simpa only [e.apply_symm_apply] using (x r).2⟩
    left_inv := by intro x; apply Subtype.ext; exact e.left_inv x.1
    right_inv := by intro x; funext r; apply Subtype.ext; exact congrFun (e.right_inv (fun r => (x r).1)) r
  }
  calc
    _ = Fintype.card (∀ r : I, {x : (ZMod r.1)ˣ // P r x}) := Fintype.card_congr eSub
    _ = ∏ r : I, Fintype.card {x : (ZMod r.1)ˣ // P r x} := Fintype.card_pi
    _ = ∏ r : I, (r.1 - 2) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact multiCRTCardAffineUnitAvoiders (hp r.1 r.2) (k r) (c r) (hk r) (hc r)

end MathGacha








namespace MathGacha

/-- The unit CRT coordinate of a natural number is its ordinary residue modulo r. -/
theorem multiCRTCrtUnitEquivNatCast (s : Finset ℕ) (hp : ∀ r ∈ s, r.Prime)
    (n : ℕ) (hn : Nat.Coprime n (multiCRTModulus s)) (r : multiCRTIndex s) :
    ((multiCRTCrtUnitEquiv s hp (ZMod.unitOfCoprime n hn)) r : ZMod r.1) =
      (n : ZMod r.1) := by
  classical
  let f := ZMod.prodEquivPi (fun i : multiCRTIndex s => i.1)
    (show Pairwise (fun i j : multiCRTIndex s => Nat.Coprime i.1 j.1) from by
      intro i j hij
      exact (Nat.coprime_primes (hp i.1 i.2) (hp j.1 j.2)).mpr (fun heq => hij (Subtype.ext heq)))
  change (((Units.mapEquiv f.toMulEquiv (ZMod.unitOfCoprime n hn) :
    (∀ i : multiCRTIndex s, ZMod i.1)ˣ) : ∀ i : multiCRTIndex s, ZMod i.1) r) = _
  rw [Units.coe_mapEquiv]
  simp only [ZMod.coe_unitOfCoprime]
  change f (n : ZMod (multiCRTModulus s)) r = _
  rw [ZMod.prodEquivPi_apply]
  exact ZMod.cast_natCast (Finset.dvd_prod_of_mem _ (Finset.mem_univ r)) n

/-- Euler's totient of the squarefree product of a finite prime set is the product
of the local unit counts. -/
theorem multiCRTTotientModulusEqProd (s : Finset ℕ)
    (hp : ∀ r ∈ s, r.Prime) :
    Nat.totient (multiCRTModulus s) = ∏ r : multiCRTIndex s, (r.1 - 1) := by
  classical
  have hpos : 0 < multiCRTModulus s := Finset.prod_pos fun r hr => (hp r.1 r.2).pos
  have hmodNeZero : NeZero (multiCRTModulus s) := ⟨hpos.ne'⟩
  let hprimeFact : ∀ r : multiCRTIndex s, Fact r.1.Prime := fun r => ⟨hp r.1 r.2⟩
  let hrNeZero : ∀ r : multiCRTIndex s, NeZero r.1 := fun r => ⟨(hp r.1 r.2).ne_zero⟩
  have hcard : Fintype.card (ZMod (multiCRTModulus s))ˣ =
      ∏ r : multiCRTIndex s, Fintype.card (ZMod r.1)ˣ := by
    calc
      _ = Fintype.card (∀ r : multiCRTIndex s, (ZMod r.1)ˣ) :=
        Fintype.card_congr (multiCRTCrtUnitEquiv s hp).toEquiv
      _ = ∏ r : multiCRTIndex s, Fintype.card (ZMod r.1)ˣ := Fintype.card_pi
  rw [ZMod.card_units_eq_totient] at hcard
  rw [hcard]
  apply Finset.prod_congr rfl
  intro r hr
  rw [ZMod.card_units_eq_totient, Nat.totient_prime (hp r.1 r.2)]

end MathGacha








namespace MathGacha

/-- The CRT coordinate of a unit is the canonical `ZMod` cast to the factor modulus. -/
theorem multiCRTCrtUnitEquivCoe (s : Finset ℕ) (hp : ∀ r ∈ s, r.Prime)
    (u : (ZMod (multiCRTModulus s))ˣ) (r : multiCRTIndex s) :
    ((multiCRTCrtUnitEquiv s hp u) r : ZMod r.1) =
      ZMod.castHom (Finset.dvd_prod_of_mem (fun i : multiCRTIndex s => i.1) (Finset.mem_univ r))
        (ZMod r.1) (u : ZMod (multiCRTModulus s)) := by
  classical
  let f := ZMod.prodEquivPi (fun i : multiCRTIndex s => i.1)
    (show Pairwise (fun i j : multiCRTIndex s => Nat.Coprime i.1 j.1) from by
      intro i j hij
      exact (Nat.coprime_primes (hp i.1 i.2) (hp j.1 j.2)).mpr (fun heq => hij (Subtype.ext heq)))
  change (((Units.mapEquiv f.toMulEquiv u : (∀ i : multiCRTIndex s, ZMod i.1)ˣ) :
    ∀ i : multiCRTIndex s, ZMod i.1) r) = _
  rw [Units.coe_mapEquiv]
  change f (u : ZMod (multiCRTModulus s)) r = _
  rw [ZMod.prodEquivPi_apply]

/-- A finite set of good residue classes, represented directly in `ZMod M`.
Every member is a unit and satisfies one prescribed nonzero affine exclusion at
each prime coordinate. -/
theorem multiCRTExistsGoodResidueFinset (s : Finset ℕ)
    [NeZero (multiCRTModulus s)] [∀ r : multiCRTIndex s, NeZero r.1] [∀ r : multiCRTIndex s, Fact r.1.Prime]
    (hp : ∀ r ∈ s, r.Prime)
    (k c : ∀ r : multiCRTIndex s, ZMod r.1)
    (hk : ∀ r, k r ≠ 0) (hc : ∀ r, c r ≠ 0) :
    ∃ T : Finset (ZMod (multiCRTModulus s)),
      (∀ a ∈ T, IsUnit a) ∧
      T.card = ∏ r : multiCRTIndex s, (r.1 - 2) ∧
      (∀ a ∈ T, ∀ r : multiCRTIndex s,
        k r * (ZMod.castHom (Finset.dvd_prod_of_mem (fun i : multiCRTIndex s => i.1)
          (Finset.mem_univ r)) (ZMod r.1) a) + c r ≠ 0) := by
  classical
  let P (u : (ZMod (multiCRTModulus s))ˣ) :=
    ∀ r : multiCRTIndex s, k r * ((multiCRTCrtUnitEquiv s hp u) r : ZMod r.1) + c r ≠ 0
  let G : Finset (ZMod (multiCRTModulus s))ˣ := Finset.univ.filter P
  let T : Finset (ZMod (multiCRTModulus s)) := Finset.image (fun u : (ZMod (multiCRTModulus s))ˣ => (u : ZMod (multiCRTModulus s))) G
  have hcardSubtype : Fintype.card {u : (ZMod (multiCRTModulus s))ˣ // P u} =
      Fintype.card
        {u : (ZMod (multiCRTModulus s))ˣ //
          ∀ r : multiCRTIndex s, k r * ((multiCRTCrtUnitEquiv s hp u) r : ZMod r.1) + c r ≠ 0} := by
    rfl
  have hGcard : G.card = Fintype.card {u : (ZMod (multiCRTModulus s))ˣ // P u} := by
    simp [G, Fintype.card_subtype]
  have hTcard : T.card = G.card := by
    apply Finset.card_image_of_injective
    intro u v huv
    exact Units.ext huv
  have hcount := multiCRTCardCrtAffineAvoiders s hp k c hk hc
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
    exact ⟨u, rfl⟩
  · calc
      T.card = G.card := hTcard
      _ = Fintype.card {u : (ZMod (multiCRTModulus s))ˣ // P u} := hGcard
      _ = ∏ r : multiCRTIndex s, (r.1 - 2) := hcount
  · intro a ha r
    rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
    have hgood := (Finset.mem_filter.mp hu).2 r
    rw [← multiCRTCrtUnitEquivCoe s hp u r]
    exact hgood

/-- The relative density of the good CRT classes is the product of their local
unit proportions. -/
theorem multiCRTGoodResidueFinsetRatio (s : Finset ℕ)
    [NeZero (multiCRTModulus s)] [∀ r : multiCRTIndex s, NeZero r.1] [∀ r : multiCRTIndex s, Fact r.1.Prime]
    (hp : ∀ r ∈ s, r.Prime) :
    (∏ r : multiCRTIndex s, ((r.1 - 2 : ℕ) : ℝ) / ((r.1 - 1 : ℕ) : ℝ)) =
      ((∏ r : multiCRTIndex s, (r.1 - 2 : ℕ) : ℝ) / (Nat.totient (multiCRTModulus s) : ℝ)) := by
  rw [multiCRTTotientModulusEqProd s hp]
  simp only [Nat.cast_prod]
  exact (Finset.prod_div_distrib (s := Finset.univ)
    (fun r : multiCRTIndex s => ((r.1 - 2 : ℕ) : ℝ))
    (fun r : multiCRTIndex s => ((r.1 - 1 : ℕ) : ℝ)))

end MathGacha
