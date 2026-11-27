import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic

namespace MathGacha

/-- Residues modulo `d` for which `n (k n + 1)` vanishes modulo `d`. -/
def pairRootResidues (k d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun a => (a * (k * a + 1)) % d = 0

/-- Count of `n < X` for which `n (k n + 1)` is divisible by `d`. -/
def pairSiftedCount (k d X : ℕ) : ℕ :=
  Nat.count (fun n => (n * (k * n + 1)) % d = 0) X

/-- The same count, split by its residue modulo `d`. -/
def pairResidueCount (k d X : ℕ) : ℕ :=
  ∑ a ∈ pairRootResidues k d, Nat.count (fun n => n ≡ a [MOD d]) X

theorem pair_poly_mod_iff_root_residue {k d n : ℕ} (hd : 0 < d) :
    (n * (k * n + 1)) % d = 0 ↔ n % d ∈ pairRootResidues k d := by
  have hnlt : n % d < d := Nat.mod_lt _ hd
  simp [pairRootResidues, Nat.mul_mod, Nat.add_mod, hnlt]

theorem residue_class_iff_mod_eq {d a n : ℕ} (ha : a < d) :
    n ≡ a [MOD d] ↔ n % d = a := by
  constructor
  · intro h
    exact Nat.mod_eq_of_modEq h ha
  · intro h
    exact h.trans (Nat.mod_eq_of_lt ha).symm

theorem pairSiftedCount_eq_pairResidueCount
    {k d : ℕ} (hd : 0 < d) :
    ∀ X, pairSiftedCount k d X = pairResidueCount k d X := by
  intro X
  induction X with
  | zero => simp [pairSiftedCount, pairResidueCount]
  | succ X ih =>
    have ih' : Nat.count (fun n => (n * (k * n + 1)) % d = 0) X =
        ∑ a ∈ pairRootResidues k d, Nat.count (fun n => n ≡ a [MOD d]) X := by
      change Nat.count (fun n => (n * (k * n + 1)) % d = 0) X =
        ∑ a ∈ pairRootResidues k d, Nat.count (fun n => n ≡ a [MOD d]) X at ih
      exact ih
    change Nat.count (fun n => (n * (k * n + 1)) % d = 0) (X + 1) =
      ∑ a ∈ pairRootResidues k d, Nat.count (fun n => n ≡ a [MOD d]) (X + 1)
    rw [Nat.count_succ]
    simp_rw [Nat.count_succ]
    rw [Finset.sum_add_distrib, ih']
    have hinc :
        (∑ a ∈ pairRootResidues k d, if X ≡ a [MOD d] then 1 else 0) =
          if X % d ∈ pairRootResidues k d then 1 else 0 := by
      calc
        _ = ∑ a ∈ pairRootResidues k d, if X % d = a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [residue_class_iff_mod_eq (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)]
        _ = if X % d ∈ pairRootResidues k d then 1 else 0 := by simp
    have hP := pair_poly_mod_iff_root_residue (k := k) (d := d) (n := X) hd
    have hite :
        (if (X * (k * X + 1)) % d = 0 then 1 else 0) =
          (if X % d ∈ pairRootResidues k d then 1 else 0) :=
      if_congr hP rfl rfl
    rw [hite, hinc]

theorem pairResidueCount_eq_quotient_main_add_remainder
    {k d X : ℕ} (hd : 0 < d) :
    pairResidueCount k d X =
      (pairRootResidues k d).card * (X / d) +
        ((pairRootResidues k d).filter (· < X % d)).card := by
  unfold pairResidueCount
  calc
    (∑ a ∈ pairRootResidues k d, Nat.count (fun n => n ≡ a [MOD d]) X) =
      ∑ a ∈ pairRootResidues k d, (X / d + if a < X % d then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha_lt : a < d := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        rw [Nat.count_modEq_card (b := X) (r := d) (v := a) hd,
          Nat.mod_eq_of_lt ha_lt]
    _ = (pairRootResidues k d).card * (X / d) +
        ((pairRootResidues k d).filter (· < X % d)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_boole]
        simp only [nsmul_eq_mul, Nat.cast_id]

theorem pairResidueCount_remainder_le
    (k d X : ℕ) :
    ((pairRootResidues k d).filter (· < X % d)).card ≤
      (pairRootResidues k d).card := Finset.card_filter_le _ _

theorem pairSiftedCount_eq_quotient_main_add_remainder
    {k d X : ℕ} (hd : 0 < d) :
    pairSiftedCount k d X =
      (pairRootResidues k d).card * (X / d) +
        ((pairRootResidues k d).filter (· < X % d)).card := by
  rw [pairSiftedCount_eq_pairResidueCount hd X,
    pairResidueCount_eq_quotient_main_add_remainder hd]

theorem pairSiftedCount_real_error_le_rootCount
    {k d X : ℕ} (hd : 0 < d) :
    |(pairSiftedCount k d X : ℝ) -
      (pairRootResidues k d).card * (X : ℝ) / (d : ℝ)| ≤
        (pairRootResidues k d).card := by
  let ρ : ℝ := (pairRootResidues k d).card
  let τ : ℝ := ((pairRootResidues k d).filter (· < X % d)).card
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod_lt : ((X % d : ℕ) : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.mod_lt X hd
  have hτ0 : 0 ≤ τ := by positivity
  have hτρ : τ ≤ ρ := by
    dsimp [τ, ρ]
    exact_mod_cast pairResidueCount_remainder_le k d X
  have hfrac0 : 0 ≤ ρ * ((X % d : ℕ) : ℝ) / (d : ℝ) := by positivity
  have hfracρ : ρ * ((X % d : ℕ) : ℝ) / (d : ℝ) ≤ ρ := by
    apply (div_le_iff₀ hdR).2
    calc
      ρ * ((X % d : ℕ) : ℝ) ≤ ρ * (d : ℝ) :=
        mul_le_mul_of_nonneg_left hmod_lt.le (by positivity)
      _ = ρ * (d : ℝ) := rfl
  have hcastdiv : (X : ℝ) = ((X % d : ℕ) : ℝ) +
      (d : ℝ) * ((X / d : ℕ) : ℝ) := by
    have hnat := Nat.mod_add_div X d
    exact_mod_cast hnat.symm
  have hcount : (pairSiftedCount k d X : ℝ) =
      ρ * ((X / d : ℕ) : ℝ) + τ := by
    dsimp [ρ, τ]
    exact_mod_cast pairSiftedCount_eq_quotient_main_add_remainder hd
  have hdiff : (pairSiftedCount k d X : ℝ) -
      (pairRootResidues k d).card * (X : ℝ) / (d : ℝ) =
        τ - ρ * ((X % d : ℕ) : ℝ) / (d : ℝ) := by
    rw [hcount, hcastdiv]
    dsimp [ρ]
    field_simp [hdR.ne']
    ring_nf
  rw [hdiff]
  have hρ : 0 ≤ ρ := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The polynomial whose values are sifted in the linear-prime-pair problem. -/
def pairPoly (k n : ℕ) : ℕ := n * (k * n + 1)

theorem pairPoly_injective (k : ℕ) : Function.Injective (pairPoly k) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab' | hba
  · have h1 : a * (k * a + 1) < b * (k * a + 1) :=
      Nat.mul_lt_mul_of_pos_right hab' (by omega)
    have h2 : b * (k * a + 1) ≤ b * (k * b + 1) := by
      exact Nat.mul_le_mul_left b (by nlinarith)
    dsimp [pairPoly] at hab
    omega
  · have h1 : b * (k * b + 1) < a * (k * b + 1) :=
      Nat.mul_lt_mul_of_pos_right hba (by omega)
    have h2 : a * (k * b + 1) ≤ a * (k * a + 1) := by
      exact Nat.mul_le_mul_left a (by nlinarith)
    dsimp [pairPoly] at hab
    omega

/-- The finite set of polynomial values, suitable as the support of `BoundingSieve`. -/
def pairSupport (k X : ℕ) : Finset ℕ := (Finset.range X).image (pairPoly k)

/-- For unit weights on `pairSupport`, `multSum d` is exactly the divisibility count. -/
theorem pairSupport_divisor_card (k d X : ℕ) :
    ((pairSupport k X).filter (fun y => d ∣ y)).card =
      pairSiftedCount k d X := by
  unfold pairSupport
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ (pairPoly_injective k)]
  simp only [pairSiftedCount, Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp [pairPoly, Nat.dvd_iff_mod_eq_zero]

/-- Bridge to Mathlib's actual `BoundingSieve.multSum`: any instance whose support is
`pairSupport` and whose weights are one has this exact progression-counting remainder. -/
theorem pair_multSum_eq_count (s : BoundingSieve) (k d X : ℕ)
    (hs : s.support = pairSupport k X)
    (hw : ∀ n ∈ pairSupport k X, s.weights n = 1) :
    s.multSum d = (pairSiftedCount k d X : ℝ) := by
  rw [BoundingSieve.multSum, hs]
  have hsum :
      (∑ n ∈ pairSupport k X, if d ∣ n then s.weights n else 0) =
        ∑ n ∈ pairSupport k X, if d ∣ n then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hw n hn]
  rw [hsum, Finset.sum_boole]
  norm_cast
  exact pairSupport_divisor_card k d X

/-- The exact finite-volume estimate supplies the `rem` bound required by the Selberg
upper-bound sieve whenever `nu(d)=rho(d)/d` and `totalMass=X`. -/
theorem pair_sieve_rem_abs_le (s : BoundingSieve) (k d X : ℕ) (hd : 0 < d)
    (hs : s.support = pairSupport k X)
    (hw : ∀ n ∈ pairSupport k X, s.weights n = 1)
    (hmass : s.totalMass = X)
    (hnu : s.nu d = (pairRootResidues k d).card / (d : ℝ)) :
    |s.rem d| ≤ (pairRootResidues k d).card := by
  rw [BoundingSieve.rem, pair_multSum_eq_count s k d X hs hw, hmass, hnu]
  convert pairSiftedCount_real_error_le_rootCount hd using 1 <;> field_simp

/-- Polynomial roots in the finite ring `ZMod d`; this version is convenient for CRT. -/
def pairZModRoots (k d : ℕ) [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter fun x => x * ((k : ZMod d) * x + 1) = 0

theorem pairZModRoots_card_eq_pairRootResidues (k d : ℕ) [NeZero d] :
    (pairZModRoots k d).card = (pairRootResidues k d).card := by
  unfold pairZModRoots pairRootResidues
  -- Both sets are the same residue classes, represented respectively by `ZMod.val`
  -- and by the canonical interval `[0,d)`.
  symm
  apply Finset.card_bij (s := (Finset.range d).filter
    (fun a => (a * (k * a + 1)) % d = 0))
    (t := Finset.univ.filter (fun x : ZMod d => x * ((k : ZMod d) * x + 1) = 0))
    (fun a _ => (a : ZMod d))
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hcast : ((a * (k * a + 1) : ℕ) : ZMod d) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).2
        ((Nat.dvd_iff_mod_eq_zero).2 ha.2)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcast
  · intro a ha b hb hab
    have ha_lt : a < d := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb_lt : b < d := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hv := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] using hv
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨x.val_lt, ?_⟩
      have hcast : ((x.val * (k * x.val + 1) : ℕ) : ZMod d) = 0 := by
        calc
          _ = x * ((k : ZMod d) * x + 1) := by simp
          _ = 0 := hx
      have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hcast
      exact (Nat.dvd_iff_mod_eq_zero).1 hdvd
    · exact ZMod.natCast_zmod_val x

/-- Root subtypes are the most convenient finite objects for the CRT root-count product. -/
abbrev PairZRoot (k d : ℕ) [NeZero d] :=
  {x : ZMod d // x * ((k : ZMod d) * x + 1) = 0}

def pairRootCrtEquiv (k a b : ℕ) (h : a.Coprime b) [NeZero a] [NeZero b] :
    PairZRoot k (a * b) ≃ PairZRoot k a × PairZRoot k b := by
  letI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  let e := ZMod.chineseRemainder h
  have hmap (x : ZMod (a * b)) :
      e (x * ((k : ZMod (a * b)) * x + 1)) =
        e x * ((k : ZMod a × ZMod b) * e x + 1) := by
    simp [e, map_mul, map_add, map_natCast, map_one]
  refine
    { toFun := fun x =>
        ⟨⟨(e x.1).1, ?_⟩, ⟨(e x.1).2, ?_⟩⟩
      invFun := fun y =>
        ⟨e.symm (y.1.1, y.2.1), ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · have hx : e (x.1 * ((k : ZMod (a * b)) * x.1 + 1)) = 0 := by
      rw [x.2, map_zero]
    have hprod : e x.1 * ((k : ZMod a × ZMod b) * e x.1 + 1) = 0 := by
      rw [← hmap, hx]
    simpa using congrArg Prod.fst hprod
  · have hx : e (x.1 * ((k : ZMod (a * b)) * x.1 + 1)) = 0 := by
      rw [x.2, map_zero]
    have hprod : e x.1 * ((k : ZMod a × ZMod b) * e x.1 + 1) = 0 := by
      rw [← hmap, hx]
    simpa using congrArg Prod.snd hprod
  · apply e.map_eq_zero_iff.mp
    rw [hmap]
    apply Prod.ext <;> simp [y.1.2, y.2.2]
  · apply Subtype.ext
    exact e.symm_apply_apply x.1
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (y.1.1, y.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd (e.apply_symm_apply (y.1.1, y.2.1))

theorem pairZRoot_card_mul (k a b : ℕ) (h : a.Coprime b)
    [NeZero a] [NeZero b] :
    Fintype.card (PairZRoot k (a * b)) =
      Fintype.card (PairZRoot k a) * Fintype.card (PairZRoot k b) := by
  rw [Fintype.card_congr (pairRootCrtEquiv k a b h), Fintype.card_prod]

theorem pairZModRoots_card_eq_fintype (k d : ℕ) [NeZero d] :
    (pairZModRoots k d).card = Fintype.card (PairZRoot k d) := by
  classical
  change (Finset.univ.filter (fun x : ZMod d =>
    x * ((k : ZMod d) * x + 1) = 0)).card = _
  rw [Fintype.card_subtype]

set_option linter.style.haveILetI false in
theorem pairRootResidues_card_mul (k a b : ℕ) (h : a.Coprime b)
    [NeZero a] [NeZero b] :
    (pairRootResidues k (a * b)).card =
      (pairRootResidues k a).card * (pairRootResidues k b).card := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  rw [← pairZModRoots_card_eq_pairRootResidues k (a * b),
    pairZModRoots_card_eq_fintype, pairZRoot_card_mul k a b h,
    ← pairZModRoots_card_eq_fintype, pairZModRoots_card_eq_pairRootResidues,
    ← pairZModRoots_card_eq_fintype, pairZModRoots_card_eq_pairRootResidues]

theorem pairRootResidues_card_le (k d : ℕ) :
    (pairRootResidues k d).card ≤ d := by
  unfold pairRootResidues
  calc
    ((Finset.range d).filter (fun a => (a * (k * a + 1)) % d = 0)).card ≤
        (Finset.range d).card := Finset.card_filter_le _ _
    _ = d := Finset.card_range d

theorem pairRootResidues_card_pos {k d : ℕ} (hd : 0 < d) :
    0 < (pairRootResidues k d).card := by
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [pairRootResidues, hd]

set_option linter.style.haveILetI false in
theorem pairRootResidues_prime_card_bounds (k p : ℕ) (hp : p.Prime) :
    0 < (pairRootResidues k p).card ∧ (pairRootResidues k p).card ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← pairZModRoots_card_eq_pairRootResidues]
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    simp [pairZModRoots]
  · let t : Finset (ZMod p) := {0, -((k : ZMod p)⁻¹)}
    have hsub : pairZModRoots k p ⊆ t := by
      intro x hx
      have hxroot : x * ((k : ZMod p) * x + 1) = 0 :=
        (Finset.mem_filter.mp hx).2
      change x ∈ ({0, -((k : ZMod p)⁻¹)} : Finset (ZMod p))
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hxzero : x = 0
      · exact Or.inl hxzero
      · have hroot := mul_eq_zero.mp hxroot
        rcases hroot with h | h
        · exact False.elim (hxzero h)
        · have hk : (k : ZMod p) ≠ 0 := by
            intro hk
            rw [hk, zero_mul, zero_add] at h
            exact one_ne_zero h
          have hlin : (k : ZMod p) * x = -1 := by
            linear_combination h
          have heq : x = -((k : ZMod p)⁻¹) := calc
            x = 1 * x := by simp
            _ = ((k : ZMod p)⁻¹ * (k : ZMod p)) * x := by
              rw [inv_mul_cancel₀ hk]
            _ = (k : ZMod p)⁻¹ * ((k : ZMod p) * x) := by ring
            _ = (k : ZMod p)⁻¹ * (-1) := by rw [hlin]
            _ = -((k : ZMod p)⁻¹) := by ring
          exact Or.inr heq
    calc
      (pairZModRoots k p).card ≤ t.card := Finset.card_le_card hsub
      _ ≤ 2 := by
        rw [show t = insert (0 : ZMod p)
          ({ -((k : ZMod p)⁻¹) } : Finset (ZMod p)) by rfl]
        calc
          (insert (0 : ZMod p)
                ({ -((k : ZMod p)⁻¹) } : Finset (ZMod p))).card ≤
              ({-((k : ZMod p)⁻¹)} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp

set_option linter.style.haveILetI false in
theorem pairRootResidues_two_card_of_even {k : ℕ} (hk : 2 ∣ k) :
    (pairRootResidues k 2).card = 1 := by
  letI : NeZero 2 := ⟨by omega⟩
  have hkz : (k : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hk
  rw [← pairZModRoots_card_eq_pairRootResidues]
  have heq : pairZModRoots k 2 = {0} := by
    ext x
    simp [pairZModRoots, hkz]
  rw [heq, Finset.card_singleton]

theorem pairRootResidues_prime_card_lt_of_even (k p : ℕ) (hk : 2 ∣ k)
    (hp : p.Prime) : (pairRootResidues k p).card < p := by
  by_cases hp2 : p = 2
  · subst p
    rw [pairRootResidues_two_card_of_even hk]
    norm_num
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨_, hcard⟩ := pairRootResidues_prime_card_bounds k p hp
    omega

noncomputable def pairRootDensity (k d : ℕ) : ℝ :=
  (pairRootResidues k d).card / (d : ℝ)

/-- The root density, extended by zero at zero, as a Mathlib arithmetic function. -/
noncomputable def pairSieveNu (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else pairRootDensity k d, by simp⟩

theorem pairSieveNu_prime_pos_lt (k p : ℕ) (hk : 2 ∣ k) (hp : p.Prime) :
    0 < pairSieveNu k p ∧ pairSieveNu k p < 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hρpos := (pairRootResidues_prime_card_bounds k p hp).1
  have hρlt := pairRootResidues_prime_card_lt_of_even k p hk hp
  constructor
  · simp [pairSieveNu, pairRootDensity, hp.ne_zero]
    positivity
  · simp [pairSieveNu, pairRootDensity, hp.ne_zero]
    apply (div_lt_one hpR).2
    exact_mod_cast hρlt

set_option linter.style.haveILetI false in
theorem pairSieveNu_isMultiplicative (k : ℕ) :
    (pairSieveNu k).IsMultiplicative := by
  constructor
  · simp [pairSieveNu, pairRootDensity, pairRootResidues, Nat.mod_one]
  · intro m n h
    by_cases hm : m = 0
    · subst m
      simp [pairSieveNu]
    by_cases hn : n = 0
    · subst n
      simp [pairSieveNu]
    letI : NeZero m := ⟨hm⟩
    letI : NeZero n := ⟨hn⟩
    have hρ := pairRootResidues_card_mul k m n h
    simp [pairSieveNu, hm, hn, Nat.mul_ne_zero hm hn]
    unfold pairRootDensity
    rw [hρ]
    push_cast
    field_simp

/-- Concrete `BoundingSieve` data for the polynomial sequence. The local density hypotheses are
exactly the prime-local conditions required by Mathlib's sieve structure. -/
noncomputable def pairBoundingSieve (k X P : ℕ) (hP : Squarefree P)
    (hpos : ∀ p, p.Prime → p ∣ P → 0 < pairSieveNu k p)
    (hlt : ∀ p, p.Prime → p ∣ P → pairSieveNu k p < 1) : BoundingSieve where
  support := pairSupport k X
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := X
  nu := pairSieveNu k
  nu_mult := pairSieveNu_isMultiplicative k
  nu_pos_of_prime := hpos
  nu_lt_one_of_prime := hlt

noncomputable def pairBoundingSieveEven (k X P : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) : BoundingSieve :=
  pairBoundingSieve k X P hP
    (fun p hp _ => (pairSieveNu_prime_pos_lt k p hk hp).1)
    (fun p hp _ => (pairSieveNu_prime_pos_lt k p hk hp).2)

noncomputable def pairSelbergSieveEven (k X P : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  toBoundingSieve := pairBoundingSieveEven k X P hk hP
  level := y
  one_le_level := hy

theorem primeFactor_set_nonempty_iff {P : ℕ} :
    P.primeFactors.Nonempty ↔ 1 < P := by
  rw [Nat.nonempty_primeFactors]

theorem pairBoundingSieve_rem_abs_le (k X P d : ℕ) (hP : Squarefree P)
    (hpos : ∀ p, p.Prime → p ∣ P → 0 < pairSieveNu k p)
    (hlt : ∀ p, p.Prime → p ∣ P → pairSieveNu k p < 1) (hd : 0 < d) :
    |(pairBoundingSieve k X P hP hpos hlt).rem d| ≤
      (pairRootResidues k d).card := by
  let s := pairBoundingSieve k X P hP hpos hlt
  apply pair_sieve_rem_abs_le s k d X hd
  · rfl
  · intro n hn
    simp [s, pairBoundingSieve]
  · rfl
  · simp [s, pairBoundingSieve, pairSieveNu, pairRootDensity,
      show d ≠ 0 by omega]

theorem pairBoundingSieveEven_rem_abs_le (k X P d : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) (hd : 0 < d) :
    |(pairBoundingSieveEven k X P hk hP).rem d| ≤
      (pairRootResidues k d).card := by
  simpa [pairBoundingSieveEven] using
    pairBoundingSieve_rem_abs_le k X P d hP
      (fun p hp _ => (pairSieveNu_prime_pos_lt k p hk hp).1)
      (fun p hp _ => (pairSieveNu_prime_pos_lt k p hk hp).2) hd

theorem pairSelbergSieveEven_rem_abs_le (k X P d : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) (y : ℝ) (hy : 1 ≤ y) (hd : 0 < d) :
    |(pairSelbergSieveEven k X P hk hP y hy).rem d| ≤
      (pairRootResidues k d).card := by
  exact pairBoundingSieveEven_rem_abs_le k X P d hk hP hd

/-- Generic composition layer: once the Λ² main term is bounded by `1 / den`, the abstract
Mathlib upper sieve immediately gives the requested main term plus its explicit remainder. -/
theorem siftedSum_le_mass_div_den_add_error (s : BoundingSieve) (muPlus : ℕ → ℝ)
    (hμ : BoundingSieve.IsUpperMoebius muPlus) (X den err : ℝ)
    (hX : 0 ≤ X)
    (hmass : s.totalMass = X) (hmain : s.mainSum muPlus ≤ den⁻¹)
    (herr : s.errSum muPlus ≤ err) :
    s.siftedSum ≤ X / den + err := by
  have hmass_nonneg : 0 ≤ s.totalMass := by rw [hmass]; exact hX
  calc
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius muPlus hμ
    _ ≤ s.totalMass * den⁻¹ + err :=
      add_le_add (mul_le_mul_of_nonneg_left hmain hmass_nonneg) herr
    _ = (X : ℝ) / den + err := by rw [hmass]; ring

/-- The finite Selberg denominator at square-support cutoff `y`. -/
noncomputable def pairSelbergDen (s : BoundingSieve) (y : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors s.prodPrimes, if d ≤ y then s.selbergTerms d else 0

theorem pairSelbergDen_pos (s : BoundingSieve) (y : ℕ) (hy : 1 ≤ y) :
    0 < pairSelbergDen s y := by
  have h1 : 1 ∈ Nat.divisors s.prodPrimes := by
    simp [Nat.mem_divisors, s.prodPrimes_ne_zero]
  have hnonneg : ∀ d ∈ Nat.divisors s.prodPrimes,
      0 ≤ if d ≤ y then s.selbergTerms d else 0 := by
    intro d hd
    split_ifs
    · exact le_of_lt (s.selbergTerms_pos (Nat.mem_divisors.mp hd).1)
    · exact le_rfl
  have hsum := Finset.single_le_sum hnonneg h1
  have hterm : 0 < s.selbergTerms 1 := s.selbergTerms_pos (Nat.one_dvd _)
  have hle : s.selbergTerms 1 ≤ pairSelbergDen s y := by
    simpa [pairSelbergDen, show 1 ≤ y from hy] using hsum
  exact lt_of_lt_of_le hterm hle

theorem pairSelbergTerm_le_den (s : BoundingSieve) (y l : ℕ)
    (hl : l ∣ s.prodPrimes) (hly : l ≤ y) :
    s.selbergTerms l ≤ pairSelbergDen s y := by
  have hmem : l ∈ Nat.divisors s.prodPrimes :=
    Nat.mem_divisors.mpr ⟨hl, s.prodPrimes_ne_zero⟩
  have hnonneg : ∀ d ∈ Nat.divisors s.prodPrimes,
      0 ≤ if d ≤ y then s.selbergTerms d else 0 := by
    intro d hd
    split_ifs
    · exact le_of_lt (s.selbergTerms_pos (Nat.mem_divisors.mp hd).1)
    · exact le_rfl
  have hsum := Finset.single_le_sum hnonneg hmem
  simpa [pairSelbergDen, hly] using hsum

/-- Desired diagonal value, indexed by the complementary divisor of `P`. -/
noncomputable def pairTargetComplement (s : BoundingSieve) (y n : ℕ) : ℝ :=
  if n ∣ s.prodPrimes ∧ s.prodPrimes / n ≤ y then
    (ArithmeticFunction.moebius (s.prodPrimes / n) : ℝ) *
      s.selbergTerms (s.prodPrimes / n) /
      pairSelbergDen s y
  else 0

theorem pairTargetComplement_abs_le_one (s : BoundingSieve) (y n : ℕ)
    (hy : 1 ≤ y) : |pairTargetComplement s y n| ≤ 1 := by
  by_cases hcond : n ∣ s.prodPrimes ∧ s.prodPrimes / n ≤ y
  · have hl : s.prodPrimes / n ∣ s.prodPrimes := Nat.div_dvd_of_dvd hcond.1
    have hsq : Squarefree (s.prodPrimes / n) :=
      Squarefree.squarefree_of_dvd hl s.prodPrimes_squarefree
    have hg : 0 < s.selbergTerms (s.prodPrimes / n) := s.selbergTerms_pos hl
    have hden : 0 < pairSelbergDen s y := pairSelbergDen_pos s y hy
    have hμ : |(ArithmeticFunction.moebius (s.prodPrimes / n) : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq
    rw [pairTargetComplement, if_pos hcond, abs_div, abs_mul,
      hμ, abs_of_pos hg, abs_of_pos hden, one_mul]
    exact (div_le_one hden).2
      (pairSelbergTerm_le_den s y (s.prodPrimes / n) hl hcond.2)
  · simp [pairTargetComplement, hcond]

theorem pair_complement_mul {P d a : ℕ} (hP : P ≠ 0)
    (hd : d ∣ P) (ha : a ∣ P / d) :
    P / (P / d / a) = d * a := by
  have hPpos : 0 < P := Nat.pos_of_ne_zero hP
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hPpos
  have hnpos : 0 < P / d :=
    Nat.div_pos (Nat.le_of_dvd hPpos hd) hdpos
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hnpos
  have hqpos : 0 < P / d / a :=
    Nat.div_pos (Nat.le_of_dvd hnpos ha) hapos
  have hmulD := Nat.div_mul_cancel hd
  have hmulA := Nat.div_mul_cancel ha
  have hprod : P = (P / d / a) * (d * a) := by
    calc
      P = (P / d) * d := by rw [hmulD]
      _ = ((P / d / a) * a) * d := by rw [hmulA]
      _ = (P / d / a) * (d * a) := by ring
  have hnum := congrArg (fun z : ℕ => z / (P / d / a)) hprod
  calc
    P / (P / d / a) = ((P / d / a) * (d * a)) / (P / d / a) := hnum
    _ = d * a := Nat.mul_div_cancel_left (d * a) hqpos

/-- Möbius-inverted coefficient on the complementary divisor lattice. -/
noncomputable def pairInvertedCoefficient (s : BoundingSieve) (y n : ℕ) : ℝ :=
  ∑ x ∈ Nat.divisorsAntidiagonal n,
    (ArithmeticFunction.moebius x.1 : ℝ) * pairTargetComplement s y x.2

theorem pairInvertedCoefficient_divisor_sum (s : BoundingSieve) (y n : ℕ)
    (hn : 0 < n) :
    (∑ d ∈ Nat.divisors n, pairInvertedCoefficient s y d) =
      pairTargetComplement s y n := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := pairInvertedCoefficient s y) (g := pairTargetComplement s y)).mpr
      (by intro m hm; simp [pairInvertedCoefficient]) n hn

theorem sum_divisors_multiples_via_complement {P l : ℕ} (hP : P ≠ 0)
    (hl : l ∣ P) (f : ℕ → ℝ) :
    (∑ d ∈ Nat.divisors P, if l ∣ d then f (P / d) else 0) =
      ∑ e ∈ Nat.divisors (P / l), f e := by
  let g : ℕ → ℝ := fun e => if l ∣ P / e then f e else 0
  calc
    (∑ d ∈ Nat.divisors P, if l ∣ d then f (P / d) else 0) =
        ∑ d ∈ Nat.divisors P, g (P / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := (Nat.mem_divisors.mp hd).1
      have hcomp : P / (P / d) = d := by
        have hmul := Nat.div_mul_cancel hdP
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdP (Nat.pos_of_ne_zero hP)
        have hqd : 0 < P / d := by
          apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hdP)
          exact hdpos
        calc
          P / (P / d) = ((P / d) * d) / (P / d) := by rw [hmul]
          _ = d := Nat.mul_div_cancel_left d hqd
      simp [g, hcomp]
    _ = ∑ d ∈ Nat.divisors P, g d := Nat.sum_div_divisors P g
    _ = ∑ e ∈ Nat.divisors (P / l), f e := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Nat.divisors P).filter (fun e => l ∣ P / e) = Nat.divisors (P / l) := by
        ext e
        simp only [Finset.mem_filter, Nat.mem_divisors]
        have hquot : P / l ≠ 0 := by
          intro hzero
          have hmul := Nat.div_mul_cancel hl
          simp [hzero] at hmul
          exact hP hmul.symm
        constructor
        · rintro ⟨⟨heP, _⟩, hle⟩
          refine ⟨(Nat.dvd_div_iff_mul_dvd hl).2 ?_, hquot⟩
          · have := (Nat.dvd_div_iff_mul_dvd heP).1 hle
            simpa [Nat.mul_comm] using this
        · rintro ⟨he, he0⟩
          refine ⟨⟨(he.trans (Nat.div_dvd_of_dvd hl)), hP⟩, ?_⟩
          apply (Nat.dvd_div_iff_mul_dvd (he.trans (Nat.div_dvd_of_dvd hl))).2
          simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hl).1 he
      rw [hfilter]

noncomputable def pairSelbergWeight (s : BoundingSieve) (y d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    pairInvertedCoefficient s y (s.prodPrimes / d) / s.nu d
  else 0

theorem pairSelbergWeight_cancel (s : BoundingSieve) (y d : ℕ)
    (hd : d ∣ s.prodPrimes) :
    s.nu d * pairSelbergWeight s y d =
      pairInvertedCoefficient s y (s.prodPrimes / d) := by
  rw [pairSelbergWeight, if_pos hd]
  field_simp [s.nu_ne_zero hd]

theorem pairSelbergWeight_diagonal (s : BoundingSieve) (y l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ Nat.divisors s.prodPrimes,
      if l ∣ d then s.nu d * pairSelbergWeight s y d else 0) =
        pairTargetComplement s y (s.prodPrimes / l) := by
  have hP := s.prodPrimes_ne_zero
  have hquotpos : 0 < s.prodPrimes / l := by
    apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    exact Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP)
  calc
    _ = ∑ d ∈ Nat.divisors s.prodPrimes,
        if l ∣ d then pairInvertedCoefficient s y (s.prodPrimes / d) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs with hld
      · exact pairSelbergWeight_cancel s y d ((Nat.mem_divisors.mp hd).1)
      · rfl
    _ = ∑ e ∈ Nat.divisors (s.prodPrimes / l),
        pairInvertedCoefficient s y e :=
      sum_divisors_multiples_via_complement hP hl (pairInvertedCoefficient s y)
    _ = pairTargetComplement s y (s.prodPrimes / l) :=
      pairInvertedCoefficient_divisor_sum s y _ hquotpos

theorem pairTargetComplement_div_complement (s : BoundingSieve) (y l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    pairTargetComplement s y (s.prodPrimes / l) =
      if l ≤ y then
        (ArithmeticFunction.moebius l : ℝ) * s.selbergTerms l /
          pairSelbergDen s y
      else 0 := by
  have hP := s.prodPrimes_ne_zero
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP)
  have hquotpos : 0 < s.prodPrimes / l := by
    apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    exact hlpos
  have hmul := Nat.div_mul_cancel hl
  have hcompl : s.prodPrimes / (s.prodPrimes / l) = l := by
    calc
      s.prodPrimes / (s.prodPrimes / l) =
          ((s.prodPrimes / l) * l) / (s.prodPrimes / l) := by rw [hmul]
      _ = l := Nat.mul_div_cancel_left l hquotpos
  simp [pairTargetComplement, Nat.div_dvd_of_dvd hl, hcompl]

theorem pairInvertedTerm_abs_le_cutoff (s : BoundingSieve) (y d a : ℕ)
    (hy : 1 ≤ y) (hd : d ∣ s.prodPrimes)
    (ha : a ∣ s.prodPrimes / d) :
    |(ArithmeticFunction.moebius a : ℝ) *
        pairTargetComplement s y (s.prodPrimes / d / a)| ≤
      if a ≤ y then 1 else 0 := by
  have hP := s.prodPrimes_ne_zero
  have hla : d * a ∣ s.prodPrimes := by
    refine ⟨s.prodPrimes / d / a, ?_⟩
    have hdivA := Nat.div_mul_cancel ha
    have hdivD := Nat.div_mul_cancel hd
    calc
      s.prodPrimes = (s.prodPrimes / d) * d := by rw [hdivD]
      _ = ((s.prodPrimes / d / a) * a) * d := by rw [hdivA]
      _ = (d * a) * (s.prodPrimes / d / a) := by ring
  have htarget : pairTargetComplement s y (s.prodPrimes / d / a) =
      if d * a ≤ y then
        (ArithmeticFunction.moebius (d * a) : ℝ) *
          s.selbergTerms (d * a) / pairSelbergDen s y
      else 0 := by
    rw [Nat.div_div_eq_div_mul]
    exact pairTargetComplement_div_complement s y (d * a) hla
  rw [htarget]
  by_cases haY : a ≤ y
  · by_cases hdaY : d * a ≤ y
    · have hμa : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have htarget1 : |((ArithmeticFunction.moebius (d * a) : ℝ) *
          s.selbergTerms (d * a) / pairSelbergDen s y)| ≤ 1 := by
        have hbound := pairTargetComplement_abs_le_one s y
          (s.prodPrimes / (d * a)) hy
        rw [pairTargetComplement_div_complement s y (d * a) hla] at hbound
        simpa [hdaY] using hbound
      simp only [if_pos hdaY, if_pos haY]
      calc
        |(ArithmeticFunction.moebius a : ℝ) *
            ((ArithmeticFunction.moebius (d * a) : ℝ) *
              s.selbergTerms (d * a) / pairSelbergDen s y)| =
            |(ArithmeticFunction.moebius a : ℝ)| *
              |((ArithmeticFunction.moebius (d * a) : ℝ) *
                s.selbergTerms (d * a) / pairSelbergDen s y)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hμa htarget1 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    · simp [haY, hdaY]
  · have hdaY : ¬ d * a ≤ y := by
      intro h
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hP)
      have : a ≤ y := by nlinarith
      exact haY this
    simp [haY, hdaY]

theorem pairInvertedCoefficient_abs_le_cutoff (s : BoundingSieve) (y d : ℕ)
    (hy : 1 ≤ y) (hd : d ∣ s.prodPrimes) :
    |pairInvertedCoefficient s y (s.prodPrimes / d)| ≤ (y : ℝ) + 1 := by
  let n := s.prodPrimes / d
  have hsum : pairInvertedCoefficient s y n =
      ∑ a ∈ Nat.divisors n,
        (ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y (n / a) := by
    rw [pairInvertedCoefficient,
      Nat.sum_divisorsAntidiagonal
        (fun a b => (ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y b)]
  rw [show s.prodPrimes / d = n from rfl, hsum]
  calc
    |∑ a ∈ Nat.divisors n,
        (ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y (n / a)| ≤
      ∑ a ∈ Nat.divisors n,
        |(ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y (n / a)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Nat.divisors n, if a ≤ y then 1 else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ∣ s.prodPrimes / d := by simpa [n] using (Nat.mem_divisors.mp ha).1
      simpa [n] using pairInvertedTerm_abs_le_cutoff s y d a hy hd ha'
    _ ≤ (y : ℝ) + 1 := by
      have hsumcard :
          (∑ a ∈ Nat.divisors n, if a ≤ y then (1 : ℝ) else 0) =
            ((Nat.divisors n).filter (· ≤ y)).card := by
        simp [Finset.sum_boole]
      rw [hsumcard]
      have hsub : (Nat.divisors n).filter (· ≤ y) ⊆ Finset.range (y + 1) := by
        intro a ha
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.mem_filter.mp ha).2
      calc
        (((Nat.divisors n).filter (· ≤ y)).card : ℝ) ≤
            (Finset.range (y + 1)).card := by exact_mod_cast Finset.card_le_card hsub
        _ = (y : ℝ) + 1 := by simp

theorem pairInvertedCoefficient_eq_zero_of_gt (s : BoundingSieve) (y d : ℕ)
    (hdy : y < d) (hd : d ∣ s.prodPrimes) :
    pairInvertedCoefficient s y (s.prodPrimes / d) = 0 := by
  let n := s.prodPrimes / d
  have hnpos : 0 < n := by
    apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hd)
    exact Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
  have hsum : pairInvertedCoefficient s y n =
      ∑ a ∈ Nat.divisors n,
        (ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y (n / a) := by
    rw [pairInvertedCoefficient,
      Nat.sum_divisorsAntidiagonal
        (fun a b => (ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y b)]
  rw [show s.prodPrimes / d = n from rfl, hsum]
  apply Finset.sum_eq_zero
  intro a ha
  have haDiv : a ∣ s.prodPrimes / d := by simpa [n] using (Nat.mem_divisors.mp ha).1
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos haDiv hnpos
  have hla : d * a ∣ s.prodPrimes := by
    refine ⟨s.prodPrimes / d / a, ?_⟩
    have hdivA := Nat.div_mul_cancel haDiv
    have hdivD := Nat.div_mul_cancel hd
    calc
      s.prodPrimes = (s.prodPrimes / d) * d := by rw [hdivD]
      _ = ((s.prodPrimes / d / a) * a) * d := by rw [hdivA]
      _ = (d * a) * (s.prodPrimes / d / a) := by ring
  have htarget : pairTargetComplement s y (n / a) = 0 := by
    dsimp [n]
    rw [Nat.div_div_eq_div_mul,
      pairTargetComplement_div_complement s y (d * a) hla]
    have hnot : ¬d * a ≤ y := by nlinarith
    simp [hnot]
  simp [htarget]

theorem pairSelbergWeight_eq_zero_of_gt (s : BoundingSieve) (y d : ℕ)
    (hdy : y < d) (hd : d ∣ s.prodPrimes) : pairSelbergWeight s y d = 0 := by
  rw [pairSelbergWeight, if_pos hd,
    pairInvertedCoefficient_eq_zero_of_gt s y d hdy hd]
  simp

theorem pairSieveNu_ge_inv (k d : ℕ) (hd : 0 < d) :
    (1 : ℝ) / d ≤ pairSieveNu k d := by
  have hρ := pairRootResidues_card_pos (k := k) hd
  have hρ' : (1 : ℝ) ≤ (pairRootResidues k d).card := by
    exact_mod_cast Nat.succ_le_of_lt hρ
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp [pairSieveNu, pairRootDensity, Nat.ne_of_gt hd]
  simpa [one_div] using (div_le_div_iff_of_pos_right hdR).2 hρ'

theorem pairSelbergWeight_abs_le (s : BoundingSieve) (k y d : ℕ)
    (hy : 1 ≤ y) (hd : d ∣ s.prodPrimes) (hdpos : 0 < d)
    (hνeq : s.nu = pairSieveNu k) :
    |pairSelbergWeight s y d| ≤ (d : ℝ) * ((y : ℝ) + 1) := by
  have hν := s.nu_pos_of_dvd_prodPrimes hd
  have hνlower := pairSieveNu_ge_inv k d hdpos
  rw [← hνeq] at hνlower
  have hcoeff := pairInvertedCoefficient_abs_le_cutoff s y d hy hd
  rw [pairSelbergWeight, if_pos hd, abs_div, abs_of_pos hν]
  apply (div_le_iff₀ hν).2
  calc
    |pairInvertedCoefficient s y (s.prodPrimes / d)| ≤ (y : ℝ) + 1 := hcoeff
    _ ≤ ((y : ℝ) + 1) * ((d : ℝ) * s.nu d) := by
      have hprod : (1 : ℝ) ≤ (d : ℝ) * s.nu d := by
        calc
          1 = (1 / (d : ℝ)) * d := by
            have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
            field_simp [ne_of_gt hdR]
          _ ≤ s.nu d * d := mul_le_mul_of_nonneg_right hνlower (by positivity)
          _ = (d : ℝ) * s.nu d := by ring
      calc
        (y : ℝ) + 1 = ((y : ℝ) + 1) * 1 := by ring
        _ ≤ ((y : ℝ) + 1) * ((d : ℝ) * s.nu d) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((d : ℝ) * ((y : ℝ) + 1)) * s.nu d := by ring

theorem pairSelbergWeight_abs_le_global (s : BoundingSieve) (k y d : ℕ)
    (hy : 1 ≤ y) (hdpos : 0 < d) (hνeq : s.nu = pairSieveNu k) :
    |pairSelbergWeight s y d| ≤ (y : ℝ) * ((y : ℝ) + 1) := by
  by_cases hd : d ∣ s.prodPrimes
  · by_cases hdy : d ≤ y
    · have hlocal := pairSelbergWeight_abs_le s k y d hy hd hdpos hνeq
      have hdyR : (d : ℝ) ≤ y := by exact_mod_cast hdy
      calc
        |pairSelbergWeight s y d| ≤ (d : ℝ) * ((y : ℝ) + 1) := hlocal
        _ ≤ (y : ℝ) * ((y : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hdyR (by positivity)
    · rw [pairSelbergWeight_eq_zero_of_gt s y d (Nat.lt_of_not_ge hdy) hd]
      simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ (y : ℝ))
        (by positivity : (0 : ℝ) ≤ (y : ℝ) + 1)
  · simp [pairSelbergWeight, hd]
    positivity

theorem pairLambdaSquared_zero_of_gt (s : BoundingSieve) (y d : ℕ)
    (hdy : y * y < d) (hP : d ∣ s.prodPrimes) :
    BoundingSieve.lambdaSquared (pairSelbergWeight s y) d = 0 := by
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro d1 hd1
  apply Finset.sum_eq_zero
  intro d2 hd2
  by_cases heq : d = Nat.lcm d1 d2
  · rw [if_pos heq]
    have hd1P : d1 ∣ s.prodPrimes := (Nat.mem_divisors.mp hd1).1.trans hP
    have hd2P : d2 ∣ s.prodPrimes := (Nat.mem_divisors.mp hd2).1.trans hP
    by_cases h1 : d1 ≤ y
    · by_cases h2 : d2 ≤ y
      · have hpos1 : 0 < d1 := Nat.pos_of_dvd_of_pos hd1P
          (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
        have hpos2 : 0 < d2 := Nat.pos_of_dvd_of_pos hd2P
          (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
        have hlcm : Nat.lcm d1 d2 ≤ d1 * d2 :=
          Nat.le_of_dvd (Nat.mul_pos hpos1 hpos2) (Nat.lcm_dvd_mul d1 d2)
        have hy1 : d1 ≤ y := h1
        have hy2 : d2 ≤ y := h2
        nlinarith [hlcm]
      · rw [pairSelbergWeight_eq_zero_of_gt s y d2 (Nat.lt_of_not_ge h2) hd2P]
        simp
    · rw [pairSelbergWeight_eq_zero_of_gt s y d1 (Nat.lt_of_not_ge h1) hd1P]
      simp
  · simp [heq]

theorem pairLambdaSquared_abs_le (s : BoundingSieve) (k y d : ℕ)
    (hy : 1 ≤ y) (hd : d ∣ s.prodPrimes) (hνeq : s.nu = pairSieveNu k) :
    |BoundingSieve.lambdaSquared (pairSelbergWeight s y) d| ≤
      ((d : ℝ) + 1) ^ 2 * ((y : ℝ) * ((y : ℝ) + 1)) ^ 2 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd
    (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
  have hdivcard : (Nat.divisors d).card ≤ d + 1 := by
    have hsub : Nat.divisors d ⊆ Finset.range (d + 1) := by
      intro a ha
      have hadvd := (Nat.mem_divisors.mp ha).1
      have hle := Nat.le_of_dvd hdpos hadvd
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
    calc
      (Nat.divisors d).card ≤ (Finset.range (d + 1)).card := Finset.card_le_card hsub
      _ = d + 1 := by simp
  let C : ℝ := (y : ℝ) * ((y : ℝ) + 1)
  have hC : 0 ≤ C := by positivity
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ d1 ∈ Nat.divisors d,
        ∑ d2 ∈ Nat.divisors d,
          if d = Nat.lcm d1 d2 then
            pairSelbergWeight s y d1 * pairSelbergWeight s y d2 else 0| ≤
      ∑ d1 ∈ Nat.divisors d,
        |∑ d2 ∈ Nat.divisors d,
          if d = Nat.lcm d1 d2 then
            pairSelbergWeight s y d1 * pairSelbergWeight s y d2 else 0| :=
              Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ Nat.divisors d, (Nat.divisors d).card * C ^ 2 := by
      apply Finset.sum_le_sum
      intro d1 hd1
      calc
        |∑ d2 ∈ Nat.divisors d,
            if d = Nat.lcm d1 d2 then
              pairSelbergWeight s y d1 * pairSelbergWeight s y d2 else 0| ≤
          ∑ d2 ∈ Nat.divisors d,
            |if d = Nat.lcm d1 d2 then
              pairSelbergWeight s y d1 * pairSelbergWeight s y d2 else 0| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d2 ∈ Nat.divisors d, C ^ 2 := by
          apply Finset.sum_le_sum
          intro d2 hd2
          by_cases heq : d = Nat.lcm d1 d2
          · simp only [if_pos heq, abs_mul]
            have hd1P : d1 ∣ s.prodPrimes :=
              (Nat.mem_divisors.mp hd1).1.trans hd
            have hd2P : d2 ∣ s.prodPrimes :=
              (Nat.mem_divisors.mp hd2).1.trans hd
            have hd1pos : 0 < d1 := Nat.pos_of_dvd_of_pos hd1P
              (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
            have hd2pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2P
              (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
            have hw1 := pairSelbergWeight_abs_le_global s k y d1 hy hd1pos hνeq
            have hw2 := pairSelbergWeight_abs_le_global s k y d2 hy hd2pos hνeq
            calc
              |pairSelbergWeight s y d1| * |pairSelbergWeight s y d2| ≤
                  (y : ℝ) * ((y : ℝ) + 1) * ((y : ℝ) * ((y : ℝ) + 1)) :=
                mul_le_mul hw1 hw2 (abs_nonneg _) (by positivity)
              _ = C ^ 2 := by dsimp [C]; ring
          · simp [heq, C]; positivity
        _ = ((Nat.divisors d).card : ℝ) * C ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ((Nat.divisors d).card : ℝ) *
        ((Nat.divisors d).card : ℝ) * C ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ((d : ℝ) + 1) ^ 2 * C ^ 2 := by
      have hcardR : (Nat.divisors d).card ≤ (d : ℝ) + 1 := by exact_mod_cast hdivcard
      have hcard0 : (0 : ℝ) ≤ (Nat.divisors d).card := by positivity
      have hsum : ((Nat.divisors d).card : ℝ) * (Nat.divisors d).card ≤
          ((d : ℝ) + 1) * ((d : ℝ) + 1) :=
        mul_le_mul hcardR hcardR hcard0 (by positivity)
      calc
        (Nat.divisors d).card * (Nat.divisors d).card * C ^ 2 ≤
            ((d : ℝ) + 1) * ((d : ℝ) + 1) * C ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg C)
        _ = ((d : ℝ) + 1) ^ 2 * C ^ 2 := by ring
    _ = ((d : ℝ) + 1) ^ 2 * ((y : ℝ) * ((y : ℝ) + 1)) ^ 2 := by rfl

theorem pairInvertedCoefficient_prod_eq_one (s : BoundingSieve) (y : ℕ)
    (hy : 1 ≤ y) : pairInvertedCoefficient s y s.prodPrimes = 1 := by
  have hP := s.prodPrimes_ne_zero
  have hden := pairSelbergDen_pos s y hy
  rw [pairInvertedCoefficient]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * pairTargetComplement s y b)
    (n := s.prodPrimes)]
  calc
    (∑ a ∈ Nat.divisors s.prodPrimes,
      (ArithmeticFunction.moebius a : ℝ) *
        pairTargetComplement s y (s.prodPrimes / a)) =
      ∑ a ∈ Nat.divisors s.prodPrimes,
        if a ≤ y then s.selbergTerms a / pairSelbergDen s y else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have haP := (Nat.mem_divisors.mp ha).1
      have hsq : Squarefree a := Squarefree.squarefree_of_dvd haP s.prodPrimes_squarefree
      rw [pairTargetComplement_div_complement s y a haP]
      split_ifs with hay
      · have hμ : (ArithmeticFunction.moebius a : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        calc
          (ArithmeticFunction.moebius a : ℝ) *
              ((ArithmeticFunction.moebius a : ℝ) * s.selbergTerms a /
                pairSelbergDen s y) =
              (ArithmeticFunction.moebius a : ℝ) ^ 2 *
                (s.selbergTerms a / pairSelbergDen s y) := by ring
          _ = s.selbergTerms a / pairSelbergDen s y := by rw [hμ, one_mul]
      · simp
    _ = pairSelbergDen s y / pairSelbergDen s y := by
      rw [pairSelbergDen]
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
      congr 1
      ext a
      by_cases ha : a ≤ y <;> simp [ha]
    _ = 1 := div_self (ne_of_gt hden)

theorem sum_cutoff_div_constant (T : Finset ℕ) (y : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (∑ d ∈ T, if d ≤ y then f d / c else 0) =
      (∑ d ∈ T, if d ≤ y then f d else 0) / c := by
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  congr 1
  ext d
  by_cases hd : d ≤ y <;> simp [hd]

theorem pairSelbergWeight_one (s : BoundingSieve) (y : ℕ)
    (hy : 1 ≤ y) : pairSelbergWeight s y 1 = 1 := by
  have hden := pairSelbergDen_pos s y hy
  have hcoeff := pairInvertedCoefficient_prod_eq_one s y hy
  have hnu1 : s.nu 1 = 1 := s.nu_mult.map_one
  simp [pairSelbergWeight, hnu1, hcoeff]

noncomputable def pairSelbergMuPlus (s : BoundingSieve) (y : ℕ) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (pairSelbergWeight s y)

theorem pairSelbergMuPlus_upper (s : BoundingSieve) (y : ℕ) (hy : 1 ≤ y) :
    BoundingSieve.IsUpperMoebius (pairSelbergMuPlus s y) := by
  unfold pairSelbergMuPlus
  apply BoundingSieve.upperMoebius_lambdaSquared
  exact pairSelbergWeight_one s y hy

theorem pairSelberg_main_eq_inverse (s : BoundingSieve) (y : ℕ)
    (hy : 1 ≤ y) :
    s.mainSum (pairSelbergMuPlus s y) = (pairSelbergDen s y)⁻¹ := by
  have hden := pairSelbergDen_pos s y hy
  rw [pairSelbergMuPlus,
    s.mainSum_lambdaSquared_eq_sum_mul_sum_sq (pairSelbergWeight s y)]
  calc
    (∑ l ∈ Nat.divisors s.prodPrimes,
      (s.selbergTerms l)⁻¹ *
        (∑ d ∈ Nat.divisors s.prodPrimes,
          if l ∣ d then s.nu d * pairSelbergWeight s y d else 0) ^ 2) =
      ∑ l ∈ Nat.divisors s.prodPrimes,
        if l ≤ y then s.selbergTerms l / (pairSelbergDen s y) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlP := (Nat.mem_divisors.mp hl).1
      have hsq : Squarefree l :=
        Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree
      rw [pairSelbergWeight_diagonal s y l hlP,
        pairTargetComplement_div_complement s y l hlP]
      split_ifs with hly
      · have hμ : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        rw [div_pow, mul_pow, hμ]
        have hg : 0 < s.selbergTerms l := s.selbergTerms_pos hlP
        field_simp [ne_of_gt hden, ne_of_gt hg]
      · simp
    _ = pairSelbergDen s y / (pairSelbergDen s y) ^ 2 := by
      rw [sum_cutoff_div_constant, pairSelbergDen]
    _ = (pairSelbergDen s y)⁻¹ := by
      field_simp [ne_of_gt hden]

theorem pairSelberg_errSum_le_root_weighted (k X P y : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) :
    (pairBoundingSieveEven k X P hk hP).errSum
        (pairSelbergMuPlus (pairBoundingSieveEven k X P hk hP) y) ≤
      ∑ d ∈ Nat.divisors P,
        |pairSelbergMuPlus (pairBoundingSieveEven k X P hk hP) y d| *
          (pairRootResidues k d).card := by
  rw [BoundingSieve.errSum]
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (pairBoundingSieveEven_rem_abs_le k X P d hk hP
      (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1
        (Nat.pos_of_ne_zero (pairBoundingSieveEven k X P hk hP).prodPrimes_ne_zero)))
    (abs_nonneg _)

theorem pairSelbergEven_sifted_bound (k X P y : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) (hy : 1 ≤ y) :
    (pairBoundingSieveEven k (X + 1) P hk hP).siftedSum ≤
      ((X + 1 : ℕ) : ℝ) /
        pairSelbergDen (pairBoundingSieveEven k (X + 1) P hk hP) y +
      (pairBoundingSieveEven k (X + 1) P hk hP).errSum
        (pairSelbergMuPlus
          (pairBoundingSieveEven k (X + 1) P hk hP) y) := by
  let s := pairBoundingSieveEven k (X + 1) P hk hP
  have hbound := siftedSum_le_mass_div_den_add_error s (pairSelbergMuPlus s y)
    (pairSelbergMuPlus_upper s y hy) (X + 1 : ℝ) (pairSelbergDen s y)
    (s.errSum (pairSelbergMuPlus s y)) (by exact_mod_cast Nat.zero_le (X + 1))
    (by simp [s, pairBoundingSieveEven, pairBoundingSieve, Nat.cast_add])
    (by rw [pairSelberg_main_eq_inverse s y hy]) le_rfl
  simpa [s, Nat.cast_add] using hbound

theorem pairSelbergEven_errSum_explicit (k X P y : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) (hy : 1 ≤ y) :
    (pairBoundingSieveEven k X P hk hP).errSum
        (pairSelbergMuPlus (pairBoundingSieveEven k X P hk hP) y) ≤
      ((y * y + 1 : ℕ) : ℝ) ^ 3 *
        ((y : ℝ) * ((y : ℝ) + 1)) ^ 2 * (y * y : ℝ) := by
  let s := pairBoundingSieveEven k X P hk hP
  let C : ℝ := (y : ℝ) * ((y : ℝ) + 1)
  have hC : 0 ≤ C := by positivity
  have hν : s.nu = pairSieveNu k := by rfl
  have hroot := pairSelberg_errSum_le_root_weighted k X P y hk hP
  calc
    s.errSum (pairSelbergMuPlus s y) ≤
      ∑ d ∈ Nat.divisors P,
        |pairSelbergMuPlus s y d| * (pairRootResidues k d).card := by
          simpa [s] using hroot
    _ ≤
      ∑ d ∈ Nat.divisors P,
        if d ≤ y * y then ((y * y : ℕ) : ℝ) *
          ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        by_cases hdy : d ≤ y * y
        · rw [if_pos hdy]
          have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
          have hrho : ((pairRootResidues k d).card : ℝ) ≤ d := by
            have hsub : pairRootResidues k d ⊆ Finset.range d := by
              intro a ha
              exact (Finset.mem_filter.mp ha).1
            calc
              ((pairRootResidues k d).card : ℝ) ≤ (Finset.range d).card := by
                exact_mod_cast Finset.card_le_card hsub
              _ = d := by simp
          have hLam := pairLambdaSquared_abs_le s k y d hy hdP hν
          have hdyR : (d : ℝ) ≤ (y * y : ℝ) := by exact_mod_cast hdy
          have hdp1R : (d : ℝ) + 1 ≤ (y * y + 1 : ℕ) := by
            exact_mod_cast Nat.add_le_add_right hdy 1
          have hρR : ((pairRootResidues k d).card : ℝ) ≤ (y * y : ℝ) :=
            hrho.trans hdyR
          have hLamR : |pairSelbergMuPlus s y d| ≤
              ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 := by
            have hpow : ((d : ℝ) + 1) ^ 2 ≤
                ((y * y + 1 : ℕ) : ℝ) ^ 2 := by
              nlinarith [hdp1R]
            calc
              |pairSelbergMuPlus s y d| ≤ ((d : ℝ) + 1) ^ 2 * C ^ 2 := by
                simpa [pairSelbergMuPlus, C] using hLam
              _ ≤ ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 :=
                mul_le_mul_of_nonneg_right hpow (sq_nonneg C)
          have hprod := mul_le_mul hLamR hρR
            (by positivity : 0 ≤ ((pairRootResidues k d).card : ℝ))
            (mul_nonneg (sq_nonneg ((y * y + 1 : ℕ) : ℝ)) (sq_nonneg C))
          convert hprod using 1
          all_goals push_cast
          all_goals ring
        · rw [if_neg hdy]
          have hzero := pairLambdaSquared_zero_of_gt s y d
            (Nat.lt_of_not_ge hdy) ((Nat.mem_divisors.mp hd).1)
          simp [pairSelbergMuPlus, hzero]
    _ ≤ ((y * y + 1 : ℕ) : ℝ) *
        (((y * y : ℕ) : ℝ) * ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2) := by
          have hcard : (Nat.divisors P |>.filter fun d => d ≤ y * y).card ≤ y * y + 1 := by
            have hsub : (Nat.divisors P).filter (fun d => d ≤ y * y) ⊆
                Finset.range (y * y + 1) := by
              intro a ha
              have hle := (Finset.mem_filter.mp ha).2
              exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
            calc
              ((Nat.divisors P).filter (fun d => d ≤ y * y)).card ≤
                  (Finset.range (y * y + 1)).card := Finset.card_le_card hsub
              _ = y * y + 1 := by simp
          calc
            (∑ d ∈ Nat.divisors P,
              if d ≤ y * y then ((y * y : ℕ) : ℝ) *
                ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 else 0) =
              ∑ d ∈ (Nat.divisors P).filter (fun d => d ≤ y * y),
                ((y * y : ℕ) : ℝ) * ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2 := by
                  rw [← Finset.sum_filter]
            _ = ((Nat.divisors P).filter (fun d => d ≤ y * y)).card *
                (((y * y : ℕ) : ℝ) * ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((y * y + 1 : ℕ) : ℝ) *
                (((y * y : ℕ) : ℝ) * ((y * y + 1 : ℕ) : ℝ) ^ 2 * C ^ 2) := by
                  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
            _ = _ := by ring
    _ = _ := by simp [C]; ring

/-- Explicit Selberg upper bound for the plus linear pair sieve.

The main term is the exact reciprocal Selberg denominator; the error is a
coarse polynomial bound obtained from the finite support of the squared
Selberg coefficients. -/
theorem pairSelbergEven_sifted_bound_explicit (k X P y : ℕ) (hk : 2 ∣ k)
    (hP : Squarefree P) (hy : 1 ≤ y) :
    (pairBoundingSieveEven k (X + 1) P hk hP).siftedSum ≤
      ((X + 1 : ℕ) : ℝ) /
        pairSelbergDen (pairBoundingSieveEven k (X + 1) P hk hP) y +
      ((y * y + 1 : ℕ) : ℝ) ^ 3 *
        ((y : ℝ) * ((y : ℝ) + 1)) ^ 2 * (y * y : ℝ) := by
  calc
    (pairBoundingSieveEven k (X + 1) P hk hP).siftedSum ≤
        ((X + 1 : ℕ) : ℝ) /
          pairSelbergDen (pairBoundingSieveEven k (X + 1) P hk hP) y +
        (pairBoundingSieveEven k (X + 1) P hk hP).errSum
          (pairSelbergMuPlus
            (pairBoundingSieveEven k (X + 1) P hk hP) y) :=
      pairSelbergEven_sifted_bound k X P y hk hP hy
    _ ≤ ((X + 1 : ℕ) : ℝ) /
          pairSelbergDen (pairBoundingSieveEven k (X + 1) P hk hP) y +
        ((y * y + 1 : ℕ) : ℝ) ^ 3 *
          ((y : ℝ) * ((y : ℝ) + 1)) ^ 2 * (y * y : ℝ) :=
      by
        simpa [add_comm] using
          (add_le_add_left
            (pairSelbergEven_errSum_explicit k (X + 1) P y hk hP hy)
            (((X + 1 : ℕ) : ℝ) /
              pairSelbergDen (pairBoundingSieveEven k (X + 1) P hk hP) y))

end MathGacha
