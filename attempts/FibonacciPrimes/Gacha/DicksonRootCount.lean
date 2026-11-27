import Gacha.DicksonSieve
import Gacha.PowerFiber
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic

namespace MathGacha

open Polynomial

/-- A root of `u^k = r` has Frobenius-fixed inverse trace, hence descends to `ZMod q`.
The descended trace is a root of the corresponding Dickson polynomial. -/
theorem traceFiber_fixed_point
    {q p k : ℕ} [Fact q.Prime] (r : AlgebraicClosure (ZMod q))
    (hr0 : r ≠ 0) (_hrinv : r ≠ r⁻¹) (htrace : r + r⁻¹ = -3)
    (hrp : r ^ p = 1) (hsize : k * p = q - 1 ∨ k * p = q + 1)
    (u : AlgebraicClosure (ZMod q)) (hu : u ^ k = r) :
    ∃ z : ZMod q, algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) z = u + u⁻¹ ∧
      (Polynomial.dickson 1 1 k).eval z = -3 := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hk : 0 < k := by
    by_contra hkn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkn
    have hqne1 : q ≠ 1 := (Fact.out : q.Prime).ne_one
    rcases hsize with h | h
    · have hq1 : q = 1 := by rw [hk0] at h; omega
      exact hqne1 hq1
    · rw [hk0] at h
      omega
  have hu0 : u ≠ 0 := by
    intro hu0
    have hzero : (0 : AlgebraicClosure (ZMod q)) = r := by
      simpa [hu0, hk.ne'] using hu
    exact hr0 hzero.symm
  have hup : u ^ (k * p) = 1 := by
    calc
      u ^ (k * p) = (u ^ k) ^ p := by rw [pow_mul]
      _ = r ^ p := by rw [hu]
      _ = 1 := hrp
  have huq : u ^ q = u ∨ u ^ q = u⁻¹ := by
    rcases hsize with h | h
    · have hprev : u ^ (q - 1) = 1 := by simpa [h] using hup
      exact Or.inl <| (powPredecessorOneIff hu0 (Fact.out : q.Prime).pos).mp hprev
    · have hsucc : u ^ (q + 1) = 1 := by simpa [h] using hup
      exact Or.inr <| (powSuccessorOneIff hu0 q).mp hsucc
  have hfix : (u + u⁻¹) ^ q = u + u⁻¹ := by
    rw [add_pow_char, inv_pow]
    rcases huq with h | h
    · simp [h]
    · simp [h, add_comm]
  obtain ⟨z, hz⟩ :=
    (finiteField_image_iff_frobenius_fixed q (u + u⁻¹)).2 hfix
  let f : ZMod q →+* AlgebraicClosure (ZMod q) := algebraMap _ _
  have hmapped (z : ZMod q) :
      f ((Polynomial.dickson 1 1 k).eval z) =
        (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (f z) := by
    rw [← Polynomial.eval_map_apply, Polynomial.map_dickson, map_one]
  have htracePow :
      (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (u + u⁻¹) =
        u ^ k + (u ^ k)⁻¹ := by
    simpa only [inv_pow] using
      Polynomial.dickson_one_one_eval_add_inv u u⁻¹ (mul_inv_cancel₀ hu0) k
  refine ⟨z, hz, ?_⟩
  apply f.injective
  calc
    f ((Polynomial.dickson 1 1 k).eval z) =
        (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (f z) := hmapped z
    _ = (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (u + u⁻¹) := by rw [hz]
    _ = u ^ k + (u ^ k)⁻¹ := htracePow
    _ = r + r⁻¹ := by rw [hu]
    _ = -3 := htrace
    _ = f (-3 : ZMod q) := by simp only [map_neg, map_ofNat]

/-- Map a power fiber to the unique descended inverse-trace Dickson root. -/
noncomputable def traceFiberToRoot
    {q p k : ℕ} [Fact q.Prime] (r : AlgebraicClosure (ZMod q))
    (hr0 : r ≠ 0) (hrinv : r ≠ r⁻¹) (htrace : r + r⁻¹ = -3)
    (hrp : r ^ p = 1) (hsize : k * p = q - 1 ∨ k * p = q + 1)
    (u : {u : AlgebraicClosure (ZMod q) // u ^ k = r}) :
    {z : ZMod q // (Polynomial.dickson 1 1 k).eval z = -3} :=
  ⟨Classical.choose (traceFiber_fixed_point r hr0 hrinv htrace hrp hsize u.1 u.2),
    (Classical.choose_spec (traceFiber_fixed_point r hr0 hrinv htrace hrp hsize u.1 u.2)).2⟩

/-- The descended root is characterized by the inverse trace. -/
theorem traceFiberToRoot_spec
    {q p k : ℕ} [Fact q.Prime] (r : AlgebraicClosure (ZMod q))
    (hr0 : r ≠ 0) (hrinv : r ≠ r⁻¹) (htrace : r + r⁻¹ = -3)
    (hrp : r ^ p = 1) (hsize : k * p = q - 1 ∨ k * p = q + 1)
    (u : {u : AlgebraicClosure (ZMod q) // u ^ k = r}) :
    algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (traceFiberToRoot r hr0 hrinv htrace hrp hsize u).1 =
      u.1 + u.1⁻¹ :=
  (Classical.choose_spec (traceFiber_fixed_point r hr0 hrinv htrace hrp hsize u.1 u.2)).1

/-- A power fiber of a non-self-inverse value of trace `-3` is equivalent to the
corresponding Dickson root fiber when `kp = q ± 1`. -/
noncomputable def traceFiberEquivDicksonRoots
    {q p k : ℕ} [Fact q.Prime] (r : AlgebraicClosure (ZMod q))
    (hr0 : r ≠ 0) (hrinv : r ≠ r⁻¹) (htrace : r + r⁻¹ = -3)
    (hrp : r ^ p = 1) (hsize : k * p = q - 1 ∨ k * p = q + 1) :
    {u : AlgebraicClosure (ZMod q) // u ^ k = r} ≃
      {z : ZMod q // (Polynomial.dickson 1 1 k).eval z = -3} := by
  let f := traceFiberToRoot r hr0 hrinv htrace hrp hsize
  apply Equiv.ofBijective f
  constructor
  · intro u v huv
    apply Subtype.ext
    have hk : 0 < k := by
      have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
      by_contra hkn
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkn
      have hqne1 : q ≠ 1 := (Fact.out : q.Prime).ne_one
      rcases hsize with h | h
      · have hq1 : q = 1 := by rw [hk0] at h; omega
        exact hqne1 hq1
      · rw [hk0] at h
        omega
    have hu0 : u.1 ≠ 0 := by
      intro hz
      apply hr0
      calc
        r = u.1 ^ k := u.2.symm
        _ = 0 := by simp [hz, hk.ne']
    have hv0 : v.1 ≠ 0 := by
      intro hz
      apply hr0
      calc
        r = v.1 ^ k := v.2.symm
        _ = 0 := by simp [hz, hk.ne']
    have htr : u.1 + u.1⁻¹ = v.1 + v.1⁻¹ := by
      calc
        u.1 + u.1⁻¹ = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (f u).1 :=
          (traceFiberToRoot_spec r hr0 hrinv htrace hrp hsize u).symm
        _ = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (f v).1 :=
          congrArg (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) (congrArg Subtype.val huv)
        _ = v.1 + v.1⁻¹ := traceFiberToRoot_spec r hr0 hrinv htrace hrp hsize v
    rcases (inverseTrace_eq_iff_eq_or_inv hu0 hv0).mp htr with h | h
    · exact h
    · have hpow : u.1 ^ k = (v.1 ^ k)⁻¹ := by
        calc
          u.1 ^ k = (v.1⁻¹) ^ k := by rw [h]
          _ = (v.1 ^ k)⁻¹ := by rw [inv_pow]
      have hrEq : r = r⁻¹ := by
        calc
          r = u.1 ^ k := u.2.symm
          _ = (v.1 ^ k)⁻¹ := hpow
          _ = r⁻¹ := by rw [v.2]
      exact (hrinv hrEq).elim
  · intro z
    let alg : ZMod q →+* AlgebraicClosure (ZMod q) := algebraMap _ _
    have hmapped (x : ZMod q) :
        alg ((Polynomial.dickson 1 1 k).eval x) =
          (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (alg x) := by
      rw [← Polynomial.eval_map_apply, Polynomial.map_dickson, map_one]
    have htracePow (w : AlgebraicClosure (ZMod q)) (hw : w ≠ 0) :
        (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (w + w⁻¹) =
          w ^ k + (w ^ k)⁻¹ := by
      simpa only [inv_pow] using
        Polynomial.dickson_one_one_eval_add_inv w w⁻¹ (mul_inv_cancel₀ hw) k
    obtain ⟨w, hw0, hwtrace⟩ := exists_unit_with_trace (alg z.1)
    have hsum : w ^ k + (w ^ k)⁻¹ = r + r⁻¹ := by
      calc
        w ^ k + (w ^ k)⁻¹ =
            (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (w + w⁻¹) :=
              (htracePow w hw0).symm
        _ = (Polynomial.dickson 1 (1 : AlgebraicClosure (ZMod q)) k).eval (alg z.1) := by rw [hwtrace]
        _ = alg ((Polynomial.dickson 1 1 k).eval z.1) := (hmapped z.1).symm
        _ = alg (-3 : ZMod q) := by rw [z.2]
        _ = -3 := by simp only [map_neg, map_ofNat]
        _ = r + r⁻¹ := htrace.symm
    have hchoose : ∃ u : AlgebraicClosure (ZMod q), u ≠ 0 ∧
        u + u⁻¹ = alg z.1 ∧ u ^ k = r := by
      rcases (inverseTrace_eq_iff_eq_or_inv (pow_ne_zero _ hw0) hr0).mp hsum with h | h
      · exact ⟨w, hw0, hwtrace, h⟩
      · refine ⟨w⁻¹, inv_ne_zero hw0, ?_, ?_⟩
        · rw [inv_inv, add_comm]
          exact hwtrace
        · calc
            (w⁻¹) ^ k = (w ^ k)⁻¹ := by rw [inv_pow]
            _ = (r⁻¹)⁻¹ := by rw [h]
            _ = r := inv_inv r
    obtain ⟨u, hu0, huz, huk⟩ := hchoose
    let x : {u : AlgebraicClosure (ZMod q) // u ^ k = r} := ⟨u, huk⟩
    have hmap : f x = z := by
      apply Subtype.ext
      apply (RingHom.injective (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))))
      calc
        algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (f x).1 = u + u⁻¹ :=
          traceFiberToRoot_spec r hr0 hrinv htrace hrp hsize x
        _ = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) z.1 := huz
    exact ⟨x, hmap⟩

/-- For primes `p,q > 5` with `p | neighborIndex q`, the number of Dickson roots
is the multiplier exactly when `q | F_p`, and is zero otherwise. -/
theorem natCard_dickson_roots_eq_if_fib_divides
    {p q : ℕ} (hp : p.Prime) [Fact q.Prime] (hq5 : 5 < q)
    (hdiv : p ∣ neighborIndex q) :
    Nat.card {z : ZMod q // (Polynomial.dickson 1 1 (neighborIndex q / p)).eval z = -3} =
      if q ∣ Nat.fib p then neighborIndex q / p else 0 := by
  let k := neighborIndex q / p
  have hneighbor : neighborIndex q = q - 1 ∨ neighborIndex q = q + 1 := by
    unfold neighborIndex
    split <;> simp
  have hkp : k * p = neighborIndex q := by
    dsimp [k]
    exact Nat.div_mul_cancel hdiv
  have ht : k * p = q - 1 ∨ k * p = q + 1 := by rw [hkp]; exact hneighbor
  have hTpos : 0 < neighborIndex q := by
    rcases hneighbor with h | h
    · rw [h]
      omega
    · rw [h]
      omega
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hk0, zero_mul] at hkp
    omega
  have hqdivk : ¬ q ∣ k := not_dvd_multiplier_of_neighbor (Fact.out : q.Prime) ht
  have hq2 : q ≠ 2 := by omega
  have hq5ne : q ≠ 5 := by omega
  by_cases hfib : q ∣ Nat.fib p
  · obtain ⟨r, hr0, hrinv, htrace, hdetect⟩ := fibRatioData hq2 hq5ne
    have hrp : r ^ p = 1 := (hdetect p).mp hfib
    let e := traceFiberEquivDicksonRoots r hr0 hrinv htrace hrp ht
    have hcount : Nat.card {u : AlgebraicClosure (ZMod q) // u ^ k = r} = k :=
      natCard_pow_fiber (AlgebraicClosure (ZMod q)) q k hk hqdivk r hr0
    calc
      Nat.card {z : ZMod q // (Polynomial.dickson 1 1 k).eval z = -3} =
          Nat.card {u : AlgebraicClosure (ZMod q) // u ^ k = r} := Nat.card_congr e.symm
      _ = k := hcount
      _ = if q ∣ Nat.fib p then neighborIndex q / p else 0 := by simp [k, hfib]
  · have hEmpty : IsEmpty {z : ZMod q // (Polynomial.dickson 1 1 k).eval z = -3} := by
      refine ⟨fun z => ?_⟩
      apply hfib
      exact (primeDivisorIffDickson hp (Fact.out : q.Prime) hq5).mpr ⟨hdiv, ⟨z.1, z.2⟩⟩
    rw [if_neg hfib]
    change Nat.card {z : ZMod q // (Polynomial.dickson 1 1 k).eval z = -3} = 0
    exact Finite.card_eq_zero_iff.mpr hEmpty

end MathGacha
