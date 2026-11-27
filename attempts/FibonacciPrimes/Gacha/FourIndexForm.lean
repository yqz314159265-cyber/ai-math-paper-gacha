import Gacha.QuarticForm
import Gacha.QuarticCharacter
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Nat.Squarefree

namespace MathGacha

theorem odd_square_mod8 {n : ℕ} (hn : n % 2 = 1) : n ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
    refine ⟨n / 2, ?_⟩
    omega
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj]
    ring_nf
    omega
  · rw [hj]
    ring_nf
    omega

theorem sumSquareRepresentation
    {q : ℕ} [Fact q.Prime] (hq40 : q % 40 = 29) :
    ∃ a b : ℕ, q = a ^ 2 + b ^ 2 := by
  have hq4 : q % 4 ≠ 3 := by omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hq4
  exact ⟨a, b, hab.symm⟩

theorem representation_has_odd_coordinate
    {q a b : ℕ} (hq40 : q % 40 = 29) (hab : q = a ^ 2 + b ^ 2) :
    a % 2 = 1 ∨ b % 2 = 1 := by
  have hq2 : q % 2 = 1 := by omega
  rw [hab] at hq2
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.add_mod, Nat.pow_mod, ha, hb] at hq2 ⊢

theorem even_coordinate_of_odd_left
    {q a b : ℕ} (hq40 : q % 40 = 29) (hab : q = a ^ 2 + b ^ 2)
    (ha : a % 2 = 1) : b % 2 = 0 := by
  have hq2 : q % 2 = 1 := by omega
  rw [hab] at hq2
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · exact hb
  · simp [Nat.add_mod, Nat.pow_mod, ha, hb] at hq2

theorem even_square_half_is_odd
    {q a v : ℕ} (hq40 : q % 40 = 29)
    (ha : a % 2 = 1) (hq : q = a ^ 2 + (2 * v) ^ 2) : v % 2 = 1 := by
  have hq8 : q % 8 = 5 := by omega
  have hasq8 := odd_square_mod8 ha
  rw [hq] at hq8
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv
  · obtain ⟨w, rfl⟩ : ∃ w, v = 2 * w := by
      refine ⟨v / 2, ?_⟩
      omega
    rw [Nat.add_mod, hasq8] at hq8
    ring_nf at hq8
    omega
  · exact hv

theorem orientedSumSquareRepresentation
    {q : ℕ} [Fact q.Prime] (hq40 : q % 40 = 29) :
    ∃ a b v : ℕ, q = a ^ 2 + b ^ 2 ∧ a % 2 = 1 ∧ b = 2 * v ∧ v % 2 = 1 := by
  obtain ⟨x, y, hxy⟩ := sumSquareRepresentation hq40
  rcases representation_has_odd_coordinate hq40 hxy with hx | hy
  · have hy0 := even_coordinate_of_odd_left hq40 hxy hx
    refine ⟨x, y, y / 2, hxy, hx, ?_, ?_⟩
    · omega
    · apply even_square_half_is_odd hq40 hx
      rw [show 2 * (y / 2) = y by omega]
      exact hxy
  · have hx0 := even_coordinate_of_odd_left hq40 (by nlinarith [hxy]) hy
    refine ⟨y, x, x / 2, by nlinarith [hxy], hy, ?_, ?_⟩
    · omega
    · apply even_square_half_is_odd hq40 hy
      rw [show 2 * (x / 2) = x by omega]
      nlinarith [hxy]

/-- Rotating a two-square representation produces a square root of minus one modulo its sum. -/
theorem coordinateRootMinusOne {a b q : ℕ} [Fact q.Prime] (he : q=a^2+b^2)
    (hb : (b : ZMod q) ≠ 0) : ((a : ZMod q)/b)^2 = -1 := by
  have hz : ((q : ℕ) : ZMod q)=0 := ZMod.natCast_self _
  have hz' := congrArg (fun n : ℕ => (n : ZMod q)) he
  change (q : ZMod q) = ((a^2+b^2 : ℕ) : ZMod q) at hz'
  rw [hz, Nat.cast_add, Nat.cast_pow, Nat.cast_pow] at hz'
  rw [div_pow, div_eq_iff (pow_ne_zero _ hb)]
  linear_combination -hz'

/-- The integer form attached to the second factor position, expressed with the parity
of the two coordinates already absorbed in the coefficient 100. -/
theorem secondFactorShapeArithmetic {q a b : ℕ} (hsum : q=a^2+b^2)
    (hbe : Even b) (hb5 : 5 ∣ b) : ∃ x y : ℕ, q = x^2+100*y^2 := by
  obtain ⟨v,hv⟩ := hbe
  have hfive : 5 ∣ v := by omega
  obtain ⟨y,hy⟩ := hfive
  exact ⟨a,y,by rw [hsum,hv,hy]; ring⟩

/-- A representation of a prime as a sum of squares is primitive. -/
theorem primeTwoSquareCoprime {q a b : ℕ} (hq : q.Prime) (he : q=a^2+b^2) : a.Coprime b := by
  apply Nat.coprime_of_dvd
  intro r hr hra hrb
  apply (Nat.squarefree_iff_prime_squarefree.mp hq.squarefree) r hr
  rw [he,pow_two,pow_two]
  exact dvd_add (mul_dvd_mul hra hra) (mul_dvd_mul hrb hrb)

/-- The even coordinate is nonzero modulo the represented prime in the
29 modulo 40 branch. -/
theorem evenCoordinateNonzero {q a b v : ℕ} (he : q=a^2+b^2)
    (ha : Odd a) (hb : b=2*v) (hv : Odd v) : (b : ZMod q) ≠ 0 := by
  obtain ⟨m,hm⟩ := ha
  obtain ⟨w,hw⟩ := hv
  have hbpos : 0<b := by omega
  have hb2 : b ≤ b^2 := by
    simpa [pow_two] using Nat.mul_le_mul_left b (show 1≤b by omega)
  have ha2 : 0<a^2 := pow_pos (by omega) 2
  intro hz
  have hh := Nat.le_of_dvd hbpos ((ZMod.natCast_eq_zero_iff b q).mp hz)
  omega

/-- In an oriented representation of q by two squares, only divisibility of the
even coordinate by five is needed to test 4p+1. -/
theorem fourNeighborDvdIffCoordinate {p q a b v : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hq : q.Prime) (hshape : q=4*p+1) (hclass : p%5=2) (he : q=a^2+b^2)
    (ha : Odd a) (hb : b=2*v) (hv : Odd v) (hcop : a.Coprime b)
    (hbzero : (b : ZMod q) ≠ 0) : q ∣ Nat.fib p ↔ 5 ∣ b := by
  have : Fact q.Prime := ⟨hq⟩
  have hn : Odd (a+2*b) := by obtain ⟨m,hm⟩ := ha; exact ⟨m+b, by omega⟩
  have hcn : Int.gcd (b:ℤ) ((a+2*b:ℕ):ℤ)=1 := by
    rw [Int.gcd_natCast_natCast, Nat.mul_comm 2 b, Nat.gcd_add_mul_left_right]
    exact hcop.symm
  have hvb : v ∣ b := hb ▸ dvd_mul_left v 2
  have hcav : Int.gcd (a:ℤ) (v:ℤ)=1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcop.of_dvd_right hvb
  have hmodav : q%v=a^2%v := by
    rw [he,hb,Nat.add_mod]
    simp [pow_two,Nat.mul_mod]
  have hq8 := fourBoundaryQModEight hp hp5 hshape
  have hmod5 : (a^2+b^2)%5=4 := by rw [← he]; omega
  rw [fourNeighborDvdIffSquare hp hp5 hq hshape hclass _ (coordinateRootMinusOne he hbzero)]
  exact isSquare_two_add_div_iff_five_dvd he rfl hn hcn hb hv hcav hmodav hq8 hmod5 hbzero

/-- For q=4p+1, writing q as x²+100y² is equivalent to writing the
index p itself as a product of consecutive integers plus 25y². -/
theorem quarterFormIndexIff (p : ℕ) :
    (∃ x y : ℕ, 4*p+1=x^2+100*y^2) ↔ ∃ u v : ℕ, p=u*(u+1)+25*v^2 := by
  constructor
  · rintro ⟨x,y,he⟩
    have hx : x%2=1 := by
      have hm := congrArg (·%2) he
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod, hx] at hm
      · exact hx
    let u := x/2
    have hu : x=2*u+1 := by dsimp [u]; omega
    refine ⟨u,y,?_⟩
    rw [hu] at he
    nlinarith
  · rintro ⟨u,v,rfl⟩
    exact ⟨2*u+1,v,by ring⟩

/-- Primality of p and 4p+1 forces the correct residue modulo five
whenever the quadratic form represents 4p+1. -/
theorem quarterFormForcesClass {p q x y : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (hq : q.Prime) (hshape : q=4*p+1) (he : q=x^2+100*y^2) : p%5=2 := by
  have hp0 : p%5 ≠ 0 := by
    intro h
    have := (Nat.dvd_prime_two_le hp (by decide : 2≤5)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hq0 : q%5 ≠ 0 := by
    intro h
    have := (Nat.dvd_prime_two_le hq (by decide : 2≤5)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hm : q%5=(x%5)^2%5 := by rw [he]; simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have hres : x%5=0 ∨ x%5=1 ∨ x%5=2 ∨ x%5=3 ∨ x%5=4 := by omega
  rcases hres with h|h|h|h|h <;> rw [h] at hm <;> norm_num at hm <;> omega

/-- In the class q≡29 (mod 40), the even coordinate determines whether
q divides the Fibonacci term at its prime quarter-index. -/
theorem fourBoundaryDvdIffQuadraticForm {p q : ℕ} (hp : p.Prime) (hp5 : 5<p)
    (he : q=4*p+1) :
    q ∣ Nat.fib p ↔ q.Prime ∧ ∃ x y : ℕ, q=x^2+100*y^2 := by
  constructor
  · intro hd
    obtain ⟨hq,hclass,_⟩ := (fourBoundaryCriterion hp hp5 he).mp hd
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
    have hq40 : q%40=29 := by omega
    obtain ⟨a,b,v,hs,ha',hb,hv'⟩ := orientedSumSquareRepresentation hq40
    have ha := Nat.odd_iff.mpr ha'
    have hv := Nat.odd_iff.mpr hv'
    have htest := fourNeighborDvdIffCoordinate hp hp5 hq he hclass hs ha hb hv
      (primeTwoSquareCoprime hq hs) (evenCoordinateNonzero hs ha hb hv)
    exact ⟨hq, secondFactorShapeArithmetic hs ⟨v,by omega⟩ (htest.mp hd)⟩
  · rintro ⟨hq,x,y,hs⟩
    have hclass := quarterFormForcesClass hp hp5 hq he hs
    obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
    have hq40 : q%40=29 := by omega
    let b := 10*y
    have hrep : q=x^2+b^2 := by rw [hs]; dsimp [b]; ring
    have hxodd : Odd x := by
      have hz := congrArg (·%2) hs
      have hx : x%2=1 := by
        rcases Nat.mod_two_eq_zero_or_one x with hh | hh
        · simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod, hh] at hz
          omega
        · exact hh
      exact Nat.odd_iff.mpr hx
    let v := 5*y
    have hb : b=2*v := by dsimp [b,v]; omega
    have hv : Odd v := Nat.odd_iff.mpr (even_square_half_is_odd hq40 (Nat.odd_iff.mp hxodd) (hb ▸ hrep))
    have htest := fourNeighborDvdIffCoordinate hp hp5 hq he hclass hrep hxodd hb hv
      (primeTwoSquareCoprime hq hrep) (evenCoordinateNonzero hrep hxodd hb hv)
    exact htest.mpr (show 5∣10*y by omega)

/-- This index-only representation eliminates the auxiliary finite field and the mod-five test. -/
theorem fourBoundaryDvdIffIndexForm {p : ℕ} (hp : p.Prime) (hp5 : 5<p) :
    4*p+1 ∣ Nat.fib p ↔ (4*p+1).Prime ∧ ∃ u v : ℕ, p=u*(u+1)+25*v^2 := by
  rw [fourBoundaryDvdIffQuadraticForm hp hp5 rfl, quarterFormIndexIff]

end MathGacha
