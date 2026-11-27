import Gacha.Primality
import Gacha.Reduction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace MathGacha

/-- The unit conditions keep the full order d after reduction modulo every prime divisor. -/
def largeOrderCertificate (N d : ℕ) : Prop :=
  ∃ w : ZMod N, w^d=1 ∧ ∀ r : ℕ, r.Prime → r ∣ d → IsUnit (w^(d/r)-1)

/-- The certified order divides q−1 for every prime q dividing the modulus. -/
theorem orderDividesPrimeFactorSubOne {N d q : ℕ} (hd : 0<d)
    (cert : largeOrderCertificate N d) (hq : q.Prime) (hqN : q ∣ N) : d ∣ q-1 := by
  obtain ⟨w,hw,hp⟩ := cert
  have : Fact q.Prime := ⟨hq⟩
  let f := ZMod.castHom hqN (ZMod q)
  have he : (f w)^d=1 := by rw [← map_pow,hw,map_one]
  have horder : orderOf (f w)=d := by
    apply orderOf_eq_of_pow_and_pow_div_prime hd he
    intro r hr hrdiv hz
    have hu := (hp r hr hrdiv).map f
    rw [map_sub,map_pow,map_one,hz,sub_self] at hu
    exact not_isUnit_zero hu
  have hw0 : f w≠0 := by intro hz; simp [hz,zero_pow hd.ne'] at he
  have hdiv := ZMod.orderOf_dvd_card_sub_one hw0
  rw [horder] at hdiv
  exact hdiv

/-- Pocklington's criterion in terms of a large order that survives reduction
at every prime divisor of the modulus. -/
theorem primeIffLargeOrderCertificate {N d : ℕ} (hN : 1<N) (hd : 0<d)
    (hf : d ∣ N-1) (hsize : N<d^2) : N.Prime ↔ largeOrderCertificate N d := by
  constructor
  · intro hp
    have : Fact N.Prime := ⟨hp⟩
    obtain ⟨a,ha,hq⟩ := reverse_lucas_primality N hp
    have ho := orderOf_eq_of_pow_and_pow_div_prime (Nat.sub_pos_of_lt hN) ha hq
    have hdd : d ∣ orderOf a := ho ▸ hf
    let w := a^(orderOf a/d)
    have how : orderOf w=d := orderOf_pow_orderOf_div (by omega) hdd
    refine ⟨w,how ▸ pow_orderOf_eq_one w,?_⟩
    intro r hr hrd
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp hz)
    rw [how] at hh
    have hdiv := Nat.div_pos (Nat.le_of_dvd hd hrd) hr.pos
    exact (Nat.not_lt_of_ge (Nat.le_of_dvd hdiv hh)) (Nat.div_lt_self hd hr.one_lt)
  · rintro ⟨w,hw,hp⟩
    by_contra hn
    let q := N.minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hdiv := orderDividesPrimeFactorSubOne hd ⟨w,hw,hp⟩ hq (Nat.minFac_dvd N)
    have hqpos := hq.one_lt
    have hl := Nat.le_of_dvd (Nat.sub_pos_of_lt hqpos) hdiv
    have hs : q^2≤N := Nat.minFac_sq_le_self (by omega) hn
    nlinarith [Nat.pow_le_pow_left (by omega : d≤q) 2]

/-- Cassini's identity at the even index, stated without integer subtraction. -/
theorem evenCassini (k : ℕ) :
    Nat.fib (2*k+1)^2=Nat.fib (2*k)*Nat.fib (2*k+2)+1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by ring]
    rw [show 2*k+2+1=(2*k+1)+2 by omega,Nat.fib_add_two (n:=2*k+2),
      Nat.fib_add_two (n:=2*k+1),Nat.fib_add_two (n:=2*k)] at *
    nlinarith

/-- Odd-index Lucas number L_(2k+1), shared by F_(4k+1)−1 and F_(4k+3)−1. -/
def oddLucasDivisor (k : ℕ) := Nat.fib (2*k)+Nat.fib (2*k+2)

theorem oddLucasDivisorProducts (k : ℕ) :
    Nat.fib (4*k+1)=Nat.fib (2*k)*oddLucasDivisor k+1 ∧
    Nat.fib (4*k+3)=Nat.fib (2*k+2)*oddLucasDivisor k+1 := by
  have h1 := Nat.fib_two_mul_add_one (2*k)
  have h3 := Nat.fib_two_mul_add_one (2*k+1)
  have hc := evenCassini k
  rw [show 2*(2*k)+1=4*k+1 by ring] at h1
  rw [show 2*(2*k+1)+1=4*k+3 by ring,show 2*k+1+1=2*k+2 by omega] at h3
  unfold oddLucasDivisor
  constructor <;> nlinarith

/-- Factoring the one odd Lucas divisor suffices for a primality certificate
at every odd Fibonacci index from five onward. -/
theorem fibPrimeIffOddLucasCertificate {p : ℕ} (hodd : Odd p) (hp5 : 5≤p) :
    (Nat.fib p).Prime ↔ largeOrderCertificate (Nat.fib p) (oddLucasDivisor (p/4)) := by
  let k := p/4
  have hk : 1≤k := by dsimp [k]; omega
  have hpform : p=4*k+1 ∨ p=4*k+3 := by obtain ⟨j,hj⟩ := hodd; dsimp [k]; omega
  have ha := Nat.fib_pos.mpr (show 0<2*k by omega)
  have hb := Nat.fib_mono (show 3≤2*k+2 by omega)
  have h2 : Nat.fib 3=2 := by decide
  let d := oddLucasDivisor k
  have hd0 : 1<d := by dsimp [d,oddLucasDivisor]; omega
  have hlt₁ : Nat.fib (2*k)<d := by dsimp [d,oddLucasDivisor]; omega
  have hlt₂ : Nat.fib (2*k+2)<d := by dsimp [d,oddLucasDivisor]; omega
  have hN := Nat.le_fib_self hp5
  have hform := oddLucasDivisorProducts k
  have hprod : ∃ b<d,Nat.fib p=b*d+1 := by
    rcases hpform with hex|hex
    · exact ⟨_,hlt₁,hex ▸ hform.1⟩
    · exact ⟨_,hlt₂,hex ▸ hform.2⟩
  obtain ⟨b,hb,he⟩ := hprod
  have hdvd : d ∣ Nat.fib p-1 := by rw [he,Nat.add_sub_cancel]; exact dvd_mul_left _ _
  have hs : Nat.fib p<d^2 := by nlinarith [Nat.mul_le_mul_right d (show b+1≤d by omega)]
  exact primeIffLargeOrderCertificate (N:=Nat.fib p) (d:=d) (show 1<Nat.fib p by omega) (by omega : 0<d) hdvd hs

theorem originalIffOddLucasCertificates :
    Original ↔ ∀ B : ℕ, ∃ p>max B 5, p.Prime ∧
      largeOrderCertificate (Nat.fib p) (oddLucasDivisor (p/4)) := by
  rw [originalIffUnboundedPrimeIndices]
  constructor
  · intro h B
    obtain ⟨p,hp,hprime,hf⟩ := h (max B 5)
    exact ⟨p,hp,hprime,(fibPrimeIffOddLucasCertificate (hprime.odd_of_ne_two (by omega)) (by omega)).mp hf⟩
  · intro h B
    obtain ⟨p,hp,hprime,hf⟩ := h B
    exact ⟨p,by omega,hprime,(fibPrimeIffOddLucasCertificate (hprime.odd_of_ne_two (by omega)) (by omega)).mpr hf⟩

end MathGacha
