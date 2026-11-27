import Gacha.F2971Factors
import Gacha.ResidueCertificate

namespace MathGacha

set_option maxRecDepth 30000
set_option maxHeartbeats 12000000

theorem fib2971Unit00 : residueUnitTest fib2971Modulus 720 (fib2971Order/537771403239312279772324930133) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit01 : residueUnitTest fib2971Modulus 720 (fib2971Order/211168537607802318179066122231) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit02 : residueUnitTest fib2971Modulus 720 (fib2971Order/137096217949680001) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit03 : residueUnitTest fib2971Modulus 720 (fib2971Order/23317837226040061) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit04 : residueUnitTest fib2971Modulus 720 (fib2971Order/3943480033796491) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit05 : residueUnitTest fib2971Modulus 720 (fib2971Order/1369471729429) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit06 : residueUnitTest fib2971Modulus 720 (fib2971Order/1808388451) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit07 : residueUnitTest fib2971Modulus 720 (fib2971Order/1550853481) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit08 : residueUnitTest fib2971Modulus 720 (fib2971Order/914116501) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit09 : residueUnitTest fib2971Modulus 720 (fib2971Order/220862269) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit10 : residueUnitTest fib2971Modulus 720 (fib2971Order/51164521) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit11 : residueUnitTest fib2971Modulus 720 (fib2971Order/4247101) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit12 : residueUnitTest fib2971Modulus 720 (fib2971Order/1513909) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit13 : residueUnitTest fib2971Modulus 720 (fib2971Order/119611) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit14 : residueUnitTest fib2971Modulus 720 (fib2971Order/42391) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit15 : residueUnitTest fib2971Modulus 720 (fib2971Order/39161) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit16 : residueUnitTest fib2971Modulus 720 (fib2971Order/9901) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit17 : residueUnitTest fib2971Modulus 720 (fib2971Order/5779) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit18 : residueUnitTest fib2971Modulus 720 (fib2971Order/2971) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit19 : residueUnitTest fib2971Modulus 720 (fib2971Order/2179) fib2971Witness=true := by
  decide +kernel

theorem fib2971Unit20 : residueUnitTest fib2971Modulus 720 (fib2971Order/991) fib2971Witness=true := by
  decide +kernel

theorem fib2971OrderCertificate : largeOrderCertificate fib2971Modulus fib2971Order := by
  apply largeOrderOfResidueTests (w:=fib2971Witness) (f:=720) (by decide +kernel) fib2971Factors
    (by decide +kernel) fib2971FactorsPrime
  · decide +kernel
  · exact ⟨fib2971Unit00, fib2971Unit01, fib2971Unit02, fib2971Unit03, fib2971Unit04, fib2971Unit05, fib2971Unit06, fib2971Unit07, fib2971Unit08, fib2971Unit09, fib2971Unit10, fib2971Unit11, fib2971Unit12, fib2971Unit13, fib2971Unit14, fib2971Unit15, fib2971Unit16, fib2971Unit17, fib2971Unit18, fib2971Unit19, fib2971Unit20⟩

/-- Primality of the 621-digit Fibonacci value from its order and integer discriminant. -/
theorem fib2971Prime : Nat.Prime (Nat.fib 2971) := by
  have he : Nat.fib 2971=fib2971Modulus := by rw [← Nat.fastFib_eq]; decide +kernel
  rw [he]
  exact primeOfCubicOrderSqrt (N:=fib2971Modulus) (d:=fib2971Order) (c:=fib2971Cofactor)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    fib2971OrderCertificate (by decide +kernel)

end MathGacha
