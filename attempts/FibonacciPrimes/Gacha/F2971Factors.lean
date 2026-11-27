import Gacha.CertifiedPrefix
import Gacha.CubicCertificate

namespace MathGacha

set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

/-- Factor leaves of the partial order certificate for F_2971. -/
def fib2971Leaves : List ℕ := [2, 3, 5, 7, 11, 13, 17, 23, 29, 37, 43, 47, 53, 59, 67, 79, 83, 89, 127, 157, 257, 263, 307, 313, 443, 461, 467, 661, 733, 991, 1051, 1061, 1201, 1289, 1567, 2179, 2351, 2591, 2971, 3407, 3823, 5779, 7541, 8363, 8669, 9133, 9901]

theorem fib2971LeavesPrime : ∀ q ∈ fib2971Leaves, Nat.Prime q := by
  intro q hq
  simp only [fib2971Leaves,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def fib2971Known00 : List ℕ := fib2971Leaves

theorem fib2971Known00_prime : ∀ q ∈ fib2971Known00, Nat.Prime q := fib2971LeavesPrime

def fib2971Batch00 : List LucasCertificate := [
  ⟨77699,2,[2, 53, 733]⟩,
  ⟨543233,3,[2, 2, 2, 2, 2, 2, 2, 2, 2, 1061]⟩,
  ⟨5107476667,2,[2, 3, 1567, 543233]⟩,
  ⟨2625243006839,13,[2, 257, 5107476667]⟩]

theorem fib2971Batch00_check : lucasCertificatesCheck fib2971Known00 fib2971Batch00=true := by decide +kernel

theorem fib2971Batch00_prime : ∀ c ∈ fib2971Batch00, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known00_prime fib2971Batch00_check

def fib2971Known01 : List ℕ := fib2971Known00 ++ lucasCertificateTargets fib2971Batch00

theorem fib2971Known01_prime : ∀ q ∈ fib2971Known01, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known00_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch00_prime q h

def fib2971Batch01 : List LucasCertificate := [
  ⟨58012619965128223,6,[2, 3, 29, 127, 2625243006839]⟩,
  ⟨537771403239312279772324930133,2,[2, 2, 13, 37, 59, 1051, 77699, 58012619965128223]⟩,
  ⟨200713,5,[2, 2, 2, 3, 8363]⟩,
  ⟨1204279,3,[2, 3, 200713]⟩]

theorem fib2971Batch01_check : lucasCertificatesCheck fib2971Known01 fib2971Batch01=true := by decide +kernel

theorem fib2971Batch01_prime : ∀ c ∈ fib2971Batch01, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known01_prime fib2971Batch01_check

def fib2971Known02 : List ℕ := fib2971Known01 ++ lucasCertificateTargets fib2971Batch01

theorem fib2971Known02_prime : ∀ q ∈ fib2971Known02, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known01_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch01_prime q h

def fib2971Batch02 : List LucasCertificate := [
  ⟨9534853,5,[2, 2, 3, 3, 29, 9133]⟩,
  ⟨12369126193663,3,[2, 3, 7, 67, 461, 9534853]⟩,
  ⟨211168537607802318179066122231,3,[2, 7, 3, 5, 3, 3, 23, 23, 11, 1289, 1204279, 12369126193663]⟩,
  ⟨137096217949680001,28,[2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 11, 47, 79, 661, 2351]⟩]

theorem fib2971Batch02_check : lucasCertificatesCheck fib2971Known02 fib2971Batch02=true := by decide +kernel

theorem fib2971Batch02_prime : ∀ c ∈ fib2971Batch02, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known02_prime fib2971Batch02_check

def fib2971Known03 : List ℕ := fib2971Known02 ++ lucasCertificateTargets fib2971Batch02

theorem fib2971Known03_prime : ∀ q ∈ fib2971Known03, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known02_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch02_prime q h

def fib2971Batch03 : List LucasCertificate := [
  ⟨11047,3,[2, 3, 7, 263]⟩,
  ⟨44189,2,[2, 2, 11047]⟩,
  ⟨662953,5,[2, 2, 2, 3, 23, 1201]⟩,
  ⟨3977719,6,[2, 3, 662953]⟩]

theorem fib2971Batch03_check : lucasCertificatesCheck fib2971Known03 fib2971Batch03=true := by decide +kernel

theorem fib2971Batch03_prime : ∀ c ∈ fib2971Batch03, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known03_prime fib2971Batch03_check

def fib2971Known04 : List ℕ := fib2971Known03 ++ lucasCertificateTargets fib2971Batch03

theorem fib2971Known04_prime : ∀ q ∈ fib2971Known04, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known03_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch03_prime q h

def fib2971Batch04 : List LucasCertificate := [
  ⟨23317837226040061,2,[2, 2, 3, 3, 5, 11, 67, 44189, 3977719]⟩,
  ⟨15083,2,[2, 7541]⟩,
  ⟨589493,2,[2, 2, 17, 8669]⟩,
  ⟨8252903,5,[2, 7, 589493]⟩]

theorem fib2971Batch04_check : lucasCertificatesCheck fib2971Known04 fib2971Batch04=true := by decide +kernel

theorem fib2971Batch04_prime : ∀ c ∈ fib2971Batch04, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known04_prime fib2971Batch04_check

def fib2971Known05 : List ℕ := fib2971Known04 ++ lucasCertificateTargets fib2971Batch04

theorem fib2971Known05_prime : ∀ q ∈ fib2971Known05, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known04_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch04_prime q h

def fib2971Batch05 : List LucasCertificate := [
  ⟨264092897,3,[2, 2, 2, 2, 2, 8252903]⟩,
  ⟨3943480033796491,3,[2, 3, 3, 5, 11, 15083, 264092897]⟩,
  ⟨20443,2,[2, 3, 3407]⟩,
  ⟨81773,2,[2, 2, 20443]⟩]

theorem fib2971Batch05_check : lucasCertificatesCheck fib2971Known05 fib2971Batch05=true := by decide +kernel

theorem fib2971Batch05_prime : ∀ c ∈ fib2971Batch05, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known05_prime fib2971Batch05_check

def fib2971Known06 : List ℕ := fib2971Known05 ++ lucasCertificateTargets fib2971Batch05

theorem fib2971Known06_prime : ∀ q ∈ fib2971Known06, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known05_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch05_prime q h

def fib2971Batch06 : List LucasCertificate := [
  ⟨1369471729429,2,[2, 2, 3, 3, 3, 3, 11, 37, 127, 81773]⟩,
  ⟨1808388451,7,[2, 3, 3, 3, 5, 5, 11, 47, 2591]⟩,
  ⟨1550853481,19,[2, 2, 2, 3, 5, 11, 43, 89, 307]⟩,
  ⟨914116501,2,[2, 2, 3, 3, 5, 5, 5, 11, 59, 313]⟩]

theorem fib2971Batch06_check : lucasCertificatesCheck fib2971Known06 fib2971Batch06=true := by decide +kernel

theorem fib2971Batch06_prime : ∀ c ∈ fib2971Batch06, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known06_prime fib2971Batch06_check

def fib2971Known07 : List ℕ := fib2971Known06 ++ lucasCertificateTargets fib2971Batch06

theorem fib2971Known07_prime : ∀ q ∈ fib2971Known07, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known06_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch06_prime q h

def fib2971Batch07 : List LucasCertificate := [
  ⟨16901,2,[2, 2, 5, 5, 13, 13]⟩,
  ⟨220862269,2,[2, 2, 3, 3, 3, 11, 11, 16901]⟩,
  ⟨51164521,13,[2, 2, 2, 3, 5, 11, 83, 467]⟩,
  ⟨4247101,2,[2, 2, 3, 3, 3, 5, 5, 11, 11, 13]⟩]

theorem fib2971Batch07_check : lucasCertificatesCheck fib2971Known07 fib2971Batch07=true := by decide +kernel

theorem fib2971Batch07_prime : ∀ c ∈ fib2971Batch07, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known07_prime fib2971Batch07_check

def fib2971Known08 : List ℕ := fib2971Known07 ++ lucasCertificateTargets fib2971Batch07

theorem fib2971Known08_prime : ∀ q ∈ fib2971Known08, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known07_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch07_prime q h

def fib2971Batch08 : List LucasCertificate := [
  ⟨1513909,2,[2, 2, 3, 3, 11, 3823]⟩,
  ⟨119611,2,[2, 3, 3, 3, 5, 443]⟩,
  ⟨42391,6,[2, 3, 3, 3, 5, 157]⟩,
  ⟨39161,3,[2, 2, 2, 5, 11, 89]⟩]

theorem fib2971Batch08_check : lucasCertificatesCheck fib2971Known08 fib2971Batch08=true := by decide +kernel

theorem fib2971Batch08_prime : ∀ c ∈ fib2971Batch08, Nat.Prime c.modulus :=
  lucasCertificatesCheck_sound _ _ fib2971Known08_prime fib2971Batch08_check

def fib2971Certified : List ℕ := fib2971Known08 ++ lucasCertificateTargets fib2971Batch08

theorem fib2971Certified_prime : ∀ q ∈ fib2971Certified, Nat.Prime q := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact fib2971Known08_prime q h
  · exact lucasCertificateTargets_sound _ fib2971Batch08_prime q h

def fib2971Modulus : ℕ :=
  357103560641909860720907774139063454445569926582843306794041997476301071102767570483343563518510007800304195444080518562630900027386498933944619210192856768352683468831754423234217978525765921040747291316681576556861490773135214861782877716560879686368266117365351884926393775431925116896322341130075880287169244980698837941931247516010101631704349963583400361910809925847721300802741705519412306522941202429437928826033885416656967971559902743150263252229456298992263008126719589203430407385228230361628494860172129702271172926469500802342608722006420745586297267929052509059154340968348509580552307148642001438470316229

def fib2971Order : ℕ :=
  26618529940051142232166028586983024118721964116290634646651123067799353129261330472224834194736626848563848623985948031387234399404752432599592049500775769179191963623702166702321458490471889373864353582193127

def fib2971Cofactor : ℕ :=
  13415600389884782531725402374391789145512557768135879224115153854987905450069395015762888963558860779714048672661354952563005846115057973767106332323045688555555373786964562684076464567780686569508969072764350317039664943616996266105299539308234010755285856695914798368638422584735332838634916316431916373283733953485398661580632385386933909055480581973061824481656821155158764465208607850896785182781769399134364

def fib2971Witness : ℕ :=
  208277114358558884988157425648648320923955673669529533582996787225514577447615579575299546063339119415363445638302511424643602668585634736891910469468616898438767662840864031200057707472738780209015711939728278536631154978589836698182119400383922847082283121823576769543023914175509572776665722110725629963020009946461533187056590718900266155379466139065233595801937627584621200659703123820640888800648676356001855230986014116111201527866738107209037034650616412136938048230230900462772883858122618062362223721245330630201343937043766562762468206081903178483366914183314992956527382286484141400617251142936444711996794962

def fib2971Factors : List ℕ :=
  [537771403239312279772324930133, 211168537607802318179066122231, 137096217949680001, 23317837226040061, 3943480033796491, 1369471729429, 1808388451, 1550853481, 914116501, 220862269, 51164521, 4247101, 1513909, 119611, 42391, 39161, 9901, 5779, 2971, 2179, 991]

theorem fib2971FactorsPrime : fib2971Factors.Forall Nat.Prime := by
  apply List.forall_iff_forall_mem.mpr
  intro q hq
  apply fib2971Certified_prime
  have hc : fib2971Factors.all (fun r => decide (r∈fib2971Certified))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hc q hq)

end MathGacha
