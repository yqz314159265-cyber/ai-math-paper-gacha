import Gacha.LucasChecker
import Gacha.PrefixFermat

namespace MathGacha

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-- Prime leaves of the unified Lucas DAG. -/
def lucasBasePrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 89, 97, 101, 107, 109, 113, 127, 131, 151, 167, 179, 181, 191, 199, 223, 229, 233, 269, 281, 283, 311, 313, 331, 353, 359, 431, 449, 491, 509, 521, 541, 557, 569, 571, 653, 661, 709, 797, 823, 857, 907, 911, 919, 941, 1021, 1091, 1163, 1291, 1597, 1721, 2069, 2207, 2281, 2357, 2417, 2521, 2767, 3469, 3571, 4057, 4073, 5081, 5279, 5779, 6263, 6673, 6709, 6917, 7451, 8501, 8521, 8581, 9343, 9349, 9377, 9769]

theorem lucasBasePrimes_sound : ∀ q ∈ lucasBasePrimes, q.Prime := by
  intro q hq
  simp only [lucasBasePrimes, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def lucasCertificateTargets (cs : List LucasCertificate) : List ℕ :=
  cs.map fun c => c.modulus

theorem lucasCertificateTargets_sound (cs : List LucasCertificate)
    (hcs : ∀ c ∈ cs, c.modulus.Prime) :
    ∀ q ∈ lucasCertificateTargets cs, q.Prime := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨c, hc, rfl⟩
  exact hcs c hc

def lucasNodePrefix00 : List LucasCertificate := []

/-- Topological Lucas nodes, batch 0. -/
def lucasNodeBatch00 : List LucasCertificate := [
  ⟨109441, 14, [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 19]⟩,
  ⟨10783342081, 37, [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 7, 17, 19, 23]⟩,
  ⟨12689, 3, [2, 2, 2, 2, 13, 61]⟩,
  ⟨786719, 13, [2, 31, 12689]⟩,
  ⟨6293753, 3, [2, 2, 2, 786719]⟩
]

theorem lucasNodeBatch00_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix00) lucasNodeBatch00 = true := by
  decide +kernel

theorem lucasNodeBatch00_sound : ∀ c ∈ lucasNodeBatch00, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix00) lucasNodeBatch00
    lucasBasePrimes_sound (by simp [lucasCertificateTargets, lucasNodePrefix00]) lucasNodeBatch00_check

def lucasNodePrefix01 : List LucasCertificate := lucasNodePrefix00 ++ lucasNodeBatch00

theorem lucasNodePrefix01_sound : ∀ c ∈ lucasNodePrefix01, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix01, List.mem_append] at hc
  rcases hc with hc | hc
  · simp [lucasNodePrefix00] at hc
  · exact lucasNodeBatch00_sound c hc

/-- Topological Lucas nodes, batch 1. -/
def lucasNodeBatch01 : List LucasCertificate := [
  ⟨12587507, 2, [2, 6293753]⟩,
  ⟨1066737847220321, 7, [2, 2, 2, 2, 2, 5, 11, 179, 269, 12587507]⟩,
  ⟨10495801, 11, [2, 2, 2, 3, 3, 5, 5, 7, 7, 7, 17]⟩,
  ⟨37110397, 2, [2, 2, 3, 331, 9343]⟩,
  ⟨1558013367771989, 2, [2, 2, 10495801, 37110397]⟩
]

theorem lucasNodeBatch01_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix01) lucasNodeBatch01 = true := by
  decide +kernel

theorem lucasNodeBatch01_sound : ∀ c ∈ lucasNodeBatch01, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix01) lucasNodeBatch01
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix01 lucasNodePrefix01_sound) lucasNodeBatch01_check

def lucasNodePrefix02 : List LucasCertificate := lucasNodePrefix01 ++ lucasNodeBatch01

theorem lucasNodePrefix02_sound : ∀ c ∈ lucasNodePrefix02, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix02, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix01_sound c hc
  · exact lucasNodeBatch01_sound c hc

/-- Topological Lucas nodes, batch 2. -/
def lucasNodeBatch02 : List LucasCertificate := [
  ⟨66932254279484647441, 7, [2, 2, 2, 2, 3, 5, 179, 1558013367771989]⟩,
  ⟨475420437734698220747368027166749382927701417016557193662268716376935476241, 14, [2, 2, 2, 2, 3, 3, 3, 5, 11, 17, 19, 31, 41, 61, 107, 181, 359, 541, 2521, 109441, 10783342081, 1066737847220321, 66932254279484647441]⟩,
  ⟨103681, 11, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5]⟩,
  ⟨144481, 11, [2, 2, 2, 2, 2, 3, 5, 7, 43]⟩,
  ⟨11128427, 2, [2, 653, 8521]⟩
]

theorem lucasNodeBatch02_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix02) lucasNodeBatch02 = true := by
  decide +kernel

theorem lucasNodeBatch02_sound : ∀ c ∈ lucasNodeBatch02, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix02) lucasNodeBatch02
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix02 lucasNodePrefix02_sound) lucasNodeBatch02_check

def lucasNodePrefix03 : List LucasCertificate := lucasNodePrefix02 ++ lucasNodeBatch02

theorem lucasNodePrefix03_sound : ∀ c ∈ lucasNodePrefix03, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix03, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix02_sound c hc
  · exact lucasNodeBatch02_sound c hc

/-- Topological Lucas nodes, batch 3. -/
def lucasNodeBatch03 : List LucasCertificate := [
  ⟨10559, 23, [2, 5279]⟩,
  ⟨177962167367, 5, [2, 2069, 4073, 10559]⟩,
  ⟨63929, 3, [2, 2, 2, 61, 131]⟩,
  ⟨5114321, 3, [2, 2, 2, 2, 5, 63929]⟩,
  ⟨1266715025281, 11, [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 43, 5114321]⟩
]

theorem lucasNodeBatch03_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix03) lucasNodeBatch03 = true := by
  decide +kernel

theorem lucasNodeBatch03_sound : ∀ c ∈ lucasNodeBatch03, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix03) lucasNodeBatch03
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix03 lucasNodePrefix03_sound) lucasNodeBatch03_check

def lucasNodePrefix04 : List LucasCertificate := lucasNodePrefix03 ++ lucasNodeBatch03

theorem lucasNodePrefix04_sound : ∀ c ∈ lucasNodePrefix04, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix04, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix03_sound c hc
  · exact lucasNodeBatch03_sound c hc

/-- Topological Lucas nodes, batch 4. -/
def lucasNodeBatch04 : List LucasCertificate := [
  ⟨25644747487, 6, [2, 3, 17, 41, 823, 7451]⟩,
  ⟨66163448516461, 6, [2, 2, 3, 5, 43, 25644747487]⟩,
  ⟨529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369, 13, [2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 11, 17, 19, 23, 53, 107, 109, 431, 1291, 1721, 5779, 6263, 6709, 103681, 144481, 11128427, 177962167367, 1266715025281, 66163448516461]⟩,
  ⟨18229, 2, [2, 2, 3, 7, 7, 31]⟩,
  ⟨3010349, 2, [2, 2, 11, 31, 2207]⟩
]

theorem lucasNodeBatch04_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix04) lucasNodeBatch04 = true := by
  decide +kernel

theorem lucasNodeBatch04_sound : ∀ c ∈ lucasNodeBatch04, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix04) lucasNodeBatch04
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix04 lucasNodePrefix04_sound) lucasNodeBatch04_check

def lucasNodePrefix05 : List LucasCertificate := lucasNodePrefix04 ++ lucasNodeBatch04

theorem lucasNodePrefix05_sound : ∀ c ∈ lucasNodePrefix05, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix05, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix04_sound c hc
  · exact lucasNodeBatch04_sound c hc

/-- Topological Lucas nodes, batch 5. -/
def lucasNodeBatch05 : List LucasCertificate := [
  ⟨125024551, 6, [2, 3, 5, 5, 7, 23, 31, 167]⟩,
  ⟨72617, 3, [2, 2, 2, 29, 313]⟩,
  ⟨197082539, 2, [2, 23, 59, 72617]⟩,
  ⟨8792101, 6, [2, 2, 3, 3, 5, 5, 9769]⟩,
  ⟨2581290516793, 10, [2, 2, 2, 3, 13, 941, 8792101]⟩
]

theorem lucasNodeBatch05_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix05) lucasNodeBatch05 = true := by
  decide +kernel

theorem lucasNodeBatch05_sound : ∀ c ∈ lucasNodeBatch05, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix05) lucasNodeBatch05
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix05 lucasNodePrefix05_sound) lucasNodeBatch05_check

def lucasNodePrefix06 : List LucasCertificate := lucasNodePrefix05 ++ lucasNodeBatch05

theorem lucasNodePrefix06_sound : ∀ c ∈ lucasNodePrefix06, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix06, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix05_sound c hc
  · exact lucasNodeBatch05_sound c hc

/-- Topological Lucas nodes, batch 6. -/
def lucasNodeBatch06 : List LucasCertificate := [
  ⟨11260169813534893704769219, 2, [2, 3, 7, 17, 31, 197082539, 2581290516793]⟩,
  ⟨1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353, 5, [2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 17, 19, 23, 29, 53, 107, 109, 5779, 6263, 18229, 103681, 3010349, 11128427, 125024551, 177962167367, 11260169813534893704769219]⟩,
  ⟨12301, 2, [2, 2, 3, 5, 5, 41]⟩,
  ⟨14503, 3, [2, 3, 2417]⟩,
  ⟨18451, 3, [2, 3, 3, 5, 5, 41]⟩
]

theorem lucasNodeBatch06_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix06) lucasNodeBatch06 = true := by
  decide +kernel

theorem lucasNodeBatch06_sound : ∀ c ∈ lucasNodeBatch06, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix06) lucasNodeBatch06
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix06 lucasNodePrefix06_sound) lucasNodeBatch06_check

def lucasNodePrefix07 : List LucasCertificate := lucasNodePrefix06 ++ lucasNodeBatch06

theorem lucasNodePrefix07_sound : ∀ c ∈ lucasNodePrefix07, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix07, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix06_sound c hc
  · exact lucasNodeBatch06_sound c hc

/-- Topological Lucas nodes, batch 7. -/
def lucasNodeBatch07 : List LucasCertificate := [
  ⟨221401, 7, [2, 2, 2, 3, 3, 3, 5, 5, 41]⟩,
  ⟨15608701, 7, [2, 2, 3, 3, 3, 3, 5, 5, 41, 47]⟩,
  ⟨10745088481, 11, [2, 2, 2, 2, 2, 3, 3, 3, 5, 7, 7, 23, 2207]⟩,
  ⟨3467131047901, 2, [2, 2, 3, 3, 5, 5, 13, 41, 47, 61, 2521]⟩,
  ⟨63419, 2, [2, 37, 857]⟩
]

theorem lucasNodeBatch07_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix07) lucasNodeBatch07 = true := by
  decide +kernel

theorem lucasNodeBatch07_sound : ∀ c ∈ lucasNodeBatch07, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix07) lucasNodeBatch07
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix07 lucasNodePrefix07_sound) lucasNodeBatch07_check

def lucasNodePrefix08 : List LucasCertificate := lucasNodePrefix07 ++ lucasNodeBatch07

theorem lucasNodePrefix08_sound : ∀ c ∈ lucasNodePrefix08, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix08, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix07_sound c hc
  · exact lucasNodeBatch07_sound c hc

/-- Topological Lucas nodes, batch 8. -/
def lucasNodeBatch08 : List LucasCertificate := [
  ⟨126839, 11, [2, 63419]⟩,
  ⟨15474359, 17, [2, 61, 126839]⟩,
  ⟨1154149773784223, 5, [2, 41, 97, 9377, 15474359]⟩,
  ⟨3061719992484545030554313848083717208111285432353738497131674799321571238149015933442805665949, 6, [2, 2, 3, 7, 7, 11, 13, 19, 29, 31, 47, 101, 151, 181, 223, 281, 449, 541, 2207, 12301, 14503, 18451, 221401, 15608701, 10745088481, 3467131047901, 1154149773784223]⟩,
  ⟨27941, 2, [2, 2, 5, 11, 127]⟩
]

theorem lucasNodeBatch08_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix08) lucasNodeBatch08 = true := by
  decide +kernel

theorem lucasNodeBatch08_sound : ∀ c ∈ lucasNodeBatch08, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix08) lucasNodeBatch08
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix08 lucasNodePrefix08_sound) lucasNodeBatch08_check

def lucasNodePrefix09 : List LucasCertificate := lucasNodePrefix08 ++ lucasNodeBatch08

theorem lucasNodePrefix09_sound : ∀ c ∈ lucasNodePrefix09, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix09, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix08_sound c hc
  · exact lucasNodeBatch08_sound c hc

/-- Topological Lucas nodes, batch 9. -/
def lucasNodeBatch09 : List LucasCertificate := [
  ⟨53551, 3, [2, 3, 3, 5, 5, 7, 17]⟩,
  ⟨95881, 13, [2, 2, 2, 3, 5, 17, 47]⟩,
  ⟨487681, 22, [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 127]⟩,
  ⟨1158551, 7, [2, 5, 5, 17, 29, 47]⟩,
  ⟨12760031, 7, [2, 5, 17, 47, 1597]⟩
]

theorem lucasNodeBatch09_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix09) lucasNodeBatch09 = true := by
  decide +kernel

theorem lucasNodeBatch09_sound : ∀ c ∈ lucasNodeBatch09, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix09) lucasNodeBatch09
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix09 lucasNodePrefix09_sound) lucasNodeBatch09_check

def lucasNodePrefix10 : List LucasCertificate := lucasNodePrefix09 ++ lucasNodeBatch09

theorem lucasNodePrefix10_sound : ∀ c ∈ lucasNodePrefix10, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix10, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix09_sound c hc
  · exact lucasNodeBatch09_sound c hc

/-- Topological Lucas nodes, batch 10. -/
def lucasNodeBatch10 : List LucasCertificate := [
  ⟨13822681, 7, [2, 2, 2, 3, 5, 127, 907]⟩,
  ⟨19954241, 3, [2, 2, 2, 2, 2, 2, 5, 127, 491]⟩,
  ⟨31721, 11, [2, 2, 2, 5, 13, 61]⟩,
  ⟨63443, 2, [2, 31721]⟩,
  ⟨162716451241291, 3, [2, 3, 5, 17, 47, 67, 1597, 63443]⟩
]

theorem lucasNodeBatch10_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix10) lucasNodeBatch10 = true := by
  decide +kernel

theorem lucasNodeBatch10_sound : ∀ c ∈ lucasNodeBatch10, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix10) lucasNodeBatch10
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix10 lucasNodePrefix10_sound) lucasNodeBatch10_check

def lucasNodePrefix11 : List LucasCertificate := lucasNodePrefix10 ++ lucasNodeBatch10

theorem lucasNodePrefix11_sound : ∀ c ∈ lucasNodePrefix11, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix11, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix10_sound c hc
  · exact lucasNodeBatch10_sound c hc

/-- Topological Lucas nodes, batch 11. -/
def lucasNodeBatch11 : List LucasCertificate := [
  ⟨37951, 3, [2, 3, 5, 5, 11, 23]⟩,
  ⟨40639, 7, [2, 3, 13, 521]⟩,
  ⟨301267, 2, [2, 3, 3, 3, 7, 797]⟩,
  ⟨48972758453, 2, [2, 2, 40639, 301267]⟩,
  ⟨696006631028466526259, 6, [2, 7, 23, 1163, 37951, 48972758453]⟩
]

theorem lucasNodeBatch11_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix11) lucasNodeBatch11 = true := by
  decide +kernel

theorem lucasNodeBatch11_sound : ∀ c ∈ lucasNodeBatch11, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix11) lucasNodeBatch11
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix11 lucasNodePrefix11_sound) lucasNodeBatch11_check

def lucasNodePrefix12 : List LucasCertificate := lucasNodePrefix11 ++ lucasNodeBatch11

theorem lucasNodePrefix12_sound : ∀ c ∈ lucasNodePrefix12, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix12, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix11_sound c hc
  · exact lucasNodeBatch11_sound c hc

/-- Topological Lucas nodes, batch 12. -/
def lucasNodeBatch12 : List LucasCertificate := [
  ⟨5568053048227732210073, 3, [2, 2, 2, 696006631028466526259]⟩,
  ⟨10597999265301490732599643671505003412515860435409421932560009680142974347195483140293254396195769876129909, 2, [2, 2, 11, 31, 509, 919, 1021, 3469, 3571, 5081, 27941, 53551, 95881, 487681, 1158551, 12760031, 13822681, 19954241, 162716451241291, 5568053048227732210073]⟩,
  ⟨32491, 2, [2, 3, 3, 5, 19, 19]⟩,
  ⟨41611, 2, [2, 3, 5, 19, 73]⟩,
  ⟨95419, 3, [2, 3, 3, 3, 3, 19, 31]⟩
]

theorem lucasNodeBatch12_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix12) lucasNodeBatch12 = true := by
  decide +kernel

theorem lucasNodeBatch12_sound : ∀ c ∈ lucasNodeBatch12, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix12) lucasNodeBatch12
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix12 lucasNodePrefix12_sound) lucasNodeBatch12_check

def lucasNodePrefix13 : List LucasCertificate := lucasNodePrefix12 ++ lucasNodeBatch12

theorem lucasNodePrefix13_sound : ∀ c ∈ lucasNodePrefix13, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix13, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix12_sound c hc
  · exact lucasNodeBatch12_sound c hc

/-- Topological Lucas nodes, batch 13. -/
def lucasNodeBatch13 : List LucasCertificate := [
  ⟨2069101, 2, [2, 2, 3, 3, 5, 5, 11, 11, 19]⟩,
  ⟨2820403, 2, [2, 3, 3, 13, 17, 709]⟩,
  ⟨9799987, 3, [2, 3, 7, 353, 661]⟩,
  ⟨87382901, 3, [2, 2, 5, 5, 11, 19, 37, 113]⟩,
  ⟨119130001, 47, [2, 2, 2, 2, 3, 5, 5, 5, 5, 11, 19, 19]⟩
]

theorem lucasNodeBatch13_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix13) lucasNodeBatch13 = true := by
  decide +kernel

theorem lucasNodeBatch13_sound : ∀ c ∈ lucasNodeBatch13, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix13) lucasNodeBatch13
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix13 lucasNodePrefix13_sound) lucasNodeBatch13_check

def lucasNodePrefix14 : List LucasCertificate := lucasNodePrefix13 ++ lucasNodeBatch13

theorem lucasNodePrefix14_sound : ∀ c ∈ lucasNodePrefix14, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix14, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix13_sound c hc
  · exact lucasNodeBatch13_sound c hc

/-- Topological Lucas nodes, batch 14. -/
def lucasNodeBatch14 : List LucasCertificate := [
  ⟨411677941, 6, [2, 2, 3, 5, 19, 331, 1091]⟩,
  ⟨57134431, 6, [2, 3, 3, 3, 5, 61, 3469]⟩,
  ⟨35537616083, 2, [2, 311, 57134431]⟩,
  ⟨102013, 5, [2, 2, 3, 8501]⟩,
  ⟨46165371073, 7, [2, 2, 2, 2, 2, 2, 3, 2357, 102013]⟩
]

theorem lucasNodeBatch14_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix14) lucasNodeBatch14 = true := by
  decide +kernel

theorem lucasNodeBatch14_sound : ∀ c ∈ lucasNodeBatch14, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix14) lucasNodeBatch14
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix14 lucasNodePrefix14_sound) lucasNodeBatch14_check

def lucasNodePrefix15 : List LucasCertificate := lucasNodePrefix14 ++ lucasNodeBatch14

theorem lucasNodePrefix15_sound : ∀ c ∈ lucasNodePrefix15, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix15, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix14_sound c hc
  · exact lucasNodeBatch14_sound c hc

/-- Topological Lucas nodes, batch 15. -/
def lucasNodeBatch15 : List LucasCertificate := [
  ⟨688846502588399, 7, [2, 7, 11, 23, 29, 71, 911, 103681]⟩,
  ⟨36684474316080978061473613646275630451100586901195229815270242868417768061193560857904335017879540515228143777781065869, 6, [2, 2, 3, 11, 31, 191, 229, 283, 569, 571, 6673, 9349, 32491, 41611, 95419, 2069101, 2820403, 9799987, 87382901, 119130001, 411677941, 35537616083, 46165371073, 688846502588399]⟩,
  ⟨1957099, 2, [2, 3, 11, 13, 2281]⟩,
  ⟨2120119, 3, [2, 3, 7, 11, 13, 353]⟩,
  ⟨94079, 13, [2, 17, 2767]⟩
]

theorem lucasNodeBatch15_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix15) lucasNodeBatch15 = true := by
  decide +kernel

theorem lucasNodeBatch15_sound : ∀ c ∈ lucasNodeBatch15, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix15) lucasNodeBatch15
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix15 lucasNodePrefix15_sound) lucasNodeBatch15_check

def lucasNodePrefix16 : List LucasCertificate := lucasNodePrefix15 ++ lucasNodeBatch15

theorem lucasNodePrefix16_sound : ∀ c ∈ lucasNodePrefix16, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix16, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix15_sound c hc
  · exact lucasNodeBatch15_sound c hc

/-- Topological Lucas nodes, batch 16. -/
def lucasNodeBatch16 : List LucasCertificate := [
  ⟨1784714380021, 7, [2, 2, 3, 3, 5, 11, 11, 13, 67, 94079]⟩,
  ⟨64613, 2, [2, 2, 29, 557]⟩,
  ⟨5363137453, 2, [2, 2, 3, 6917, 64613]⟩,
  ⟨2917546774433, 3, [2, 2, 2, 2, 2, 17, 5363137453]⟩,
  ⟨1929584153756850496621, 2, [2, 2, 3, 5, 11, 13, 19, 4057, 2917546774433]⟩
]

theorem lucasNodeBatch16_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix16) lucasNodeBatch16 = true := by
  decide +kernel

theorem lucasNodeBatch16_sound : ∀ c ∈ lucasNodeBatch16, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix16) lucasNodeBatch16
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix16 lucasNodePrefix16_sound) lucasNodeBatch16_check

def lucasNodePrefix17 : List LucasCertificate := lucasNodePrefix16 ++ lucasNodeBatch16

theorem lucasNodePrefix17_sound : ∀ c ∈ lucasNodePrefix17, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix17, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix16_sound c hc
  · exact lucasNodeBatch16_sound c hc

/-- Topological Lucas nodes, batch 17. -/
def lucasNodeBatch17 : List LucasCertificate := [
  ⟨96041200618922553823942883360924865026104917411877067816822264789029014378308478864192589084185254331637646183008074629, 2, [2, 2, 11, 31, 89, 191, 199, 229, 233, 521, 571, 8581, 9349, 32491, 41611, 95419, 1957099, 2069101, 2120119, 87382901, 119130001, 411677941, 1784714380021, 1929584153756850496621]⟩
]

theorem lucasNodeBatch17_check : lucasCertificatesCheckAux lucasBasePrimes (lucasCertificateTargets lucasNodePrefix17) lucasNodeBatch17 = true := by
  decide +kernel

theorem lucasNodeBatch17_sound : ∀ c ∈ lucasNodeBatch17, c.modulus.Prime := by
  exact lucasCertificatesCheckAux_sound lucasBasePrimes (lucasCertificateTargets lucasNodePrefix17) lucasNodeBatch17
    lucasBasePrimes_sound (lucasCertificateTargets_sound lucasNodePrefix17 lucasNodePrefix17_sound) lucasNodeBatch17_check

def lucasNodePrefix18 : List LucasCertificate := lucasNodePrefix17 ++ lucasNodeBatch17

theorem lucasNodePrefix18_sound : ∀ c ∈ lucasNodePrefix18, c.modulus.Prime := by
  intro c hc
  simp only [lucasNodePrefix18, List.mem_append] at hc
  rcases hc with hc | hc
  · exact lucasNodePrefix17_sound c hc
  · exact lucasNodeBatch17_sound c hc

/-- Every prime factor node in the shared DAG has been certified. -/
theorem lucasAllNodes_sound : ∀ c ∈ lucasNodePrefix18, c.modulus.Prime := lucasNodePrefix18_sound

def lucasAllNodeTargets : List ℕ := lucasCertificateTargets lucasNodePrefix18

/-- Unified-DAG Lucas certificate for the prime value at index 359. -/
def lucasTarget359 : LucasCertificate := ⟨475420437734698220747368027166749382927701417016557193662268716376935476241, 14, [2, 2, 2, 2, 3, 3, 3, 5, 11, 17, 19, 31, 41, 61, 107, 181, 359, 541, 2521, 109441, 10783342081, 1066737847220321, 66932254279484647441]⟩

def lucasTargetKnown00 : List ℕ := lucasAllNodeTargets

theorem lucasTargetKnown00_sound : ∀ q ∈ lucasTargetKnown00, q.Prime := by
  exact lucasCertificateTargets_sound lucasNodePrefix18 lucasAllNodes_sound

theorem lucasTarget359_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown00) lucasTarget359 = true := by
  decide +kernel

theorem lucasTarget359_prime : lucasTarget359.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown00 lucasTarget359
    lucasBasePrimes_sound lucasTargetKnown00_sound lucasTarget359_check

/-- Unified-DAG Lucas certificate for the prime value at index 431. -/
def lucasTarget431 : LucasCertificate := ⟨529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369, 13, [2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 11, 17, 19, 23, 53, 107, 109, 431, 1291, 1721, 5779, 6263, 6709, 103681, 144481, 11128427, 177962167367, 1266715025281, 66163448516461]⟩

def lucasTargetKnown01 : List ℕ := lucasAllNodeTargets ++ [475420437734698220747368027166749382927701417016557193662268716376935476241]

theorem lucasTargetKnown01_sound : ∀ q ∈ lucasTargetKnown01, q.Prime := by
  intro q hq
  simp only [lucasTargetKnown01, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl
  · exact lucasTargetKnown00_sound q hq
  · exact lucasTarget359_prime

theorem lucasTarget431_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown01) lucasTarget431 = true := by
  decide +kernel

theorem lucasTarget431_prime : lucasTarget431.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown01 lucasTarget431
    lucasBasePrimes_sound lucasTargetKnown01_sound lucasTarget431_check

/-- Unified-DAG Lucas certificate for the prime value at index 433. -/
def lucasTarget433 : LucasCertificate := ⟨1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353, 5, [2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 17, 19, 23, 29, 53, 107, 109, 5779, 6263, 18229, 103681, 3010349, 11128427, 125024551, 177962167367, 11260169813534893704769219]⟩

def lucasTargetKnown02 : List ℕ := lucasAllNodeTargets ++ [475420437734698220747368027166749382927701417016557193662268716376935476241, 529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369]

theorem lucasTargetKnown02_sound : ∀ q ∈ lucasTargetKnown02, q.Prime := by
  intro q hq
  simp only [lucasTargetKnown02, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl
  · exact lucasTargetKnown01_sound q (List.mem_append_left _ hq)
  · exact lucasTarget359_prime
  · exact lucasTarget431_prime

theorem lucasTarget433_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown02) lucasTarget433 = true := by
  decide +kernel

theorem lucasTarget433_prime : lucasTarget433.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown02 lucasTarget433
    lucasBasePrimes_sound lucasTargetKnown02_sound lucasTarget433_check

/-- Unified-DAG Lucas certificate for the prime value at index 449. -/
def lucasTarget449 : LucasCertificate := ⟨3061719992484545030554313848083717208111285432353738497131674799321571238149015933442805665949, 6, [2, 2, 3, 7, 7, 11, 13, 19, 29, 31, 47, 101, 151, 181, 223, 281, 449, 541, 2207, 12301, 14503, 18451, 221401, 15608701, 10745088481, 3467131047901, 1154149773784223]⟩

def lucasTargetKnown03 : List ℕ := lucasAllNodeTargets ++ [475420437734698220747368027166749382927701417016557193662268716376935476241, 529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369, 1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353]

theorem lucasTargetKnown03_sound : ∀ q ∈ lucasTargetKnown03, q.Prime := by
  intro q hq
  simp only [lucasTargetKnown03, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl | rfl
  · exact lucasTargetKnown02_sound q (List.mem_append_left _ hq)
  · exact lucasTarget359_prime
  · exact lucasTarget431_prime
  · exact lucasTarget433_prime

theorem lucasTarget449_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown03) lucasTarget449 = true := by
  decide +kernel

theorem lucasTarget449_prime : lucasTarget449.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown03 lucasTarget449
    lucasBasePrimes_sound lucasTargetKnown03_sound lucasTarget449_check

/-- Unified-DAG Lucas certificate for the prime value at index 509. -/
def lucasTarget509 : LucasCertificate := ⟨10597999265301490732599643671505003412515860435409421932560009680142974347195483140293254396195769876129909, 2, [2, 2, 11, 31, 509, 919, 1021, 3469, 3571, 5081, 27941, 53551, 95881, 487681, 1158551, 12760031, 13822681, 19954241, 162716451241291, 5568053048227732210073]⟩

def lucasTargetKnown04 : List ℕ := lucasAllNodeTargets ++ [475420437734698220747368027166749382927701417016557193662268716376935476241, 529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369, 1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353, 3061719992484545030554313848083717208111285432353738497131674799321571238149015933442805665949]

theorem lucasTargetKnown04_sound : ∀ q ∈ lucasTargetKnown04, q.Prime := by
  intro q hq
  simp only [lucasTargetKnown04, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl
  · exact lucasTargetKnown03_sound q (List.mem_append_left _ hq)
  · exact lucasTarget359_prime
  · exact lucasTarget431_prime
  · exact lucasTarget433_prime
  · exact lucasTarget449_prime

theorem lucasTarget509_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown04) lucasTarget509 = true := by
  decide +kernel

theorem lucasTarget509_prime : lucasTarget509.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown04 lucasTarget509
    lucasBasePrimes_sound lucasTargetKnown04_sound lucasTarget509_check

/-- Unified-DAG Lucas certificate for the prime value at index 569. -/
def lucasTarget569 : LucasCertificate := ⟨36684474316080978061473613646275630451100586901195229815270242868417768061193560857904335017879540515228143777781065869, 6, [2, 2, 3, 11, 31, 191, 229, 283, 569, 571, 6673, 9349, 32491, 41611, 95419, 2069101, 2820403, 9799987, 87382901, 119130001, 411677941, 35537616083, 46165371073, 688846502588399]⟩

def lucasTargetKnown05 : List ℕ := lucasAllNodeTargets ++ [475420437734698220747368027166749382927701417016557193662268716376935476241, 529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369, 1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353, 3061719992484545030554313848083717208111285432353738497131674799321571238149015933442805665949, 10597999265301490732599643671505003412515860435409421932560009680142974347195483140293254396195769876129909]

theorem lucasTargetKnown05_sound : ∀ q ∈ lucasTargetKnown05, q.Prime := by
  intro q hq
  simp only [lucasTargetKnown05, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl | rfl
  · exact lucasTargetKnown04_sound q (List.mem_append_left _ hq)
  · exact lucasTarget359_prime
  · exact lucasTarget431_prime
  · exact lucasTarget433_prime
  · exact lucasTarget449_prime
  · exact lucasTarget509_prime

theorem lucasTarget569_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown05) lucasTarget569 = true := by
  decide +kernel

theorem lucasTarget569_prime : lucasTarget569.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown05 lucasTarget569
    lucasBasePrimes_sound lucasTargetKnown05_sound lucasTarget569_check

/-- Unified-DAG Lucas certificate for the prime value at index 571. -/
def lucasTarget571 : LucasCertificate := ⟨96041200618922553823942883360924865026104917411877067816822264789029014378308478864192589084185254331637646183008074629, 2, [2, 2, 11, 31, 89, 191, 199, 229, 233, 521, 571, 8581, 9349, 32491, 41611, 95419, 1957099, 2069101, 2120119, 87382901, 119130001, 411677941, 1784714380021, 1929584153756850496621]⟩

def lucasTargetKnown06 : List ℕ := lucasAllNodeTargets ++ [475420437734698220747368027166749382927701417016557193662268716376935476241, 529892711006095621792039556787784670197112759029534506620905162834769955134424689676262369, 1387277127804783827114186103186246392258450358171783690079918032136025225954602593712568353, 3061719992484545030554313848083717208111285432353738497131674799321571238149015933442805665949, 10597999265301490732599643671505003412515860435409421932560009680142974347195483140293254396195769876129909, 36684474316080978061473613646275630451100586901195229815270242868417768061193560857904335017879540515228143777781065869]

theorem lucasTargetKnown06_sound : ∀ q ∈ lucasTargetKnown06, q.Prime := by
  intro q hq
  simp only [lucasTargetKnown06, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lucasTargetKnown05_sound q (List.mem_append_left _ hq)
  · exact lucasTarget359_prime
  · exact lucasTarget431_prime
  · exact lucasTarget433_prime
  · exact lucasTarget449_prime
  · exact lucasTarget509_prime
  · exact lucasTarget569_prime

theorem lucasTarget571_check : lucasStepCheck (lucasBasePrimes ++ lucasTargetKnown06) lucasTarget571 = true := by
  decide +kernel

theorem lucasTarget571_prime : lucasTarget571.modulus.Prime := by
  exact lucasStepCheck_sound lucasBasePrimes lucasTargetKnown06 lucasTarget571
    lucasBasePrimes_sound lucasTargetKnown06_sound lucasTarget571_check

theorem fibValue359 : Nat.fib 359 = lucasTarget359.modulus := by
  decide +kernel

theorem fibValue359_prime : Nat.Prime (Nat.fib 359) := by
  rw [fibValue359]
  exact lucasTarget359_prime

theorem fibValue431 : Nat.fib 431 = lucasTarget431.modulus := by
  decide +kernel

theorem fibValue431_prime : Nat.Prime (Nat.fib 431) := by
  rw [fibValue431]
  exact lucasTarget431_prime

theorem fibValue433 : Nat.fib 433 = lucasTarget433.modulus := by
  decide +kernel

theorem fibValue433_prime : Nat.Prime (Nat.fib 433) := by
  rw [fibValue433]
  exact lucasTarget433_prime

theorem fibValue449 : Nat.fib 449 = lucasTarget449.modulus := by
  decide +kernel

theorem fibValue449_prime : Nat.Prime (Nat.fib 449) := by
  rw [fibValue449]
  exact lucasTarget449_prime

theorem fibValue509 : Nat.fib 509 = lucasTarget509.modulus := by
  decide +kernel

theorem fibValue509_prime : Nat.Prime (Nat.fib 509) := by
  rw [fibValue509]
  exact lucasTarget509_prime

theorem fibValue569 : Nat.fib 569 = lucasTarget569.modulus := by
  decide +kernel

theorem fibValue569_prime : Nat.Prime (Nat.fib 569) := by
  rw [fibValue569]
  exact lucasTarget569_prime

theorem fibValue571 : Nat.fib 571 = lucasTarget571.modulus := by
  decide +kernel

theorem fibValue571_prime : Nat.Prime (Nat.fib 571) := by
  rw [fibValue571]
  exact lucasTarget571_prime

def fibPrimeIndicesCoreThrough1000 : List ℕ :=
  [3, 4, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83, 131, 137]

def fibPrimeIndicesThrough1000 : List ℕ :=
  fibPrimeIndicesCoreThrough1000 ++ furtherPrimeCandidates

/-- Complete classification of prime Fibonacci values through index 1000. -/
theorem fib_prime_indices_through_1000 (n : ℕ) (hn : n ≤ 1000) :
    (Nat.fib n).Prime ↔ n ∈ fibPrimeIndicesThrough1000 := by
  constructor
  · intro hp
    by_cases h137 : n ≤ 137
    · have hs := (fib_prime_indices_through_137 n h137).mp hp
      have hcore : n ∈ fibPrimeIndicesCoreThrough1000 := by
        rcases hs with hsmall | h131 | h137eq
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsmall
          simp only [fibPrimeIndicesCoreThrough1000, List.mem_cons, List.not_mem_nil, or_false]
          omega
        · simp [fibPrimeIndicesCoreThrough1000, h131]
        · simp [fibPrimeIndicesCoreThrough1000, h137eq]
      exact List.mem_append_left _ hcore
    · have hcand := fibPrimeCandidatesThrough1000 (by omega) hn hp
      exact List.mem_append_right _ (by simpa [furtherPrimeCandidates] using hcand)
  · intro hmem
    simp only [fibPrimeIndicesThrough1000] at hmem
    rcases List.mem_append.mp hmem with hcore | hcand
    · have hs : n ∈ [3, 4, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83] ∨ n = 131 ∨ n = 137 := by
        simp only [fibPrimeIndicesCoreThrough1000, List.mem_cons, List.not_mem_nil, or_false] at hcore
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcore ⊢
        omega
      have hn137 : n ≤ 137 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        omega
      exact (fib_prime_indices_through_137 n hn137).mpr hs
    · simp only [furtherPrimeCandidates, List.mem_cons, List.not_mem_nil, or_false] at hcand
      rcases hcand with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fibValue359_prime
      · exact fibValue431_prime
      · exact fibValue433_prime
      · exact fibValue449_prime
      · exact fibValue509_prime
      · exact fibValue569_prime
      · exact fibValue571_prime

end MathGacha
