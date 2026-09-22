import GQF1LiteralRows

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace
open Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev SmoothCapSource (L sigma gamma ell : ℝ) :=
  APSmooth L sigma gamma ell 2 × (APSmooth L sigma gamma ell 1 × APSmooth L sigma gamma ell 1)

abbrev CapSourceAmbient (L sigma gamma ell : ℝ) (grade : ℕ) :=
  WithLp 2 (apGrade L sigma gamma ell 2 (grade + 1) ×
    WithLp 2 (apGrade L sigma gamma ell 1 grade × apGrade L sigma gamma ell 1 (grade + 1)))

abbrev CapAugmentedAmbient (L sigma gamma ell : ℝ) (grade : ℕ) :=
  WithLp 2 (CapSourceAmbient L sigma gamma ell grade × APBoundaryGrade L sigma gamma ell 1 (grade + 1))

instance capSourceNormedSpace (L sigma gamma ell : ℝ) (grade : ℕ) :
    NormedSpace ℂ (CapSourceAmbient L sigma gamma ell grade) := by
  unfold CapSourceAmbient
  infer_instance

instance capAugmentedNormedSpace (L sigma gamma ell : ℝ) (grade : ℕ) :
    NormedSpace ℂ (CapAugmentedAmbient L sigma gamma ell grade) := by
  unfold CapAugmentedAmbient
  infer_instance

def hilbertPairLinear {E F G : Type*} [AddCommMonoid E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (first : E →ₗ[ℂ] F) (second : E →ₗ[ℂ] G) : E →ₗ[ℂ] WithLp 2 (F × G) where
  toFun value := WithLp.toLp 2 (first value, second value)
  map_add' firstValue secondValue :=
    congrArg (WithLp.toLp 2) (Prod.ext (first.map_add firstValue secondValue) (second.map_add firstValue secondValue))
  map_smul' scalar value :=
    congrArg (WithLp.toLp 2) (Prod.ext (first.map_smul scalar value) (second.map_smul scalar value))

variable {L sigma gamma ell : ℝ}

def capSourceGrade (grade : ℕ) :
    SmoothCapSource L sigma gamma ell →ₗ[ℂ] CapSourceAmbient L sigma gamma ell grade :=
  hilbertPairLinear ((apSmoothGrade L sigma gamma ell 2 (grade + 1)).comp (LinearMap.fst ℂ _ _))
    (hilbertPairLinear
      ((apSmoothGrade L sigma gamma ell 1 grade).comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)))
      ((apSmoothGrade L sigma gamma ell 1 (grade + 1)).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))

def apSmoothCurl (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 2) (output := 1) 0 1)).comp
      (apSmoothPartial admissible 2 0) -
    (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 2) (output := 1) 0 0)).comp
      (apSmoothPartial admissible 2 1)

/-- The actual smooth AM9 source constraints, with no condition on the
determinant first jet. The scalar value in the last factor is already forced
by its mean, and is included in the accepted zero-first-jet vocabulary. -/
def smoothCapSourceCore (admissible : Admissible L sigma gamma ell) :
    Submodule ℂ (SmoothCapSource L sigma gamma ell) :=
  (LinearMap.ker (apSmoothQrad L sigma gamma ell - LinearMap.id) ⊓
    apSmoothAxisValues admissible 2 ⊓
    (apSmoothAxisValues admissible 1).comap (apSmoothCurl admissible)).comap (LinearMap.fst ℂ _ _) ⊓
  (apSmoothMeanFree admissible).comap ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)) ⊓
  (apSmoothMeanFree admissible ⊓ apSmoothAxisFirsts admissible 1).comap
    ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))

/-- Closure of the specified smooth source, not a maximal PDE domain. -/
def capSourceClosure (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    Submodule ℂ (CapSourceAmbient L sigma gamma ell grade) :=
  (LinearMap.range ((capSourceGrade grade).comp (smoothCapSourceCore admissible).subtype)).topologicalClosure

def circularRows (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] SmoothCapSource L sigma gamma ell :=
  (circularForce admissible).prod ((circularDeterminant admissible).prod (circularThird admissible))

def actualRows (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] SmoothCapSource L sigma gamma ell :=
  (actualForce admissible data coherent).prod
    ((actualDeterminant admissible data coherent).prod (actualThird admissible data coherent))

def circularCoreTrace (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  (apHighTrace L sigma gamma ell (grade + 1) (by omega)).toLinearMap.comp
    ((apSmoothGrade L sigma gamma ell 1 (grade + 1)).comp
      ((apSmoothRadial admissible).comp (compensatedReconstruct admissible)))

def actualCoreTrace (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  (apHighTrace L sigma gamma ell (grade + 1) (by omega)).toLinearMap.comp
    ((apSmoothGrade L sigma gamma ell 1 (grade + 1)).comp
      ((apSmoothMultiplier admissible (normalRowFamily data) (normalRowFamily_coherent data coherent)).comp
        (compensatedReconstruct admissible)))

def circularAugmentedCore (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] CapAugmentedAmbient L sigma gamma ell grade :=
  hilbertPairLinear ((capSourceGrade grade).comp (circularRows admissible)) (circularCoreTrace admissible grade)

def actualAugmentedCore (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] CapAugmentedAmbient L sigma gamma ell grade :=
  hilbertPairLinear ((capSourceGrade grade).comp (actualRows admissible data coherent))
    (actualCoreTrace admissible data coherent grade)

end Grad.GaugeCoefficients.Physical.Compensated
