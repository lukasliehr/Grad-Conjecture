import AJD13SameOriginalCrossFluxOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution

def hilbertOperatorPair {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (first : X →L[ℂ] E) (second : X →L[ℂ] F) : X →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp (first.prod second)

theorem hilbertOperatorPair_contDiff {P X E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (first : P → X →L[ℂ] E) (second : P → X →L[ℂ] F)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ (fun point => hilbertOperatorPair (first point) (second point)) := by
  have composed := (ContinuousLinearMap.prodL (𝕜 := ℂ) (E := X) (F := E) (G := F) ℝ).contDiff.comp
    (firstSmooth.prodMk secondSmooth)
  have same : (fun point => (ContinuousLinearMap.prodL (𝕜 := ℂ) (E := X) (F := E) (G := F) ℝ) (first point, second point)) =
      (fun point => (first point).prod (second point)) := by
    funext point
    apply ContinuousLinearMap.ext
    intro field
    rfl
  simp only [Function.comp_def] at composed
  rw [same] at composed
  have paired : ContDiff ℝ ∞ (fun point => (first point).prod (second point)) := composed
  exact complexOperatorComposition_contDiff _ _ contDiff_const paired

local instance crossHighNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CrossHighSpace lower L positive lengthPositive) := inferInstance
local instance crossHighSeminormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    SeminormedAddCommGroup (CrossHighSpace lower L positive lengthPositive) :=
  (crossHighNormed lower L positive lengthPositive).toSeminormedAddCommGroup
local instance crossHighComplexNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℂ (CrossHighSpace lower L positive lengthPositive) := inferInstance
local instance crossHighComplexModule (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℂ (CrossHighSpace lower L positive lengthPositive) :=
  (crossHighComplexNormed lower L positive lengthPositive).toModule

local instance crossHighRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighSpace lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighSpace lower L positive lengthPositive)
local instance crossHighRealModule (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℝ (CrossHighSpace lower L positive lengthPositive) :=
  (crossHighRealNormed lower L positive lengthPositive).toModule

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

local instance crossResponseRealNormed (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighData parameters lower →L[ℂ] CrossHighSpace lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighData parameters lower →L[ℂ] CrossHighSpace lower L positive lengthPositive)
local instance crossResponseRealModule (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℝ (CrossHighData parameters lower →L[ℂ] CrossHighSpace lower L positive lengthPositive) :=
  (crossResponseRealNormed parameters lower L positive lengthPositive).toModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Literal conjugation of the SAME complete physical W × Domega cross response. -/
def actualHighCrossResponseOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℂ] CrossHighSpace lower L positive lengthPositive :=
  (highTranslationEquivalence lower L positive lengthPositive tau).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
      (crossDataTranslation parameters lower (-tau)))

theorem actualHighCrossResponseOrbit_pair (tau : OrbitParameter) :
    actualHighCrossResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau =
      hilbertOperatorPair
        (crossEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
        (crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau) := by
  apply ContinuousLinearMap.ext
  intro datum
  change WithLp.toLp 2
    (energyTranslation lower L positive tau
      (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (crossDataTranslation parameters lower (-tau) datum)),
     crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum) =
    WithLp.toLp 2
      (crossEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum,
       crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum)
  exact congrArg (fun energy => WithLp.toLp 2
      (energy, crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum))
    (crossEnergyOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum).symm

/-- Genuine operator-norm smoothness in BOTH original high graph coordinates. -/
theorem actualHighCrossResponseOrbit_contDiff :
    ContDiff ℝ ∞ (actualHighCrossResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) := by
  have same := funext (actualHighCrossResponseOrbit_pair parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
  rw [same]
  exact hilbertOperatorPair_contDiff _ _
    (crossEnergyOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (crossFluxOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

end Grad.AnnularCrossOrbit
