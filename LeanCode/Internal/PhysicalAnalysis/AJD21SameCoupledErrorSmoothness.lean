import AJD20SameActualOffDiagonalOrbits
import AIZ6SameCoupledInverseOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2
open Grad.AnnularPhysicalSolution Grad.GaugeCoefficients.Physical.Allocation

theorem hilbertOffDiagonal_contDiff {P H E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (upper : P → E →L[ℂ] H) (lower : P → H →L[ℂ] E)
    (upperSmooth : ContDiff ℝ ∞ upper) (lowerSmooth : ContDiff ℝ ∞ lower) :
    ContDiff ℝ ∞ (fun point => hilbertOffDiagonal (upper point) (lower point)) :=
  hilbertOperatorPair_contDiff _ _
    (complexOperatorComposition_contDiff _ _ upperSmooth contDiff_const)
    (complexOperatorComposition_contDiff _ _ lowerSmooth contDiff_const)

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule crossHighRealNormed crossHighRealModule
  crossResponseRealNormed crossResponseRealModule lowToHighOperatorRealNormed highToLowOperatorRealNormed
  highOffDiagonalRealNormed lowOffDiagonalRealNormed

local instance coupledNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CoupledSpace lower L positive lengthPositive) := inferInstance
local instance coupledSeminormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    SeminormedAddCommGroup (CoupledSpace lower L positive lengthPositive) :=
  (coupledNormed lower L positive lengthPositive).toSeminormedAddCommGroup
local instance coupledComplexNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℂ (CoupledSpace lower L positive lengthPositive) := inferInstance
local instance coupledComplexModule (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℂ (CoupledSpace lower L positive lengthPositive) := (coupledComplexNormed lower L positive lengthPositive).toModule
local instance coupledRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CoupledSpace lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CoupledSpace lower L positive lengthPositive)
local instance coupledRealModule (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℝ (CoupledSpace lower L positive lengthPositive) := (coupledRealNormed lower L positive lengthPositive).toModule
local instance coupledOperatorRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CoupledSpace lower L positive lengthPositive →L[ℂ] CoupledSpace lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CoupledSpace lower L positive lengthPositive →L[ℂ] CoupledSpace lower L positive lengthPositive)
local instance coupledOperatorRealModule (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℝ (CoupledSpace lower L positive lengthPositive →L[ℂ] CoupledSpace lower L positive lengthPositive) :=
  (coupledOperatorRealNormed lower L positive lengthPositive).toModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (lengthPositive : 0 < L)
  (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
  (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- Exact equality with the already accepted original coupled error orbit. -/
theorem coupledOrbitError_assembly (tau : OrbitParameter) :
    coupledOrbitError parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau =
      hilbertOffDiagonal
        (actualHighOffDiagonalOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau)
        (actualLowOffDiagonalOrbit parameters L compact lower lengthPositive positive lowerHalf state tau) := by
  apply ContinuousLinearMap.ext
  intro field
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (CrossHighSpace lower L positive lengthPositive) (lowEnergyGraph lower L positive)).injective
  apply Prod.ext
  · exact (actualHighOffDiagonalOrbit_apply parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau field.ofLp.2).symm
  · exact (actualLowOffDiagonalOrbit_apply parameters L compact lower lengthPositive positive lowerHalf state tau field.ofLp.1).symm

/-- Genuine operator-norm smoothness of the SAME AIZ coupled error, on the original B8 ball. -/
theorem coupledOrbitError_contDiff :
    ContDiff ℝ ∞ (coupledOrbitError parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small) := by
  have same := funext (coupledOrbitError_assembly parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
  rw [same]
  exact hilbertOffDiagonal_contDiff _ _
    (actualHighOffDiagonalOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    (actualLowOffDiagonalOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf state small)

end Grad.AnnularCrossOrbit
