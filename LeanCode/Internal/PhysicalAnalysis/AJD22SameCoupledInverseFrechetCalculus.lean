import AJD21SameCoupledErrorSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2
open Grad.AnnularPhysicalSolution Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule crossHighRealNormed crossHighRealModule
  crossResponseRealNormed crossResponseRealModule lowToHighOperatorRealNormed highToLowOperatorRealNormed
  highOffDiagonalRealNormed lowOffDiagonalRealNormed

attribute [local instance] coupledNormed coupledSeminormed coupledComplexNormed coupledComplexModule
  coupledRealNormed coupledRealModule coupledOperatorRealNormed coupledOperatorRealModule
open Grad.AnnularInverseCalculus

variable (parameters : PhaseParameters) (L compact lower : ℝ) (lengthPositive : 0 < L)
  (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
  (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- The SAME actual residual, using the already accepted original coupled error orbit. -/
def coupledResidualOrbit (tau : OrbitParameter) :
    CoupledSpace lower L positive lengthPositive →L[ℂ] CoupledSpace lower L positive lengthPositive :=
  ContinuousLinearMap.id ℂ (CoupledSpace lower L positive lengthPositive) -
    coupledOrbitError parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau

theorem coupledResidualOrbit_contDiff :
    ContDiff ℝ ∞ (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small) :=
  contDiff_const.sub (coupledOrbitError_contDiff parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)

theorem coupledResidualOrbit_inverse_right (tau : OrbitParameter) :
    (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau).comp
      (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau) =
    ContinuousLinearMap.id ℂ (CoupledSpace lower L positive lengthPositive) := by
  apply ContinuousLinearMap.ext
  intro field
  exact coupledOrbitInverse_right parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field

theorem coupledResidualOrbit_inverse_left (tau : OrbitParameter) :
    (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau).comp
      (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau) =
    ContinuousLinearMap.id ℂ (CoupledSpace lower L positive lengthPositive) := by
  apply ContinuousLinearMap.ext
  intro field
  exact coupledOrbitInverse_left parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field

/-- All genuine operator-norm derivatives of the SAME inverse exist on the unchanged primitive ball. -/
theorem coupledOrbitInverse_contDiff :
    ContDiff ℝ ∞ (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small) :=
  sameInverse_contDiff (𝕜 := ℂ) (P := OrbitParameter)
    (E := CoupledSpace lower L positive lengthPositive) (F := CoupledSpace lower L positive lengthPositive)
    (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledResidualOrbit_inverse_right parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledResidualOrbit_inverse_left parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledResidualOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)

def coupledInverseOrbitDerivative (tau : OrbitParameter) :
    OrbitParameter →L[ℝ] (CoupledSpace lower L positive lengthPositive →L[ℂ] CoupledSpace lower L positive lengthPositive) :=
  (inverseSandwich (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau)).comp
    (fderiv ℝ (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small) tau)

/-- The derivative is the true -J(dA)J sandwich, retaining the original complex-linear operators. -/
theorem coupledOrbitInverse_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt
      (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small)
      (coupledInverseOrbitDerivative parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau) tau :=
  sameInverse_hasFDerivAt (𝕜 := ℂ) (P := OrbitParameter)
    (E := CoupledSpace lower L positive lengthPositive) (F := CoupledSpace lower L positive lengthPositive)
    (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledResidualOrbit_inverse_right parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledResidualOrbit_inverse_left parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
    tau _ ((coupledResidualOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small).differentiable
      (by simp)).differentiableAt.hasFDerivAt

theorem coupledInverseOrbitDerivative_apply (tau step : OrbitParameter) :
    coupledInverseOrbitDerivative parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau step =
      -(coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau).comp
        ((fderiv ℝ (coupledResidualOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small) tau step).comp
          (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau)) := rfl

end Grad.AnnularCrossOrbit
