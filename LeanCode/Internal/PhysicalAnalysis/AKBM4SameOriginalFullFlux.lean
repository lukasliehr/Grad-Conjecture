import AKBM3SameOriginalSevenCovariant
import AKBD26SameCartesianSignedCofactorFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.NonlinearRange
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.Constraints Grad.Cor18
open Grad.OriginalKernelCovariantRecovery Grad.AnnularPhysicalReconstruction Grad.ActualDeterminantEquations
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift

variable (parameters : PhaseParameters) (compact : ℝ) (nonzero : parameters.length≠0)
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)
    (radius : Icc lower (1 : ℝ))

include nonzero sameBase sameEpsilon constrained homogeneous


/-- The SAME full seven-slot reconstruction equals the original smooth
polar covariant on every closed collar, including its two endpoints. -/
theorem originalHomogeneous_sevenCovariantFullField (angles : ℝ×ℝ) :
    ((originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar).covariant
        parameters parameters.length compact lower positive bounded state.val).fullField bounded (radius.val,angles)=
    (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector).fullField bounded (radius.val,angles) := by
  apply originalCurveFullField_eq_of_negative _ _ bounded radius _ angles
  rw [originalKernelSevenCurves_covariant]
  exact (originalHomogeneous_covariantRecovery parameters compact nonzero state small insideSeed lower positive bounded
    physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius).symm

/-- Literal B_C F_C^T U, recovered from the SAME original seven fields. -/
theorem originalHomogeneous_sevenCartesianFlux (angles : ℝ×ℝ) :
    (samePolarCofactorVector parameters parameters.length compact lower positive bounded state
      (originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar)).cartesianCovariant.fullField bounded (radius.val,angles)=
    coreValue (originalCartesianCofactorFluxCore parameters.length physicalState vector)
      (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) angles.2 := by
  rw [sameCartesianCofactorFlux_literal (inside := radius.property),originalHomogeneous_sevenCovariantFullField parameters compact nonzero state small
    insideSeed lower positive bounded physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius angles,
    originalPolarCovariantCurves_fullField parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded vector radius.val radius.property angles,
    originalPolarCovariantValue_inverse]
  exact originalCartesianCofactorFlux_value parameters parameters.length state.val.val.rho state.val.val.epsilon nonzero
    state.val.val.field state.val.val.low physicalState sameBase sameEpsilon vector _ _

end Grad.OriginalKernelHomogeneousGraph
