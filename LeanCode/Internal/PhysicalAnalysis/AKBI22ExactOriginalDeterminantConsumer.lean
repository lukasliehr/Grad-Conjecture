import AKBI21LiteralOriginalCofactorField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

/-- Actual original Cartesian adjugate divergence is the literal three-term
determinant variation. No annular equation or artificial derivative occurs. -/
theorem originalActualCofactorField_literalDeterminant (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (state : QuotientState parameters) (sameBase : state.2.1=planarReferenceCore parameters+base)
    (sameEpsilon : state.1=(epsilon : ℂ)) (vector : ACore parameters 3)
    (point : SpatialCell) (inside : point∈openUnitCylinder) :
    let closed := (diskCellPoint point (openCylinderMembershipClosed point inside)).1
    (length : ℂ)*(fderiv ℝ (originalActualCofactorField parameters length epsilon base vector) point (spatialCellBasis 0) 0+
      fderiv ℝ (originalActualCofactorField parameters length epsilon base vector) point (spatialCellBasis 1) 1)+
      fderiv ℝ (originalActualCofactorField parameters length epsilon base vector) point (spatialCellBasis 2) 2=
    Grad.NonlinearQuotient.complexDeterminant (coreValue (partialCore parameters 0 vector) closed (point 2))
      (coreValue (partialCore parameters 1 state.2.1) closed (point 2)) (coreValue (affineStateCore parameters length state) closed (point 2))+
    Grad.NonlinearQuotient.complexDeterminant (coreValue (partialCore parameters 0 state.2.1) closed (point 2))
      (coreValue (partialCore parameters 1 vector) closed (point 2)) (coreValue (affineStateCore parameters length state) closed (point 2))+
    Grad.NonlinearQuotient.complexDeterminant (coreValue (partialCore parameters 0 state.2.1) closed (point 2))
      (coreValue (partialCore parameters 1 state.2.1) closed (point 2)) (coreValue (physicalVariationAffine state.1 vector) closed (point 2)) := by
  dsimp only
  rw [originalActualCofactorField_divergence parameters length rho epsilon nonzero base small state sameBase sameEpsilon vector point inside,
    originalCartesianCofactorDivergence parameters length nonzero,coreValue_add,coreValue_add]
  simp only [PiLp.add_apply,coreValue_determinantOperation]

end Grad.OriginalKernelHomogeneousGraph
