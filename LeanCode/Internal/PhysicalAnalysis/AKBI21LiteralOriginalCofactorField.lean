import AKBI20ActualCartesianCofactorDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter
open scoped BigOperators Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarCoefficients

/-- The literal original signed-cofactor flux in Cartesian coordinates.
The exterior value only totalizes the ambient function. -/
def originalActualCofactorField (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (point : SpatialCell) : ComplexEuclidean 3 := by
  classical
  exact if inside : point∈openUnitCylinder then
    let closed := (diskCellPoint point (openCylinderMembershipClosed point inside)).1
    WithLp.toLp 2 ((originalPhysicalSignedCofactor parameters length epsilon base (point 2) closed).mulVec
      ((originalPhysicalFrameMatrix parameters length epsilon base (point 2) closed).transpose.mulVec
        (coreValue vector closed (point 2))))
  else 0

variable (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (state : QuotientState parameters) (sameBase : state.2.1=planarReferenceCore parameters+base)
    (sameEpsilon : state.1=(epsilon : ℂ)) (vector : ACore parameters 3)
    (point : SpatialCell) (inside : point∈openUnitCylinder)

include nonzero small sameBase sameEpsilon inside

theorem originalActualCofactorField_same :
    originalActualCofactorField parameters length epsilon base vector=ᶠ[𝓝 point]
      originalCoreCartesianLift parameters (originalCartesianCofactorFluxCore length state vector) := by
  filter_upwards [openUnitCylinder_isOpen.mem_nhds inside] with query included
  rw [originalActualCofactorField,dif_pos included,originalCoreCartesianLift_value parameters _ query included]
  exact originalCartesianCofactorFlux_value parameters length rho epsilon nonzero base small state sameBase sameEpsilon vector _ _

theorem originalActualCofactorField_hasFDerivAt :
    HasFDerivAt (originalActualCofactorField parameters length epsilon base vector)
      (fderiv ℝ (originalCoreCartesianLift parameters (originalCartesianCofactorFluxCore length state vector)) point) point :=
  (originalCoreCartesianLift_hasFDerivAt parameters _ point inside).congr_of_eventuallyEq
    (originalActualCofactorField_same parameters length rho epsilon nonzero base small state sameBase sameEpsilon vector point inside)

/-- Genuine Frechet divergence of the literal SAME B_C F_C^T U, with
all three original L,L,1 contractions present. -/
theorem originalActualCofactorField_divergence :
    (length : ℂ)*(fderiv ℝ (originalActualCofactorField parameters length epsilon base vector) point (spatialCellBasis 0) 0+
      fderiv ℝ (originalActualCofactorField parameters length epsilon base vector) point (spatialCellBasis 1) 1)+
      fderiv ℝ (originalActualCofactorField parameters length epsilon base vector) point (spatialCellBasis 2) 2=
    coreValue (originalCartesianDivergenceCore length (originalCartesianCofactorFluxCore length state vector))
      (diskCellPoint point (openCylinderMembershipClosed point inside)).1 (point 2) 0 := by
  rw [(originalActualCofactorField_hasFDerivAt parameters length rho epsilon nonzero base small state sameBase sameEpsilon vector point inside).fderiv]
  exact (originalCartesianDivergence_value parameters length _ point inside).symm

end Grad.OriginalKernelHomogeneousGraph
