import AKBI19SameCoreCofactorDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2300000
open Set Filter
open scoped BigOperators Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger

theorem originalCoreCartesianLift_axial {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (point : SpatialCell) (inside : point∈openUnitCylinder) :
    fderiv ℝ (originalCoreCartesianLift parameters field) point (spatialCellBasis 2)=
      coreValue (timeDerivativeCore parameters field) (diskCellPoint point (openCylinderMembershipClosed point inside)).1 (point 2) := by
  rw [originalCoreCartesianLift,ordinaryAmbientDerivativeSeries_fderiv_cellBasis _ _ _ point inside]
  rw [show ordinaryAmbientDerivativeSeries (originalCoefficientCore parameters field) emptyCartesianWord 1 point=
      diskCellLift (ordinaryDerivativeExtension (originalCoefficientCore parameters field) emptyCartesianWord 1) point from
    (diskCellLift_ordinaryDerivativeExtension (originalCoefficientCore parameters field) emptyCartesianWord 1 point inside).symm,
    diskCellLift,dif_pos (openCylinderMembershipClosed point inside)]
  exact originalAxialDerivative_eq_coreValue parameters field _ (point 2)

theorem originalCoreCartesianLift_valueMap_fderiv {input output : ℕ} (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ACore parameters input)
    (point : SpatialCell) (inside : point∈openUnitCylinder) (direction : SpatialCell) :
    fderiv ℝ (originalCoreCartesianLift parameters (valueMapCore parameters mapping field)) point direction=
      mapping (fderiv ℝ (originalCoreCartesianLift parameters field) point direction) := by
  have composed := (mapping.restrictScalars ℝ).hasFDerivAt.comp point (originalCoreCartesianLift_hasFDerivAt parameters field point inside)
  have same : originalCoreCartesianLift parameters (valueMapCore parameters mapping field)=ᶠ[𝓝 point]
      (fun query => mapping (originalCoreCartesianLift parameters field query)) := by
    filter_upwards [openUnitCylinder_isOpen.mem_nhds inside] with query included
    rw [originalCoreCartesianLift_value parameters _ query included,originalCoreCartesianLift_value parameters _ query included,
      coreValue_valueMap]
  have actual := originalCoreCartesianLift_hasFDerivAt parameters (valueMapCore parameters mapping field) point inside
  exact congrArg (fun derivative : SpatialCell →L[ℝ] ComplexEuclidean output => derivative direction)
    (actual.unique (composed.congr_of_eventuallyEq same))

/-- The core divergence is literally the actual Cartesian Frechet
contraction, in the original L,L,1 convention. -/
theorem originalCartesianDivergence_value (parameters : PhaseParameters) (length : ℝ) (field : ACore parameters 3)
    (point : SpatialCell) (inside : point∈openUnitCylinder) :
    coreValue (originalCartesianDivergenceCore length field) (diskCellPoint point (openCylinderMembershipClosed point inside)).1 (point 2) 0=
      (length : ℂ)*(fderiv ℝ (originalCoreCartesianLift parameters field) point (spatialCellBasis 0) 0+
        fderiv ℝ (originalCoreCartesianLift parameters field) point (spatialCellBasis 1) 1)+
      fderiv ℝ (originalCoreCartesianLift parameters field) point (spatialCellBasis 2) 2 := by
  unfold originalCartesianDivergenceCore
  rw [coreValue_add,coreValue_smul,coreValue_add]
  rw [← originalCoreCartesianLift_partial parameters _ point inside 0,
    ← originalCoreCartesianLift_partial parameters _ point inside 1,
    ← originalCoreCartesianLift_axial parameters _ point inside]
  rw [originalCoreCartesianLift_valueMap_fderiv parameters _ field point inside,
    originalCoreCartesianLift_valueMap_fderiv parameters _ field point inside,
    originalCoreCartesianLift_valueMap_fderiv parameters _ field point inside]
  simp [matrixUnit_apply,operatorBasis,fp17PlanarCoordinate,mul_add]

end Grad.OriginalKernelHomogeneousGraph
