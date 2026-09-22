import AKBI2OriginalHomogeneousEulerForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.SourceCollar

/-- Existing FP17 Cartesian Fourier series of the original unmodified core. -/
def originalCoreCartesianLift {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension) :
    SpatialCell → ComplexEuclidean dimension :=
  ordinaryAmbientDerivativeSeries (originalCoefficientCore parameters field) emptyCartesianWord 0

theorem originalCoreCartesianLift_value {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (point : SpatialCell) (inside : point∈openUnitCylinder) :
    originalCoreCartesianLift parameters field point=
      coreValue field (diskCellPoint point (openCylinderMembershipClosed point inside)).1 (point 2) := by
  have same : diskCellLift (ordinaryReconstructedValue (originalCoefficientCore parameters field)) point=
      originalCoreCartesianLift parameters field point :=
    diskCellLift_ordinaryReconstructedValue_eq_series (originalCoefficientCore parameters field) inside
  rw [← same,diskCellLift,dif_pos (openCylinderMembershipClosed point inside)]
  exact (sourceCoreValue_eq_originalPhysicalEvaluationLift field _ (point 2)).symm

theorem originalCoreCartesianLift_hasFDerivAt {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (point : SpatialCell) (inside : point∈openUnitCylinder) :
    HasFDerivAt (originalCoreCartesianLift parameters field) (fderiv ℝ (originalCoreCartesianLift parameters field) point) point :=
  (ordinaryAmbientDerivativeSeries_hasFDerivAt (originalCoefficientCore parameters field) emptyCartesianWord 0 point inside).differentiableAt.hasFDerivAt

theorem originalCoreCartesianLift_partial {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (point : SpatialCell) (inside : point∈openUnitCylinder) (direction : Fin 2) :
    fderiv ℝ (originalCoreCartesianLift parameters field) point (spatialCellBasis (fp17PlanarCoordinate direction))=
      coreValue (partialCore parameters direction field) (diskCellPoint point (openCylinderMembershipClosed point inside)).1 (point 2) := by
  rw [originalCoreCartesianLift,ordinaryAmbientDerivativeSeries_fderiv_planarBasis _ _ _ point inside direction]
  rw [show ordinaryAmbientDerivativeSeries (originalCoefficientCore parameters field) (Fin.cons direction emptyCartesianWord) 0 point=
      diskCellLift (ordinaryDerivativeExtension (originalCoefficientCore parameters field) (Fin.cons direction emptyCartesianWord) 0) point from
    (diskCellLift_ordinaryDerivativeExtension (originalCoefficientCore parameters field) (Fin.cons direction emptyCartesianWord) 0 point inside).symm,
    diskCellLift,dif_pos (openCylinderMembershipClosed point inside),ordinaryDerivativeExtension_apply]
  unfold coreValue
  apply tsum_congr
  intro cell
  simp only [cellDerivativeFactor,pow_zero,one_smul,diskCellPoint,cellCharacter_coe]
  have phase : cellExponential cell (point 2)=axialPhase cell (point 2) :=
    ((axialPhase_eq_character cell (point 2)).trans (cellCharacter_coe cell (point 2))).symm
  rw [phase]
  congr 1
  change closedDerivative (field.val cell) 1 (Fin.cons direction emptyCartesianWord) _=
    closedDerivative (field.val cell) 1 (fun _ => direction) _
  congr 2
  funext position
  fin_cases position
  rfl

theorem originalCore_ext_interior {dimension : ℕ} {parameters : PhaseParameters}
    {first second : ACore parameters dimension}
    (same : ∀ (point : ClosedDisk),point.val∈openUnitDisk→∀ angle,coreValue first point angle=coreValue second point angle) : first=second := by
  apply acore_ext
  intro cell point
  have values := continuousMap_eq_of_openDisk (first.val cell).value (second.val cell).value (by
    intro query inside
    have allCells := axialSeries_ext (fun cell => (first.val cell).value query) (fun cell => (second.val cell).value query)
      (Gauges.originalValueNorm_summable parameters first query) (Gauges.originalValueNorm_summable parameters second query) (same query inside)
    exact congrFun allCells cell)
  exact congrArg (fun value : C(ClosedDisk,ComplexEuclidean dimension) => value point) values

end Grad.OriginalKernelHomogeneousGraph
