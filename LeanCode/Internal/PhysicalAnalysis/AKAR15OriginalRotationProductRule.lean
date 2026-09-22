import AKAR14ActualHomogeneousFirstRow
import GQ3RotationCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.BoundaryLift
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem rotationCore_cell {dimension : ℕ} {parameters : PhaseParameters}
    (field : ACore parameters dimension) (cell : ℤ) :
    (rotationCore parameters field).val cell = rotationJet (field.val cell) := rfl

/-- The full original axial series differentiates along the actual rotation
orbit, with its existing all-grade smooth-core majorants. -/
theorem originalCoreOrbit_hasDerivAt {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : ClosedDisk) (axial angle : ℝ) :
    HasDerivAt (fun time => coreValue field (rotatedPoint time point) axial)
      (coreValue (rotationCore parameters field) (rotatedPoint angle point) axial) angle := by
  let term (cell : ℤ) (time : ℝ) := axialPhase cell axial • (field.val cell).value (rotatedPoint time point)
  let slope (cell : ℤ) (time : ℝ) := axialPhase cell axial • ((rotationCore parameters field).val cell).value (rotatedPoint time point)
  have norms : Summable (fun cell : ℤ => ‖((rotationCore parameters field).val cell).value‖) := by
    simpa only [pow_zero,one_mul,closedDerivative_zero_order] using
      originalClosedDerivative_frequency_summable parameters (rotationCore parameters field) emptyCartesianWord 0
  have each (cell : ℤ) (time : ℝ) : HasDerivAt (term cell) (slope cell time) time :=
    (closedOrbit_hasDerivAt (field.val cell) point time).const_smul (axialPhase cell axial)
  have bound (cell : ℤ) (time : ℝ) : ‖slope cell time‖ ≤ ‖((rotationCore parameters field).val cell).value‖ := by
    dsimp only [slope]
    rw [norm_smul,norm_axialPhase,one_mul]
    exact ContinuousMap.norm_coe_le_norm _ _
  exact hasDerivAt_tsum norms each bound (coreValue_summable field (rotatedPoint 0 point) axial) angle

theorem originalDot_rotation {parameters : PhaseParameters} (first second : ACore parameters 3) :
    rotationCore parameters (dotOperation parameters first second) =
      dotOperation parameters (rotationCore parameters first) second +
        dotOperation parameters first (rotationCore parameters second) := by
  apply coreValue_ext
  intro point axial
  let product := physicalBilinear physicalDotProduct
  let realProduct := (ContinuousLinearMap.restrictScalarsL ℂ (ComplexEuclidean 3) (ComplexEuclidean 1) ℝ ℝ).comp (product.restrictScalars ℝ)
  have mapped := (realProduct.hasFDerivAt).comp_hasDerivAt 0 (originalCoreOrbit_hasDerivAt parameters first point axial 0)
  have derivative := mapped.clm_apply (originalCoreOrbit_hasDerivAt parameters second point axial 0)
  change HasDerivAt (fun time => product (coreValue first (rotatedPoint time point) axial) (coreValue second (rotatedPoint time point) axial))
    (product (coreValue (rotationCore parameters first) (rotatedPoint 0 point) axial) (coreValue second (rotatedPoint 0 point) axial) +
      product (coreValue first (rotatedPoint 0 point) axial) (coreValue (rotationCore parameters second) (rotatedPoint 0 point) axial)) 0 at derivative
  have original := originalCoreOrbit_hasDerivAt parameters (dotOperation parameters first second) point axial 0
  have same : (fun time => coreValue (dotOperation parameters first second) (rotatedPoint time point) axial) =
      (fun time => product (coreValue first (rotatedPoint time point) axial) (coreValue second (rotatedPoint time point) axial)) := by
    funext time
    exact (coreValue_pairProduct physicalDotProduct first second _ _).trans (physicalBilinear_apply _ _ _).symm
  rw [same] at original
  have identity := original.unique derivative
  rw [rotatedPoint_zero] at identity
  rw [coreValue_add]
  change _ = coreValue (pairProductLinear parameters physicalDotProduct (rotationCore parameters first) second) point axial +
    coreValue (pairProductLinear parameters physicalDotProduct first (rotationCore parameters second)) point axial
  rw [coreValue_pairProduct,coreValue_pairProduct]
  simpa only [product,physicalBilinear_apply] using identity

/-- Removing the angular mean does not change the literal R derivative. -/
theorem rotationCore_removeAngular {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) :
    rotationCore parameters (removeAngularCore parameters field) = rotationCore parameters field := by
  change rotationCore parameters (field-angularCore parameters 0 field) = _
  rw [map_sub]
  have zero : rotationCore parameters (angularCore parameters 0 field) = 0 := by
    apply Subtype.ext
    funext cell
    change rotationJet (angularClosedJet 0 (field.val cell)) = 0
    exact rotationJet_angular_zero _
  rw [zero,sub_zero]

end Grad.OriginalKernelRetainedDecay
