import AKAR22LiteralAngularCommutators
import AKQ10NormalizedChartAxisColumns

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.SourceCollar Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Frame

/-- Literal derivative of the existing zero-cell constant core. -/
theorem originalConstant_partial {parameters : PhaseParameters} {dimension : ℕ}
    (direction : Fin 2) (value : ComplexEuclidean dimension) :
    partialCore parameters direction (constantCore parameters value)=0 := by
  apply acore_ext
  intro cell point
  change (Grad.NonlinearQuotientBounds.partialJet direction ((constantCore parameters value).val cell)).value point = 0
  unfold constantCore
  rw [singletonCore_val]
  split
  · exact partial_constantValueJet_value direction value point
  · change (Grad.GaugeCoefficients.Physical.Compensated.partialJetLinear dimension direction 0).value point = 0
    rw [map_zero]
    rfl

theorem originalPlanarCoordinate_partial (parameters : PhaseParameters) (direction : Fin 2) :
    partialCore parameters direction (tamePlanarCoordinateField parameters) =
      constantCore parameters (EuclideanSpace.single direction 1) := by
  rw [tamePlanarCoordinateField,singleton_coordinate,singleton_coordinate,map_add,
    partialCore_coordinateCore,partialCore_coordinateCore]
  have constant (value : ComplexEuclidean 2) : singletonCore parameters (constantValueJet value)=constantCore parameters value := rfl
  rw [constant,constant,originalConstant_partial,originalConstant_partial,map_zero,map_zero,add_zero,add_zero]
  fin_cases direction <;> simp

/-- Both original full Cartesian frame columns agree with derivatives of
v = iota*y + displacement throughout the whole disk, not only on the axis. -/
theorem originalTotalFirstDerivative_frame (parameters : PhaseParameters) (length epsilon : ℝ)
    (base : ACore parameters 3) (direction : Fin 2) (point : ClosedDisk) (axial : ℝ) (row : Fin 3) :
    coreValue (partialCore parameters direction (planarReferenceCore parameters+base)) point axial row =
      originalPhysicalFrameMatrix parameters length epsilon base axial point row direction.castSucc := by
  rw [map_add,coreValue_add,planarReferenceCore,partialCore_valueMap,coreValue_valueMap,
    originalPlanarCoordinate_partial,coreValue_constant]
  exact (originalFrame_planarColumn parameters length epsilon base point axial direction row).symm

theorem originalCore_rotation_value {dimension : ℕ} {parameters : PhaseParameters}
    (field : ACore parameters dimension) (point : ClosedDisk) (axial : ℝ) :
    coreValue (rotationCore parameters field) point axial =
      (point.val 0 : ℂ) • coreValue (partialCore parameters 1 field) point axial -
        (point.val 1 : ℂ) • coreValue (partialCore parameters 0 field) point axial := by
  rw [rotationCore,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.comp_apply,coreValue_subtract,
    coreValue_coordinate,coreValue_coordinate,Complex.coe_smul,Complex.coe_smul]

end Grad.OriginalKernelRetainedDecay
