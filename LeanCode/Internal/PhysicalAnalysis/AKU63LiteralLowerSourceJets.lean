import AKU62ActualForceFirstJets
import AKU53LiteralFourthSourceJetMatch
import AKU61LiteralDeterminantJetMatch

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation

theorem traceFirst_valueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) (direction : Fin 2) :
    traceFirst direction (valueMapCore parameters mapping field) =
      axisValueMap mapping (traceFirst direction field) := by
  apply axisPhysicalValue_ext
  intro angle
  rw [traceFirst_physical,partialCore_valueMap,coreValue_valueMap,axisValueMap_physical]
  exact congrArg mapping (traceFirst_physical field direction angle).symm

theorem originalFiniteLift_derivative_force_linear (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (derivative : Fin 2) :
    traceFirst derivative (cartesianSourceVector
      (quotientRowsDerivative parameters length 1 ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
        ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
          originalFiniteLiftS parameters length rho epsilon field low source)])) =
      traceFirst derivative (cartesianSourceVector source) := by
  rw [quotientRowsDerivative_etaZero_cartesian]
  apply Subtype.ext
  funext cell
  apply PiLp.ext
  intro direction
  have mapped := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell 0)
    (originalFiniteLift_force_firstTrace parameters length rho epsilon field low source flat direction derivative)
  have recover := traceFirst_valueMap (componentValue 2 direction)
    (vectorTuple
      (physicalCartesianForceComponent 0 (planarReferenceCore parameters+field)
        (originalFiniteLiftU parameters length rho epsilon field low source)
        (originalFiniteLiftS parameters length rho epsilon field low source))
      (physicalCartesianForceComponent 1 (planarReferenceCore parameters+field)
        (originalFiniteLiftU parameters length rho epsilon field low source)
        (originalFiniteLiftS parameters length rho epsilon field low source))) derivative
  change traceFirst derivative (componentCore 2 direction _) = _ at recover
  rw [componentCore_vectorTuple] at recover
  have sourceRecover := traceFirst_valueMap (componentValue 2 direction) (cartesianSourceVector source) derivative
  change traceFirst derivative (componentCore 2 direction
    (vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source))) = _ at sourceRecover
  rw [componentCore_vectorTuple] at sourceRecover
  have recovered := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell 0) recover
  have sourceRecovered := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell 0) sourceRecover
  fin_cases direction <;>
    simpa only [axisValueMap_val,componentValue_apply] using recovered.symm.trans (mapped.trans sourceRecovered)

theorem traceZero_removeAngular {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) : traceZero (removeAngularCore parameters field) = 0 := by
  apply Subtype.ext
  funext cell
  change originValue (field.val cell-angularClosedJet 0 (field.val cell)) = 0
  rw [originValue_sub,angularJet_zero_originValue,sub_self]

theorem traceFirst_rotation_lift_dot {parameters : PhaseParameters}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (field : ACore parameters 3)
    (derivative : Fin 2) : traceFirst derivative (dotOperation parameters
      (rotationCore parameters (localizedQuadraticVectorAxisCore data)) field) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  fin_cases derivative <;> simp [rotationCore,partialCore_coordinateCore,map_add,map_sub,
    dot_coordinate_first,traceFirst_coordinateCore,traceZero_coordinateCore]

theorem traceFirst_rotation_dot_actual_axial_lift {parameters : PhaseParameters}
    (epsilon : ℂ) (field : ACore parameters 3)
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (derivative : Fin 2) :
    traceFirst derivative (dotOperation parameters (rotationCore parameters field)
      (physicalVariationAffine epsilon (localizedQuadraticVectorAxisCore data))) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  have additive (a b : ACore parameters 3) : physicalVariationAffine epsilon (a+b) =
      physicalVariationAffine epsilon a + physicalVariationAffine epsilon b := by
    simp only [physicalVariationAffine,map_add,smul_add]
    abel
  rw [additive,additive]
  fin_cases derivative <;> simp [physicalVariationAffine_coordinate,map_add,dot_coordinate_second,
    traceFirst_coordinateCore,traceZero_coordinateCore]

theorem traceFirst_time_vector_value {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) (cell : ℤ) :
    (traceFirst direction (timeDerivativeCore parameters field)).val cell =
      ((cell : ℂ)*Complex.I) • (traceFirst direction field).val cell := by
  rw [traceFirst_val,timeDerivativeCore_val,originPartial_smul]
  rfl

theorem originalFiniteLift_derivative_fourth_linear (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (direction : Fin 2) :
    traceFirst direction ((quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
      ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
        originalFiniteLiftS parameters length rho epsilon field low source)]) 3) = 0 := by
  rw [quotientRowsDerivative_etaZero]
  change traceFirst direction (removeAngularCore parameters
    (dotOperation parameters (rotationCore parameters (originalFiniteLiftU parameters length rho epsilon field low source))
      (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)) +
      dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+field))
        (physicalVariationAffine (epsilon : ℂ) (originalFiniteLiftU parameters length rho epsilon field low source)) -
      timeDerivativeCore parameters (originalFiniteLiftS parameters length rho epsilon field low source))) = 0
  rw [traceFirst_removeAngular,map_sub,map_add,originalFiniteLiftU,
    traceFirst_rotation_lift_dot,traceFirst_rotation_dot_actual_axial_lift,zero_add,zero_sub]
  have zero : traceFirst direction (timeDerivativeCore parameters
      (originalFiniteLiftS parameters length rho epsilon field low source)) = 0 := by
    apply Subtype.ext
    funext cell
    rw [traceFirst_time_vector_value,(originalFiniteLiftS_zero_jets parameters length rho epsilon field low source).2 direction]
    exact smul_zero _
  rw [zero,neg_zero]

end Grad.FinitePhysicalJetLift
