import AKU48LiteralDerivativeQuadraticForce
import AKU51ActualScalarTimeTaylor
import AKU52AngularSecondTaylorPreservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation

theorem traceFirst_lift_partial_rotation {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (direction derivative : Fin 2) :
    traceFirst derivative (dotOperation parameters
      (partialCore parameters direction (localizedQuadraticVectorAxisCore data))
      (rotationCore parameters field)) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  fin_cases direction <;> fin_cases derivative <;>
    simp [rotationCore,partialCore_coordinateCore,map_add,map_sub,
      dot_coordinate_first,dot_coordinate_second,traceFirst_coordinateCore,traceZero_coordinateCore]

theorem traceFirst_current_partial_rotation_lift {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (direction derivative : Fin 2) :
    traceFirst derivative (dotOperation parameters (partialCore parameters direction field)
      (rotationCore parameters (localizedQuadraticVectorAxisCore data))) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  fin_cases direction <;> fin_cases derivative <;>
    simp [rotationCore,partialCore_coordinateCore,map_add,map_sub,
      dot_coordinate_second,traceFirst_coordinateCore,traceZero_coordinateCore]

theorem localizedQuadraticForce_firstTrace_scalar {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (scalar : ACore parameters 1) (direction derivative : Fin 2) :
    traceFirst derivative (physicalCartesianForceComponent direction field
      (localizedQuadraticVectorAxisCore data) scalar) = secondAxisTrace derivative direction scalar := by
  rw [localizedQuadraticForce_firstTrace,map_sub,map_sub,
    traceFirst_lift_partial_rotation,traceFirst_current_partial_rotation_lift,sub_zero,sub_zero]
  rfl

theorem originalSourceHessian_axis_symmetric {parameters : PhaseParameters}
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    traceFirst 1 (cartesianSpinFirst source) = traceFirst 0 (cartesianSpinSecond source) := by
  have curlZero := (isFlat_iff_cartesian source).mp flat |>.2.2.1
  change traceFirst 0 (componentCore 2 1 (cartesianSourceVector source)) -
    traceFirst 1 (componentCore 2 0 (cartesianSourceVector source)) = 0 at curlZero
  change traceFirst 0 (componentCore 2 1 (vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source))) -
    traceFirst 1 (componentCore 2 0 (vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source))) = 0 at curlZero
  rw [componentCore_vectorTuple,componentCore_vectorTuple] at curlZero
  exact (sub_eq_zero.mp curlZero).symm

theorem originalFiniteLiftS_hessian (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (derivative direction : Fin 2) :
    secondAxisTrace derivative direction (originalFiniteLiftS parameters length rho epsilon field low source) =
      traceFirst derivative (![cartesianSpinFirst source,cartesianSpinSecond source] direction) := by
  have coefficients := originalFiniteLiftS_secondTaylor parameters length rho epsilon field low source
  have diagonal (index : Fin 3) := congrArg (fun data => (2 : ℂ) • data index) coefficients
  have mixed := congrFun coefficients (1 : Fin 3)
  fin_cases derivative <;> fin_cases direction
  · have same := diagonal 0
    simpa [secondTaylorAxis,originalScalarHessianAxis,smul_smul] using same
  · exact mixed.trans (originalSourceHessian_axis_symmetric source flat)
  · rw [secondAxisTrace_symm]
    exact mixed
  · have same := diagonal 2
    simpa [secondTaylorAxis,originalScalarHessianAxis,smul_smul] using same

theorem originalFiniteLift_force_firstTrace (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (direction derivative : Fin 2) :
    traceFirst derivative (physicalCartesianForceComponent direction (planarReferenceCore parameters+field)
      (originalFiniteLiftU parameters length rho epsilon field low source)
      (originalFiniteLiftS parameters length rho epsilon field low source)) =
      traceFirst derivative (![cartesianSpinFirst source,cartesianSpinSecond source] direction) := by
  rw [originalFiniteLiftU,localizedQuadraticForce_firstTrace_scalar]
  exact originalFiniteLiftS_hessian parameters length rho epsilon field low source flat derivative direction

end Grad.FinitePhysicalJetLift
