import AKU44ActualLiftCovectorRecovery
import AKU46ActualScalarAndFiniteForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 3000
namespace Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Ledger

theorem originalLiftPlanarAxis_finite_force (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (angle : ℝ) :
    cubicGradientCoefficients (cubicComplementCoefficients
      (axisPhysicalValue (originalLiftEllAxis parameters length rho epsilon field low source) angle)) -
        quadraticPlanarOperator (fun index =>
          axisPhysicalValue (originalLiftPlanarAxis parameters length rho epsilon field low source index) angle) =
      fun index => axisPhysicalValue (originalForce2Axis source index) angle := by
  have same : (fun index => axisPhysicalValue
      (originalLiftPlanarAxis parameters length rho epsilon field low source index) angle) =
      leadingPlanarLiftCoefficients
        (axisPhysicalValue (originalLiftEllAxis parameters length rho epsilon field low source) angle)
        (fun index => axisPhysicalValue (originalForce2Axis source index) angle) := by
    funext index
    simp only [originalLiftPlanarAxis,Pi.sub_apply,axisPhysicalValue_sub,
      axisCubicComplementVector_physical,quadraticAxisPlanarInverse_physical,leadingPlanarLiftCoefficients]
  rw [same]
  exact leadingPlanarLift_force_coefficients _ _

/-- The literal variable-current Cartesian force of the actual localized
lift matches every prescribed quadratic coefficient of the original source.
The full current, original cutoff, all cell modes and full F^-T are retained. -/
theorem originalFiniteLift_force_secondTaylor (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (direction : Fin 2) :
    secondTaylorAxis (physicalCartesianForceComponent direction (planarReferenceCore parameters + field)
      (originalFiniteLiftU parameters length rho epsilon field low source)
      (originalFiniteLiftS parameters length rho epsilon field low source)) =
      fun index => axisComponent direction (originalForce2Axis source index) := by
  rw [originalFiniteLiftU,actualCurrentForce_secondTaylor,localizedQuadraticForce_secondTaylor,
    secondTaylorAxis_sub,secondTaylorAxis_sub,originalFiniteLiftS_secondTaylor_partial,
    secondTaylorAxis_lift_partial_current_rotation,secondTaylorAxis_current_partial_rotation_lift]
  funext index
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  have equation := congrArg (fun coefficients : QuadraticPlanarCoefficients => coefficients index direction)
    (originalLiftPlanarAxis_finite_force parameters length rho epsilon field low source angle)
  fin_cases direction <;> fin_cases index
  all_goals simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Pi.sub_apply,
    axisDot_comm (originalLiftPhysicalUAxis parameters length rho epsilon field low source 0) _,
    axisDot_comm (originalLiftPhysicalUAxis parameters length rho epsilon field low source 1) _,
    axisDot_comm (originalLiftPhysicalUAxis parameters length rho epsilon field low source 2) _,
    originalLiftPhysicalUAxis_covector,axisPhysicalValue_sub,
    axisComponent_physical,componentValue_apply,
    originalLiftS3Axis,PiLp.sub_apply] at *
  all_goals simp [cubicGradientCoefficients,cubicComplementCoefficients,quadraticPlanarOperator,
    quadraticRotation,quadraticQuarterTurn,quarterValueMap,quarterValueLinear,
    axisPhysicalValue_add,axisPhysicalValue_sub,axisPhysicalValue_smul,
    axisComponent_physical,componentValue_apply] at equation ⊢
  all_goals linear_combination equation

end Grad.FinitePhysicalJetLift
