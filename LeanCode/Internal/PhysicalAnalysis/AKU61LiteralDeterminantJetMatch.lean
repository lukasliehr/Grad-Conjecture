import AKU56ActualDeterminantLinearTrace
import AKU59ActualDeterminantAxisTerms
import AKU60SameMetricSourceDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation

/-- The literal original projected determinant row of the actual finite
lift matches the full prescribed linear source jet, with the original -Ld. -/
theorem originalFiniteLift_derivative_determinant_linear (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (positive : 0 < length) (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (direction : Fin 2) :
    traceFirst direction ((quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
      ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
        originalFiniteLiftS parameters length rho epsilon field low source)]) 2) =
      traceFirst direction (source 2) := by
  rw [quotientRowsDerivative_etaZero]
  change traceFirst direction (removeAngularCore parameters
    (determinantOperation parameters (partialCore parameters 0 (originalFiniteLiftU parameters length rho epsilon field low source))
      (partialCore parameters 1 (planarReferenceCore parameters+field))
      (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)) +
      determinantOperation parameters (partialCore parameters 0 (planarReferenceCore parameters+field))
        (partialCore parameters 1 (originalFiniteLiftU parameters length rho epsilon field low source))
        (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)) +
      determinantOperation parameters (partialCore parameters 0 (planarReferenceCore parameters+field))
        (partialCore parameters 1 (planarReferenceCore parameters+field))
        (physicalVariationAffine (epsilon : ℂ) (originalFiniteLiftU parameters length rho epsilon field low source)))) = _
  rw [traceFirst_removeAngular,map_add,map_add,originalFiniteLiftU,
    traceFirst_determinant_partial_lift_first,traceFirst_determinant_partial_lift_second,
    traceFirst_determinant_actual_axial_lift_zero,add_zero]
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  have equation := congrArg (fun vector : ComplexEuclidean 2 => vector direction)
    (originalLiftMetricAxis_actual_divergence parameters length rho epsilon positive field vanishes low source angle)
  have alternatives : direction = 0 ∨ direction = 1 := by omega
  rcases alternatives with rfl | rfl
  all_goals simp only [ite_true,if_neg (by decide : ¬(1 : Fin 2) = 0),axisPhysicalValue_add,axisPhysicalValue_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  · rw [originalLift_determinant_axis_first parameters length rho epsilon field potential vanishes low source 0 angle,
      originalLift_determinant_axis_second parameters length rho epsilon field potential vanishes low source 1 angle]
    simp [quadraticDivergenceCoefficients,originalG1Axis,scalarAxisPair_physical] at equation
    linear_combination equation
  · rw [originalLift_determinant_axis_first parameters length rho epsilon field potential vanishes low source 1 angle,
      originalLift_determinant_axis_second parameters length rho epsilon field potential vanishes low source 2 angle]
    simp [quadraticDivergenceCoefficients,originalG1Axis,scalarAxisPair_physical] at equation
    linear_combination equation

end Grad.FinitePhysicalJetLift
