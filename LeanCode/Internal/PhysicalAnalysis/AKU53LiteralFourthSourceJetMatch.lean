import AKU50ActualToroidalAxisRecovery
import AKU51ActualScalarTimeTaylor
import AKU52AngularSecondTaylorPreservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.ChartAxisSplit
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation

theorem originalTotal_axis_zero (parameters : PhaseParameters) (field : ACore parameters 3)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0) :
    traceZero (planarReferenceCore parameters + field) = 0 := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val,acore_val_add,originValue_add,planarReferenceCore,
    valueMapCore_originValue,tamePlanarCoordinate_origin_zero,map_zero,zero_add]
  exact vanishes cell

theorem originalC2Axis_actual_equation (parameters : PhaseParameters) (length : ℝ) (positive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    (length : ℂ) • ![originalC2Axis length source 1,
      (2 : ℂ) • originalC2Axis length source 2 - (2 : ℂ) • originalC2Axis length source 0,
      -(originalC2Axis length source 1)] - originalScalarHessianAxis (timeDifferentiatedSource source) =
      scalarSecondTaylorAxis (source 3) := by
  funext index
  apply Subtype.ext
  funext cell
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  have scalarMean : originalScalarSourceJetCoefficients source cell 0 + originalScalarSourceJetCoefficients source cell 2 = 0 := by
    change originalSourceHessian source cell 0 0 / 2 + originalSourceHessian source cell 1 1 / 2 = 0
    linear_combination (1/2 : ℂ) * originalSourceHessian_traceFree source flat cell
  have sourceMean : scalarSecondTaylorCoefficients ((source 3).val cell) 0 + scalarSecondTaylorCoefficients ((source 3).val cell) 2 = 0 := by
    apply scalarSecondTaylor_meanFree
    exact congrArg (fun core : ACore parameters 1 => core.val cell) flat.1.1
  have timeCoeff (slot : Fin 3) : originalScalarSourceJetCoefficients (timeDifferentiatedSource source) cell slot =
      ((cell : ℂ)*Complex.I) * originalScalarSourceJetCoefficients source cell slot := by
    rw [← originalScalarHessianAxis_val,originalScalarHessianAxis_time,originalScalarHessianAxis_val]
  have equation := congrFun (scalarToroidalLift_coefficients_equation length positive ((cell : ℂ)*Complex.I)
    (originalScalarSourceJetCoefficients source cell) (scalarSecondTaylorCoefficients ((source 3).val cell)) scalarMean sourceMean) index
  fin_cases index <;>
    simpa [quadraticScalarRotation,originalC2Axis_val,originalScalarHessianAxis_val,timeCoeff,scalarSecondTaylorAxis_val] using equation

theorem originalFiniteLiftS_secondTaylor_time (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    secondTaylorAxis (timeDerivativeCore parameters (originalFiniteLiftS parameters length rho epsilon field low source)) =
      originalScalarHessianAxis (timeDifferentiatedSource source) := by
  funext index
  apply Subtype.ext
  funext cell
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  rw [secondTaylorAxis_time_value,originalFiniteLiftS_secondTaylor,originalScalarHessianAxis_time]
  rfl

/-- The original projected fourth source row of the SAME finite lift
matches all quadratic coefficients, including its actual cell derivative. -/
theorem originalFiniteLift_derivative_fourth_quadratic (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (positive : 0 < length) (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    secondTaylorAxis ((quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
      ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
        originalFiniteLiftS parameters length rho epsilon field low source)]) 3) =
      secondTaylorAxis (source 3) := by
  rw [quotientRowsDerivative_etaZero]
  change secondTaylorAxis (removeAngularCore parameters
    (dotOperation parameters (rotationCore parameters (originalFiniteLiftU parameters length rho epsilon field low source))
      (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+field,potential)) +
      dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+field))
        (physicalVariationAffine (epsilon : ℂ) (originalFiniteLiftU parameters length rho epsilon field low source)) -
      timeDerivativeCore parameters (originalFiniteLiftS parameters length rho epsilon field low source))) = _
  apply secondTaylorAxis_removeAngular_eq _ _ flat.1.1
  rw [secondTaylorAxis_sub,secondTaylorAxis_add,originalFiniteLiftU,
    secondTaylorAxis_rotation_dot_actual_axial_lift,add_zero,secondTaylorAxis_rotation_lift_dot,
    affineStateCore_axis parameters length _ (originalTotal_axis_zero parameters field vanishes),
    originalFiniteLiftS_secondTaylor_time]
  simp only [axisDot_smul_right,axisDot_eT,originalLiftPhysicalUAxis_toroidal parameters length rho epsilon field vanishes low,
    smul_comm (2 : ℂ) (length : ℂ)]
  have equation := originalC2Axis_actual_equation parameters length positive source flat
  funext index
  apply Subtype.ext
  funext cell
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  have value := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell 0)
    (congrFun equation index)
  fin_cases index <;> simpa [scalarSecondTaylorAxis,secondTaylorAxis,secondAxisTrace,smul_sub,Complex.real_smul] using value

end Grad.FinitePhysicalJetLift
