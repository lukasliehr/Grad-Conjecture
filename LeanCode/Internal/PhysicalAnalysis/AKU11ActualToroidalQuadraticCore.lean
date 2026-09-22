import AKU10OriginalScalarPolynomialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.NonlinearDivision Grad.NonlinearRange

def timeDifferentiatedSource {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    SmoothQuotient parameters := fun slot => timeDerivativeCore parameters (source slot)

theorem timeDifferentiatedSource_cartesian_first {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    cartesianSpinFirst (timeDifferentiatedSource source) = timeDerivativeCore parameters (cartesianSpinFirst source) := by
  change (1/2 : ℂ) • (_ + _) = timeDerivativeCore parameters ((1/2 : ℂ) • (_ + _))
  rw [map_smul,map_add]
  rfl

theorem timeDifferentiatedSource_cartesian_second {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    cartesianSpinSecond (timeDifferentiatedSource source) = timeDerivativeCore parameters (cartesianSpinSecond source) := by
  change (-Complex.I/2) • (_ - _) = timeDerivativeCore parameters ((-Complex.I/2) • (_ - _))
  rw [map_smul,map_sub]
  rfl

theorem traceFirst_time_value {parameters : PhaseParameters} (field : ACore parameters 1)
    (direction : Fin 2) (cell : ℤ) :
    (traceFirst direction (timeDerivativeCore parameters field)).val cell 0 =
      ((cell : ℂ) * Complex.I) * (traceFirst direction field).val cell 0 := by
  rw [traceFirst_val,timeDerivativeCore_val,originPartial_smul]
  rfl

theorem originalScalarHessianAxis_time {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (cell : ℤ) (index : Fin 3) :
    (originalScalarHessianAxis (timeDifferentiatedSource source) index).val cell 0 =
      ((cell : ℂ) * Complex.I) * (originalScalarHessianAxis source index).val cell 0 := by
  fin_cases index
  · change (1/2 : ℂ) * (traceFirst 0 (cartesianSpinFirst (timeDifferentiatedSource source))).val cell 0 =
      _ * ((1/2 : ℂ) * (traceFirst 0 (cartesianSpinFirst source)).val cell 0)
    rw [timeDifferentiatedSource_cartesian_first,traceFirst_time_value]
    ring
  · change (traceFirst 1 (cartesianSpinFirst (timeDifferentiatedSource source))).val cell 0 = _
    rw [timeDifferentiatedSource_cartesian_first,traceFirst_time_value]
    rfl
  · change (1/2 : ℂ) * (traceFirst 1 (cartesianSpinSecond (timeDifferentiatedSource source))).val cell 0 =
      _ * ((1/2 : ℂ) * (traceFirst 1 (cartesianSpinSecond source)).val cell 0)
    rw [timeDifferentiatedSource_cartesian_second,traceFirst_time_value]
    ring

def originalToroidalTargetAxis {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    ScalarQuadraticAxisData parameters :=
  scalarSecondTaylorAxis (source 3) + originalScalarHessianAxis (timeDifferentiatedSource source)

def originalC2Core {parameters : PhaseParameters} (length : ℝ) (source : SmoothQuotient parameters) :
    ACore parameters 1 :=
  (length : ℂ)⁻¹ • quadraticAxisCore ![-(1/4 : ℂ) • originalToroidalTargetAxis source 1,
    originalToroidalTargetAxis source 0,(1/4 : ℂ) • originalToroidalTargetAxis source 1]

theorem originalC2Core_val {parameters : PhaseParameters} (length : ℝ) (source : SmoothQuotient parameters)
    (cell : ℤ) : (originalC2Core length source).val cell =
      quadraticScalarJet (scalarToroidalLiftCoefficients length ((cell : ℂ) * Complex.I)
        (originalScalarSourceJetCoefficients source cell) (scalarSecondTaylorCoefficients ((source 3).val cell))) := by
  have target (index : Fin 3) : (originalToroidalTargetAxis source index).val cell 0 =
      scalarSecondTaylorCoefficients ((source 3).val cell) index +
        ((cell : ℂ) * Complex.I) * originalScalarSourceJetCoefficients source cell index := by
    change (scalarSecondTaylorAxis (source 3) index).val cell 0 +
      (originalScalarHessianAxis (timeDifferentiatedSource source) index).val cell 0 = _
    rw [scalarSecondTaylorAxis_val,originalScalarHessianAxis_time,originalScalarHessianAxis_val]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  have componentZero : component = 0 := Subsingleton.elim _ _
  subst component
  change (((length : ℂ)⁻¹ • (quadraticAxisCore _).val cell).value point 0) = _
  rw [closedJet_value_smul,ContinuousMap.smul_apply,PiLp.smul_apply,smul_eq_mul,quadraticAxisCore_val]
  simp only [quadraticScalarJet_value,scalarToroidalLiftCoefficients,quadraticScalarAngularInverse,
    Pi.smul_apply,Pi.add_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two]
  change (length : ℂ)⁻¹ * ((point.val 0 : ℂ)^2 * (-(1/4 : ℂ) * (originalToroidalTargetAxis source 1).val cell 0) +
    (point.val 0 : ℂ) * (point.val 1 : ℂ) * (originalToroidalTargetAxis source 0).val cell 0 +
    (point.val 1 : ℂ)^2 * ((1/4 : ℂ) * (originalToroidalTargetAxis source 1).val cell 0)) = _
  rw [target,target]
  norm_num
  ring

theorem originalC2Core_mean_zero {parameters : PhaseParameters} (length : ℝ) (source : SmoothQuotient parameters) :
    angularCore parameters 0 (originalC2Core length source) = 0 := by
  apply Subtype.ext
  funext cell
  change angularClosedJet 0 ((originalC2Core length source).val cell) = 0
  rw [originalC2Core_val]
  exact scalarToroidalLift_mean_zero _ _ _ _

/-- Exact original third leading row in the original smooth core; its time
multiplier is the actual cell derivative and includes the zero cell. -/
theorem originalC2Core_third_leading {parameters : PhaseParameters} (length : ℝ) (positive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    (length : ℂ) • rotationCore parameters (originalC2Core length source) -
      timeDerivativeCore parameters (originalS2Core source) =
        quadraticAxisCore (scalarSecondTaylorAxis (source 3)) := by
  apply Subtype.ext
  funext cell
  change (length : ℂ) • rotationJet ((originalC2Core length source).val cell) -
    ((cell : ℂ) * Complex.I) • (originalS2Core source).val cell = _
  rw [originalC2Core_val,originalS2Core_val,quadraticAxisCore_val]
  have coefficients : (fun index => (scalarSecondTaylorAxis (source 3) index).val cell 0) =
      scalarSecondTaylorCoefficients ((source 3).val cell) := funext (scalarSecondTaylorAxis_val _ cell)
  rw [coefficients]
  apply scalarToroidalLift_equation length positive
  · change originalSourceHessian source cell 0 0 / 2 + originalSourceHessian source cell 1 1 / 2 = 0
    linear_combination (1/2 : ℂ) * originalSourceHessian_traceFree source flat cell
  · apply scalarSecondTaylor_meanFree
    have mean := congrArg (fun core : ACore parameters 1 => core.val cell) flat.1.1
    exact mean

end Grad.FinitePhysicalJetLift
