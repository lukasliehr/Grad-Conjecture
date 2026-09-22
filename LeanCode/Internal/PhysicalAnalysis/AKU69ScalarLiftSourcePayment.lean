import AKU68SharpAxisCoefficientPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.ExhaustionSourceAllocation

theorem cartesianSpinCore_source_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (direction : Fin 2) (grade : ℕ) :
    originalGradeNorm grade (![cartesianSpinFirst source,cartesianSpinSecond source] direction) ≤
      ‖quotientEta parameters grade source‖ := by
  have first := originalScalarCore_norm_le parameters grade source 0
  have second := originalScalarCore_norm_le parameters grade source 1
  change originalGradeNorm grade (source 0) ≤ _ at first
  change originalGradeNorm grade (source 1) ≤ _ at second
  fin_cases direction
  · change originalGradeNorm grade ((1/2 : ℂ) • (source 0+source 1)) ≤ _
    rw [originalGradeNorm_smul]
    have triangle := Grad.NonlinearQuotientBounds.originalGradeNorm_add_le grade (source 0) (source 1)
    norm_num
    nlinarith only [triangle,first,second]
  · change originalGradeNorm grade ((-Complex.I/2) • (source 0-source 1)) ≤ _
    rw [originalGradeNorm_smul]
    have triangle := Grad.NonlinearQuotientBounds.originalGradeNorm_sub_le grade (source 0) (source 1)
    norm_num [norm_div,Complex.norm_I]
    nlinarith only [triangle,first,second]

theorem traceFirst_cartesianSpin_source_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (component direction : Fin 2) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade
      (traceFirst direction (![cartesianSpinFirst source,cartesianSpinSecond source] component))‖ ≤
      (6*diskSupConstant) * ‖quotientEta parameters (grade+3) source‖ := by
  exact (traceFirst_all_grade_bound _ direction grade).trans
    (mul_le_mul_of_nonneg_left (cartesianSpinCore_source_bound parameters source component (grade+3))
      (mul_nonneg (by norm_num) diskSupConstant_pos.le))

theorem originalScalarHessianAxis_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (originalScalarHessianAxis source index)‖ ≤
      (6*diskSupConstant) * ‖quotientEta parameters (grade+3) source‖ := by
  have half (data : Grad.AxisCore.AxisSmoothCore parameters 1) :
      ‖Grad.AxisCore.axisEta parameters 1 grade ((1/2 : ℂ) • data)‖ ≤
        ‖Grad.AxisCore.axisEta parameters 1 grade data‖ := by
    rw [map_smul,norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  fin_cases index
  · exact (half _).trans (traceFirst_cartesianSpin_source_bound parameters source 0 0 grade)
  · exact traceFirst_cartesianSpin_source_bound parameters source 0 1 grade
  · exact (half _).trans (traceFirst_cartesianSpin_source_bound parameters source 1 1 grade)

theorem originalScalarHessianAxis_time_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (originalScalarHessianAxis (timeDifferentiatedSource source) index)‖ ≤
      (6*diskSupConstant) * ‖quotientEta parameters (grade+4) source‖ := by
  have single (component direction : Fin 2) :
      ‖Grad.AxisCore.axisEta parameters 1 grade
        (traceFirst direction (![cartesianSpinFirst (timeDifferentiatedSource source),cartesianSpinSecond (timeDifferentiatedSource source)] component))‖ ≤
        (6*diskSupConstant) * ‖quotientEta parameters (grade+4) source‖ := by
    have same : (![cartesianSpinFirst (timeDifferentiatedSource source),cartesianSpinSecond (timeDifferentiatedSource source)] component) =
        timeDerivativeCore parameters (![cartesianSpinFirst source,cartesianSpinSecond source] component) := by
      fin_cases component
      · exact timeDifferentiatedSource_cartesian_first source
      · exact timeDifferentiatedSource_cartesian_second source
    rw [same]
    apply (traceFirst_all_grade_bound _ direction grade).trans
    exact mul_le_mul_of_nonneg_left ((timeDerivativeCore_bound parameters (grade+3) _).trans
      (cartesianSpinCore_source_bound parameters source component (grade+4)))
      (mul_nonneg (by norm_num) diskSupConstant_pos.le)
  have half (data : Grad.AxisCore.AxisSmoothCore parameters 1) :
      ‖Grad.AxisCore.axisEta parameters 1 grade ((1/2 : ℂ) • data)‖ ≤
        ‖Grad.AxisCore.axisEta parameters 1 grade data‖ := by
    rw [map_smul,norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  fin_cases index
  · exact (half _).trans (single 0 0)
  · exact single 0 1
  · exact (half _).trans (single 1 1)

def originalC2AxisBound (length : ℝ) (grade : ℕ) : ℝ :=
  ‖(length : ℂ)⁻¹‖ * (6*diskSupConstant*partialGradeConstant (grade+3)+6*diskSupConstant)

theorem originalC2AxisBound_nonnegative (length : ℝ) (grade : ℕ) : 0 ≤ originalC2AxisBound length grade := by
  have disk := diskSupConstant_pos.le
  have partialNonnegative := partialGradeConstant_nonnegative (grade+3)
  unfold originalC2AxisBound
  positivity

theorem originalC2Axis_bound (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters)
    (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (originalC2Axis length source index)‖ ≤
      originalC2AxisBound length grade * ‖quotientEta parameters (grade+4) source‖ := by
  have target (slot : Fin 3) : ‖Grad.AxisCore.axisEta parameters 1 grade (originalToroidalTargetAxis source slot)‖ ≤
      (6*diskSupConstant*partialGradeConstant (grade+3)+6*diskSupConstant) * ‖quotientEta parameters (grade+4) source‖ := by
    change ‖Grad.AxisCore.axisEta parameters 1 grade (_+_)‖ ≤ _
    rw [map_add]
    exact (norm_add_le _ _).trans ((add_le_add (originalScalarSecondAxis_bound parameters source 3 slot grade)
      (originalScalarHessianAxis_time_bound parameters source slot grade)).trans_eq (by ring))
  have scalar (a : ℂ) (bounded : ‖a‖ ≤ 1) (slot : Fin 3) :
      ‖Grad.AxisCore.axisEta parameters 1 grade (a • originalToroidalTargetAxis source slot)‖ ≤
        (6*diskSupConstant*partialGradeConstant (grade+3)+6*diskSupConstant) * ‖quotientEta parameters (grade+4) source‖ := by
    rw [map_smul,norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) bounded).trans (target slot)
  have finish (data : Grad.AxisCore.AxisSmoothCore parameters 1)
      (bounded : ‖Grad.AxisCore.axisEta parameters 1 grade data‖ ≤
        (6*diskSupConstant*partialGradeConstant (grade+3)+6*diskSupConstant) * ‖quotientEta parameters (grade+4) source‖) :
      ‖Grad.AxisCore.axisEta parameters 1 grade ((length : ℂ)⁻¹ • data)‖ ≤
        originalC2AxisBound length grade * ‖quotientEta parameters (grade+4) source‖ := by
    rw [map_smul,norm_smul]
    exact (mul_le_mul_of_nonneg_left bounded (norm_nonneg _)).trans_eq (by unfold originalC2AxisBound; ring)
  fin_cases index
  · exact finish _ (scalar (-(1/4 : ℂ)) (by norm_num) 1)
  · exact finish _ (target 0)
  · exact finish _ (scalar (1/4 : ℂ) (by norm_num) 1)

end Grad.FinitePhysicalJetLift
