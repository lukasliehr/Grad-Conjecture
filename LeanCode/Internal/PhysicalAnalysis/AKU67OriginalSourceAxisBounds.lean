import AKU64ActualResidualVanishing
import AKN30ExactEXSourceAllocationBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.ExhaustionSourceAllocation

theorem axisEta_norm_grade_mono {parameters : PhaseParameters} {dimension : ℕ} {lower upper : ℕ}
    (ordered : lower ≤ upper) (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    ‖Grad.AxisCore.axisEta parameters dimension lower data‖ ≤ ‖Grad.AxisCore.axisEta parameters dimension upper data‖ := by
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Grad.AxisCore.axisEta_apply,Grad.AxisCore.axisEta_apply,norm_smul,norm_smul,
    Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters lower cell).le,
    Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters upper cell).le]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (monotone_nat_of_le_succ (fun grade => Grad.AxisCore.axisWeight_grade_le parameters grade cell)) ordered

theorem traceFirst_all_grade_bound {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters dimension grade (traceFirst direction field)‖ ≤
      (6 * diskSupConstant) * originalGradeNorm (grade+3) field := by
  exact (axisEta_norm_grade_mono (by omega : grade ≤ grade+1) _).trans
    (traceFirst_bound direction field (grade+1) (by omega))

theorem secondAxisTrace_all_grade_bound {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (first second : Fin 2) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters dimension grade (secondAxisTrace first second field)‖ ≤
      (6 * diskSupConstant * partialGradeConstant (grade+3)) * originalGradeNorm (grade+4) field := by
  apply (traceFirst_all_grade_bound (partialCore parameters second field) first grade).trans
  exact (mul_le_mul_of_nonneg_left (partialCore_bound parameters second field (grade+3))
    (by have hd := diskSupConstant_pos.le; have hp := partialGradeConstant_nonnegative (grade+3); positivity)).trans_eq (by ring)

theorem secondTaylorAxis_all_grade_bound {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters dimension grade (secondTaylorAxis field index)‖ ≤
      (6 * diskSupConstant * partialGradeConstant (grade+3)) * originalGradeNorm (grade+4) field := by
  have half (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
      ‖Grad.AxisCore.axisEta parameters dimension grade ((1/2 : ℂ) • data)‖ ≤
        ‖Grad.AxisCore.axisEta parameters dimension grade data‖ := by
    rw [map_smul,norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  fin_cases index
  · exact (half _).trans (secondAxisTrace_all_grade_bound field 0 0 grade)
  · exact secondAxisTrace_all_grade_bound field 0 1 grade
  · exact (half _).trans (secondAxisTrace_all_grade_bound field 1 1 grade)

theorem originalForce2Axis_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (originalForce2Axis source index)‖ ≤
      (6 * diskSupConstant * partialGradeConstant (grade+3)) * ‖quotientEta parameters (grade+4) source‖ := by
  apply (secondTaylorAxis_all_grade_bound (cartesianSourceVector source) index grade).trans
  exact mul_le_mul_of_nonneg_left (originalPlanarCore_norm_le parameters (grade+4) source) (by have hd := diskSupConstant_pos.le; have hp := partialGradeConstant_nonnegative (grade+3); positivity)

theorem originalScalarSecondAxis_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (component : Fin 4) (index : Fin 3) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (scalarSecondTaylorAxis (source component) index)‖ ≤
      (6 * diskSupConstant * partialGradeConstant (grade+3)) * ‖quotientEta parameters (grade+4) source‖ := by
  apply (secondTaylorAxis_all_grade_bound (source component) index grade).trans
  exact mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters (grade+4) source component) (by have hd := diskSupConstant_pos.le; have hp := partialGradeConstant_nonnegative (grade+3); positivity)

theorem originalScalarFirstAxis_bound (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (component : Fin 4) (direction : Fin 2) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (traceFirst direction (source component))‖ ≤
      (6 * diskSupConstant) * ‖quotientEta parameters (grade+3) source‖ := by
  apply (traceFirst_all_grade_bound (source component) direction grade).trans
  exact mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters (grade+3) source component) (by have hd := diskSupConstant_pos.le; have hp := partialGradeConstant_nonnegative (grade+3); positivity)

end Grad.FinitePhysicalJetLift
