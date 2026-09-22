import AKU70FiniteAxisMapBounds
import AKU71ActualLiftCoefficientBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.ExhaustionSourceAllocation

def axisCovectorConstant : ℝ := 1+‖matrixOperator firstTwoInclusion‖+
  ‖matrixOperator (!![0;0;1] : Matrix (Fin 3) (Fin 1) ℂ)‖

theorem axisCovectorConstant_nonnegative : 0 ≤ axisCovectorConstant := by
  unfold axisCovectorConstant
  positivity

theorem axisCovectorTriple_bound {parameters : PhaseParameters}
    (planar : Grad.AxisCore.AxisSmoothCore parameters 2) (toroidal : Grad.AxisCore.AxisSmoothCore parameters 1) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters 3 grade (axisCovectorTriple planar toroidal)‖ ≤
      axisCovectorConstant * (‖Grad.AxisCore.axisEta parameters 2 grade planar‖+‖Grad.AxisCore.axisEta parameters 1 grade toroidal‖) := by
  rw [axisCovectorTriple,map_add]
  apply (norm_add_le _ _).trans
  have first := axisValueMap_bound (matrixOperator firstTwoInclusion) planar grade
  have second := axisValueMap_bound (matrixOperator (!![0;0;1] : Matrix (Fin 3) (Fin 1) ℂ)) toroidal grade
  unfold axisCovectorConstant
  nlinarith only [first,second,norm_nonneg (Grad.AxisCore.axisEta parameters 2 grade planar),
    norm_nonneg (Grad.AxisCore.axisEta parameters 1 grade toroidal),
    mul_nonneg (norm_nonneg (matrixOperator firstTwoInclusion)) (norm_nonneg (Grad.AxisCore.axisEta parameters 1 grade toroidal)),
    mul_nonneg (norm_nonneg (matrixOperator (!![0;0;1] : Matrix (Fin 3) (Fin 1) ℂ))) (norm_nonneg (Grad.AxisCore.axisEta parameters 2 grade planar))]

theorem axisCubicComplementVector_bound {parameters : PhaseParameters}
    (data : Grad.AxisCore.AxisSmoothCore parameters 2) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (axisCubicComplementVector data index)‖ ≤
      4*‖Grad.AxisCore.axisEta parameters 2 grade data‖ := by
  have first := axisComponent_bound data 0 grade
  have second := axisComponent_bound data 1 grade
  fin_cases index
  all_goals apply (scalarAxisPair_bound _ _ grade).trans
  all_goals simp only [map_smul,norm_smul]
  all_goals norm_num
  all_goals nlinarith only [first,second,norm_nonneg (Grad.AxisCore.axisEta parameters 2 grade data)]

def finiteSourceAxisConstant (grade : ℕ) : ℝ := 6*diskSupConstant*(1+partialGradeConstant (grade+3))

theorem finiteSourceAxisConstant_nonnegative (grade : ℕ) : 0 ≤ finiteSourceAxisConstant grade := by
  have disk := diskSupConstant_pos.le
  have part := partialGradeConstant_nonnegative (grade+3)
  unfold finiteSourceAxisConstant
  positivity

theorem finiteLiftAxisPayment_source_le (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    ‖quotientEta parameters (grade+4) source‖ ≤ finiteLiftAxisPayment parameters field rho epsilon source grade :=
  le_add_of_nonneg_right (mul_nonneg (physicalBudget_nonnegative parameters field rho epsilon _) (norm_nonneg _))

theorem originalForce2Axis_payment (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 2 grade (originalForce2Axis source index)‖ ≤
      finiteSourceAxisConstant grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have disk := diskSupConstant_pos.le
  have coefficient : 6*diskSupConstant*partialGradeConstant (grade+3) ≤ finiteSourceAxisConstant grade := by
    unfold finiteSourceAxisConstant
    nlinarith only [disk]
  exact (originalForce2Axis_bound parameters source index grade).trans
    ((mul_le_mul_of_nonneg_right coefficient (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (finiteLiftAxisPayment_source_le parameters field rho epsilon source grade)
        (finiteSourceAxisConstant_nonnegative grade)))

theorem originalScalarFirstAxis_payment (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) (component : Fin 4) (direction : Fin 2) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (traceFirst direction (source component))‖ ≤
      finiteSourceAxisConstant grade * finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have disk := diskSupConstant_pos.le
  have part := partialGradeConstant_nonnegative (grade+3)
  have coefficient : 6*diskSupConstant ≤ finiteSourceAxisConstant grade := by
    unfold finiteSourceAxisConstant
    nlinarith only [mul_nonneg disk part]
  have sourceBound := (originalSourceNorm_monotone parameters source (by omega : grade+3 ≤ grade+4)).trans
    (finiteLiftAxisPayment_source_le parameters field rho epsilon source grade)
  exact (originalScalarFirstAxis_bound parameters source component direction grade).trans
    ((mul_le_mul_of_nonneg_right coefficient (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left sourceBound (finiteSourceAxisConstant_nonnegative grade)))

theorem originalC2Axis_payment (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon length : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) (index : Fin 3) :
    ‖Grad.AxisCore.axisEta parameters 1 grade (originalC2Axis length source index)‖ ≤
      originalC2AxisBound length grade * finiteLiftAxisPayment parameters field rho epsilon source grade :=
  (originalC2Axis_bound parameters length source index grade).trans
    (mul_le_mul_of_nonneg_left (finiteLiftAxisPayment_source_le parameters field rho epsilon source grade)
      (originalC2AxisBound_nonnegative length grade))

end Grad.FinitePhysicalJetLift
