import AKU15AxisConvolutionMajorant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Allocation Grad.PhaseAlgebra

theorem axisEnvelopeConvolution_term_summable {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input)
    (coefficientGrade dataGrade : ℕ) (cell : ℤ) :
    Summable (fun shift => Grad.Constraints.Multipliers.envelopeTerm parameters coefficientGrade
      (axisFamilyOperator family) shift * axisDataNormSequence dataGrade data (cell-shift)) := by
  have nonnegative (cell : ℤ) : 0 ≤ axisDataNormSequence dataGrade data cell := norm_nonneg _
  apply Summable.of_nonneg_of_le
    (fun shift => mul_nonneg (Grad.Constraints.Multipliers.envelopeTerm_nonnegative parameters coefficientGrade _ shift)
      (nonnegative _)) (fun shift => ?_)
    ((axisFamilyOperator_envelope_summable family coherent coefficientGrade).mul_right
      ‖axisDataNormSequence dataGrade data‖)
  apply mul_le_mul_of_nonneg_left _
    (Grad.Constraints.Multipliers.envelopeTerm_nonnegative parameters coefficientGrade _ shift)
  exact (le_abs_self _).trans (component_norm_le (axisDataNormSequence dataGrade data) _)

theorem axisActionMajorant_apply {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input)
    (grade : ℕ) (cell : ℤ) :
    axisActionMajorant family coherent data grade cell = (2 : ℝ)^grade *
      ((∑' shift, Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family) shift *
        axisDataNormSequence 0 data (cell-shift)) +
       (∑' shift, Grad.Constraints.Multipliers.envelopeTerm parameters 0 (axisFamilyOperator family) shift *
        axisDataNormSequence grade data (cell-shift))) := by
  change (2 : ℝ)^grade * (_ + _) = _
  rw [axisEnvelopeConvolution_apply,axisEnvelopeConvolution_apply]

theorem axisFamilyRawAction_weighted_term {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) (cell shift : ℤ) :
    Grad.AxisCore.axisWeight parameters grade cell *
      ‖axisFamilyOperator family shift (data.val (cell-shift))‖ ≤
        (2 : ℝ)^grade *
          (Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family) shift *
            axisDataNormSequence 0 data (cell-shift) +
           Grad.Constraints.Multipliers.envelopeTerm parameters 0 (axisFamilyOperator family) shift *
            axisDataNormSequence grade data (cell-shift)) := by
  have weight := originalAxisWeight_one_high parameters grade shift (cell-shift)
  rw [add_sub_cancel] at weight
  apply (mul_le_mul_of_nonneg_left ((axisFamilyOperator family shift).le_opNorm _)
    (Grad.AxisCore.axisWeight_pos parameters grade cell).le).trans
  apply (mul_le_mul_of_nonneg_right weight (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
  rw [axisDataNormSequence_apply,axisDataNormSequence_apply]
  unfold Grad.Constraints.Multipliers.envelopeTerm tameWeight
  ring

theorem axisFamilyRawAction_majorized {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input)
    (grade : ℕ) (cell : ℤ) :
    Grad.AxisCore.axisWeight parameters grade cell * ‖axisFamilyRawAction family data cell‖ ≤
      axisActionMajorant family coherent data grade cell := by
  have high := axisEnvelopeConvolution_term_summable family coherent data grade 0 cell
  have low := axisEnvelopeConvolution_term_summable family coherent data 0 grade cell
  calc
    _ ≤ Grad.AxisCore.axisWeight parameters grade cell *
        ∑' shift, ‖axisFamilyOperator family shift (data.val (cell-shift))‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (axisFamilyRawAction_term_summable family coherent data cell))
        (Grad.AxisCore.axisWeight_pos parameters grade cell).le
    _ = ∑' shift, Grad.AxisCore.axisWeight parameters grade cell *
        ‖axisFamilyOperator family shift (data.val (cell-shift))‖ := tsum_mul_left.symm
    _ ≤ ∑' shift, (2 : ℝ)^grade *
        (Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family) shift *
          axisDataNormSequence 0 data (cell-shift) +
         Grad.Constraints.Multipliers.envelopeTerm parameters 0 (axisFamilyOperator family) shift *
          axisDataNormSequence grade data (cell-shift)) :=
      ((axisFamilyRawAction_term_summable family coherent data cell).mul_left _).tsum_le_tsum
        (axisFamilyRawAction_weighted_term family data grade cell) ((high.add low).mul_left _)
    _ = _ := by
      rw [tsum_mul_left,high.tsum_add low,axisActionMajorant_apply]

end Grad.FinitePhysicalJetLift
