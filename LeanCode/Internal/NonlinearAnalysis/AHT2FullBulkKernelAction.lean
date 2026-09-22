import AHT1OriginalBulkWeights

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ) (r : RadialPoint)
    (kernel : RadialKernel parameters r src tgt)

def bulkShiftEntry (shift mode : ℤ × ℤ) :
    ComplexEuclidean src →L[ℂ] ComplexEuclidean tgt :=
  (bulkWeightRatio parameters power r.val shift mode : ℂ) •
    kernel.entry shift (twoFrequencyTranslation shift mode)

theorem bulkShiftEntry_bound (shift mode : ℤ × ℤ) :
    ‖bulkShiftEntry parameters power r kernel shift mode‖ ≤
      boundaryCoefficientPhaseCost (radialKernelParameters parameters r) shift *
        annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg
    (bulkWeightRatio_pos parameters power r.val shift mode).le]
  exact mul_le_mul (bulkWeightRatio_le parameters power r shift mode)
    (kernel.entry_le shift (twoFrequencyTranslation shift mode)) (norm_nonneg _)
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative _ _)
      (pow_nonneg (annularFrequency_pos shift).le _))

def bulkShiftAction (shift : ℤ × ℤ) : CellL2 src →L[ℂ] CellL2 tgt :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (bulkShiftEntry parameters power r kernel shift)
    (mul_nonneg (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative _ _)
      (pow_nonneg (annularFrequency_pos shift).le power))
      (fullKernelEntryNorm_nonnegative kernel shift))
    (bulkShiftEntry_bound parameters power r kernel shift)

theorem bulkShiftAction_apply (shift : ℤ × ℤ) (field : CellL2 src) (mode : ℤ × ℤ) :
    bulkShiftAction parameters power r kernel shift field mode =
      (bulkWeightRatio parameters power r.val shift mode : ℂ) •
        kernel.entry shift (twoFrequencyTranslation shift mode)
          (field (twoFrequencyTranslation shift mode)) := rfl

theorem bulkShiftAction_norm_le (shift : ℤ × ℤ) :
    ‖bulkShiftAction parameters power r kernel shift‖ ≤
      boundaryCoefficientPhaseCost (radialKernelParameters parameters r) shift *
        annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift :=
  coefficientOperator_norm_le _ _ _ _ _ _

theorem bulkShiftAction_norm_summable :
    Summable (fun shift => ‖bulkShiftAction parameters power r kernel shift‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (bulkShiftAction_norm_le parameters power r kernel) (kernel.moments power)

theorem bulkShiftAction_summable :
    Summable (bulkShiftAction parameters power r kernel) :=
  (bulkShiftAction_norm_summable parameters power r kernel).of_norm

/-- Full input-mode-dependent kernel on the exact original bulk coordinates. -/
def bulkKernelAction : CellL2 src →L[ℂ] CellL2 tgt :=
  ∑' shift, bulkShiftAction parameters power r kernel shift

theorem bulkKernelAction_norm_le : ‖bulkKernelAction parameters power r kernel‖ ≤
    fullKernelMoment (radialKernelParameters parameters r) power kernel := by
  exact (norm_tsum_le_tsum_norm (bulkShiftAction_norm_summable parameters power r kernel)).trans
    ((bulkShiftAction_norm_summable parameters power r kernel).tsum_le_tsum
      (bulkShiftAction_norm_le parameters power r kernel) (kernel.moments power))

theorem bulkKernelAction_bound (field : CellL2 src) :
    ‖bulkKernelAction parameters power r kernel field‖ ≤
      fullKernelMoment (radialKernelParameters parameters r) power kernel * ‖field‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (bulkKernelAction_norm_le parameters power r kernel) (norm_nonneg _))

theorem bulkKernelAction_hasSum (field : CellL2 src) :
    HasSum (fun shift => bulkShiftAction parameters power r kernel shift field)
      (bulkKernelAction parameters power r kernel field) :=
  (operatorEvaluation parameters 0 field).hasSum
    (bulkShiftAction_summable parameters power r kernel).hasSum

theorem bulkKernelAction_coordinate (field : CellL2 src) (mode : ℤ × ℤ) :
    HasSum (fun shift => (bulkWeightRatio parameters power r.val shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (field (twoFrequencyTranslation shift mode)))
      (bulkKernelAction parameters power r kernel field mode) := by
  exact (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean tgt) 2 mode).hasSum
    (bulkKernelAction_hasSum parameters power r kernel field)

end Grad.AnnularKernelL2
