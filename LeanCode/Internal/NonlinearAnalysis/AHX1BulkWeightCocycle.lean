import AHV14ExactPhysicalInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators ENNReal
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

theorem bulkTranslation_comp (outer inner mode : ℤ × ℤ) :
    twoFrequencyTranslation inner (twoFrequencyTranslation outer mode) =
      twoFrequencyTranslation (outer + inner) mode := by
  ext <;> simp only [twoFrequencyTranslation_apply] <;> dsimp <;> ring

/-- Exact cocycle of original bulk weights, with no half-order inserted. -/
theorem bulkWeightRatio_cocycle (parameters : PhaseParameters) (power : ℕ) (radius : ℝ)
    (outer inner mode : ℤ × ℤ) :
    bulkWeightRatio parameters power radius outer mode *
      bulkWeightRatio parameters power radius inner (twoFrequencyTranslation outer mode) =
    bulkWeightRatio parameters power radius (outer + inner) mode := by
  have nonzero (index : ℤ × ℤ) : annularFrequency index.1 index.2 ^ power ≠ 0 :=
    (pow_pos (annularFrequency_pos index) power).ne'
  simp only [bulkWeightRatio, bulkTranslation_comp, Real.exp_sub]
  field_simp [nonzero (twoFrequencyTranslation outer mode),
    nonzero (twoFrequencyTranslation (outer + inner) mode)]
  apply (div_eq_div_iff
    (mul_ne_zero (nonzero (twoFrequencyTranslation outer mode))
      (nonzero (twoFrequencyTranslation (outer + inner) mode)))
    (nonzero (twoFrequencyTranslation (outer + inner) mode))).2
  ring

theorem bulkWeightRatio_zero (parameters : PhaseParameters) (power : ℕ) (radius : ℝ)
    (mode : ℤ × ℤ) : bulkWeightRatio parameters power radius (0, 0) mode = 1 := by
  have nonzero := (pow_pos (annularFrequency_pos mode) power).ne'
  simp [bulkWeightRatio, twoFrequencyTranslation_apply, nonzero]

variable {input middle output : ℕ} (parameters : PhaseParameters) (power : ℕ) (radius : RadialPoint)
    (outer : RadialKernel parameters radius middle output)
    (inner : RadialKernel parameters radius input middle)
    (field : CellL2 input) (mode : ℤ × ℤ)

def bulkActionPairTerm (pair : (ℤ × ℤ) × (ℤ × ℤ)) : ComplexEuclidean output :=
  bulkShiftAction parameters power radius outer pair.1
    (bulkShiftAction parameters power radius inner pair.2 field) mode

theorem bulkActionPairTerm_norm_le (pair : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖bulkActionPairTerm parameters power radius outer inner field mode pair‖ ≤
      ‖bulkShiftAction parameters power radius outer pair.1‖ *
        ‖bulkShiftAction parameters power radius inner pair.2‖ * ‖field‖ := by
  apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (bulkShiftAction parameters power radius outer pair.1
      (bulkShiftAction parameters power radius inner pair.2 field)) mode).trans
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _).symm)

theorem bulkActionPairTerm_summable :
    Summable (bulkActionPairTerm parameters power radius outer inner field mode) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (bulkActionPairTerm_norm_le parameters power radius outer inner field mode)
  exact ((bulkShiftAction_norm_summable parameters power radius outer).mul_of_nonneg
    (bulkShiftAction_norm_summable parameters power radius inner)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right ‖field‖

/-- Pairwise composition retains the exact original bulk ratio. -/
theorem bulkActionPairTerm_literal (pair : (ℤ × ℤ) × (ℤ × ℤ)) :
    bulkActionPairTerm parameters power radius outer inner field mode pair =
      (bulkWeightRatio parameters power radius.val (pair.1 + pair.2) mode : ℂ) •
        outer.entry pair.1 (twoFrequencyTranslation pair.1 mode)
          (inner.entry pair.2 (twoFrequencyTranslation (pair.1 + pair.2) mode)
            (field (twoFrequencyTranslation (pair.1 + pair.2) mode))) := by
  rw [bulkActionPairTerm, bulkShiftAction_apply, bulkShiftAction_apply, map_smul, smul_smul,
    ← Complex.ofReal_mul, bulkWeightRatio_cocycle, bulkTranslation_comp]

end Grad.AnnularKernelL2
