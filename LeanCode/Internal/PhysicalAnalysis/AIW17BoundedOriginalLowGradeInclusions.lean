import AIW16ExactLowDiagonalCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.CartesianState Grad.PhaseAlgebra
open Grad.AnnularSourceGraph

/-- Original AJ H^t comparison uses precisely Lambda_n, not an angular surrogate. -/
def originalLowCellGradeRatio (grade larger : ℕ) (index : LowAnnularIndex) : ℝ :=
  cellFrequency index.2.val.2 ^ grade / cellFrequency index.2.val.2 ^ larger

theorem originalLowCellGradeRatio_bound (grade larger : ℕ) (included : grade ≤ larger) (index : LowAnnularIndex) :
    |originalLowCellGradeRatio grade larger index| ≤ 1 := by
  have frequency := cellFrequency_pos index.2.val.2
  have monotone := pow_le_pow_right₀ (originalLow_cell_bounds index.2.val.2).1 included
  rw [originalLowCellGradeRatio, abs_of_pos (div_pos (pow_pos frequency _) (pow_pos frequency _))]
  exact (div_le_one (pow_pos frequency _)).mpr monotone

def originalLowAJInclusion (lower : ℝ) (grade larger : ℕ) (included : grade ≤ larger) :
    originalLowGraph lower →L[ℂ] originalLowGraph lower :=
  originalLowGraphDiagonal lower (originalLowCellGradeRatio grade larger) 1 (by norm_num)
    (originalLowCellGradeRatio_bound grade larger included)

def originalLowYInclusion (lower length : ℝ) (positive : 0 < lower)
    (grade larger : ℕ) (included : grade ≤ larger) :
    lowEnergyGraph lower length positive →L[ℂ] lowEnergyGraph lower length positive :=
  originalLowEnergyDiagonal lower (originalLowCellGradeRatio grade larger) 1 (by norm_num)
    (originalLowCellGradeRatio_bound grade larger included) length positive

theorem originalLowAJInclusion_bound (lower : ℝ) (grade larger : ℕ) (included : grade ≤ larger)
    (field : originalLowGraph lower) : ‖originalLowAJInclusion lower grade larger included field‖ ≤ ‖field‖ := by
  change ‖originalLowDiagonal lower (originalLowCellGradeRatio grade larger) 1 (by norm_num)
    (originalLowCellGradeRatio_bound grade larger included) field.val‖ ≤ ‖field.val‖
  simpa only [one_mul] using originalLowDiagonal_bound lower (originalLowCellGradeRatio grade larger) 1
    (by norm_num) (originalLowCellGradeRatio_bound grade larger included) field.val

theorem originalLowYInclusion_bound (lower length : ℝ) (positive : 0 < lower)
    (grade larger : ℕ) (included : grade ≤ larger) (field : lowEnergyGraph lower length positive) :
    ‖originalLowYInclusion lower length positive grade larger included field‖ ≤ ‖field‖ := by
  change ‖originalLowDiagonal lower (originalLowCellGradeRatio grade larger) 1 (by norm_num)
    (originalLowCellGradeRatio_bound grade larger included) field.val‖ ≤ ‖field.val‖
  simpa only [one_mul] using originalLowDiagonal_bound lower (originalLowCellGradeRatio grade larger) 1
    (by norm_num) (originalLowCellGradeRatio_bound grade larger included) field.val

theorem originalLowGraphEquivalence_inclusion (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (grade larger : ℕ) (included : grade ≤ larger) (field : originalLowGraph lower) :
    originalLowGraphEquivalence parameters lower length positive lengthPositive bounded
      (originalLowAJInclusion lower grade larger included field) =
    originalLowYInclusion lower length positive grade larger included
      (originalLowGraphEquivalence parameters lower length positive lengthPositive bounded field) :=
  originalLowWeight_diagonal lower (originalLowCellGradeRatio grade larger) 1 (by norm_num)
    (originalLowCellGradeRatio_bound grade larger included) parameters length positive lengthPositive bounded field

/-- Same split/inserted frequency used by the full BF Hilbert scale. -/
def originalLowSplitGradeRatio (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (index : LowAnnularIndex) : ℝ :=
  sourceInsertedWeight angular cell inserted index.2.val /
    sourceInsertedWeight largerAngular largerCell largerInserted index.2.val

theorem originalLowSplitGradeRatio_bound (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)
    (index : LowAnnularIndex) :
    |originalLowSplitGradeRatio angular cell inserted largerAngular largerCell largerInserted index| ≤ 1 := by
  have firstPositive := sourceInsertedWeight_pos angular cell inserted index.2.val
  have secondPositive := sourceInsertedWeight_pos largerAngular largerCell largerInserted index.2.val
  rw [originalLowSplitGradeRatio, abs_of_pos (div_pos firstPositive secondPositive)]
  apply (div_le_one secondPositive).mpr
  change (1 + |(index.2.val.1 : ℝ)| + |(index.2.val.2 : ℝ)|) ^ inserted *
      ((1 + |(index.2.val.1 : ℝ)|) ^ angular * (1 + |(index.2.val.2 : ℝ)|) ^ cell) ≤
    (1 + |(index.2.val.1 : ℝ)| + |(index.2.val.2 : ℝ)|) ^ largerInserted *
      ((1 + |(index.2.val.1 : ℝ)|) ^ largerAngular * (1 + |(index.2.val.2 : ℝ)|) ^ largerCell)
  have angularOne : (1 : ℝ) ≤ 1 + |(index.2.val.1 : ℝ)| := by linarith [abs_nonneg (index.2.val.1 : ℝ)]
  have cellOne : (1 : ℝ) ≤ 1 + |(index.2.val.2 : ℝ)| := by linarith [abs_nonneg (index.2.val.2 : ℝ)]
  have totalOne : (1 : ℝ) ≤ 1 + |(index.2.val.1 : ℝ)| + |(index.2.val.2 : ℝ)| := by
    linarith [abs_nonneg (index.2.val.1 : ℝ), abs_nonneg (index.2.val.2 : ℝ)]
  exact mul_le_mul (pow_le_pow_right₀ totalOne insertedLe)
    (mul_le_mul (pow_le_pow_right₀ angularOne angularLe) (pow_le_pow_right₀ cellOne cellLe)
      (pow_nonneg (zero_le_one.trans cellOne) _) (pow_nonneg (zero_le_one.trans angularOne) _))
    (mul_nonneg (pow_nonneg (zero_le_one.trans angularOne) _) (pow_nonneg (zero_le_one.trans cellOne) _))
    (pow_nonneg (zero_le_one.trans totalOne) _)

theorem originalLowGraphEquivalence_split_inclusion (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)
    (field : originalLowGraph lower) :
    originalLowGraphEquivalence parameters lower length positive lengthPositive bounded
      (originalLowGraphDiagonal lower
        (originalLowSplitGradeRatio angular cell inserted largerAngular largerCell largerInserted) 1 (by norm_num)
        (originalLowSplitGradeRatio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe) field) =
    originalLowEnergyDiagonal lower
      (originalLowSplitGradeRatio angular cell inserted largerAngular largerCell largerInserted) 1 (by norm_num)
      (originalLowSplitGradeRatio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe)
      length positive (originalLowGraphEquivalence parameters lower length positive lengthPositive bounded field) :=
  originalLowWeight_diagonal lower _ 1 (by norm_num) _ parameters length positive lengthPositive bounded field

end Grad.AnnularOriginalLow
