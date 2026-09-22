import AKDS24FiniteJetPairPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace

/-- All endpoint terms in the final planar estimate have one common
fixed-loss payment. The high budget multiplies the independent base norm. -/
theorem finiteJetEndpoint_oneHigh_payment (parameters : PhaseParameters)
    (grade shift loss : ℕ) (lossLarge : shift+20≤loss)
    (cellConstants : ℕ→ℝ) (cellNonnegative : ∀ index,0≤cellConstants index)
    (rho epsilon : ℝ) (field : ACore parameters 3)
    (bounded : physicalBudget parameters field rho epsilon 20≤1)
    (source : SmoothQuotient parameters) (core : ACore parameters 3)
    (cell : ∀ index, originalCellNorm parameters index core≤cellConstants index*
      (‖quotientEta parameters (index+20) source‖+
        physicalBudget parameters field rho epsilon (index+20)*‖quotientEta parameters 20 source‖)) :
    originalCellNorm parameters (grade+shift) core+
      (1+physicalBudget parameters field rho epsilon (grade+shift+20))*originalGradeNorm 0 core+
      ‖quotientEta parameters (grade+shift+20) source‖+
      (1+physicalBudget parameters field rho epsilon (grade+shift+20))*‖quotientEta parameters 20 source‖ ≤
    (cellConstants (grade+shift)+2*cellConstants 0+2)*
      (‖quotientEta parameters (grade+loss) source‖+
        physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖) := by
  let payment := ‖quotientEta parameters (grade+loss) source‖+
    physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖
  have highMono := referenceSource_norm_mono parameters (by omega : grade+shift+20≤grade+loss) source
  have lowMono := referenceSource_norm_mono parameters (by omega : 20≤loss) source
  have budgetMono := physicalBudget_monotone parameters field rho epsilon (by omega : grade+shift+20≤grade+loss)
  have productMono := mul_le_mul budgetMono lowMono (norm_nonneg _) (physicalBudget_nonnegative _ _ _ _ _)
  have cellPaid : originalCellNorm parameters (grade+shift) core≤cellConstants (grade+shift)*payment :=
    (cell (grade+shift)).trans (mul_le_mul_of_nonneg_left (add_le_add highMono productMono) (cellNonnegative _))
  have base := originalGradeNorm_zero_of_cellTame parameters core (cellConstants 0)
    ‖quotientEta parameters 20 source‖ (physicalBudget parameters field rho epsilon 20)
    (cellNonnegative _) (norm_nonneg _) bounded (by simpa only [zero_add] using cell 0)
  have lowHigh := referenceSource_norm_mono parameters (by omega : 20≤grade+loss) source
  have weightedLow : (1+physicalBudget parameters field rho epsilon (grade+shift+20))*‖quotientEta parameters 20 source‖≤payment := by
    have pieces := add_le_add lowHigh productMono
    dsimp only [payment]
    nlinarith only [pieces]
  have baseWeighted := mul_le_mul_of_nonneg_left base
    (add_nonneg zero_le_one (physicalBudget_nonnegative parameters field rho epsilon (grade+shift+20)))
  have basePayment := mul_le_mul_of_nonneg_left weightedLow (mul_nonneg (by norm_num : (0:ℝ)≤2) (cellNonnegative 0))
  have basePaid : (1+physicalBudget parameters field rho epsilon (grade+shift+20))*originalGradeNorm 0 core≤
      (2*cellConstants 0)*payment := by nlinarith only [baseWeighted,basePayment]
  have sourcePaid : ‖quotientEta parameters (grade+shift+20) source‖≤payment :=
    highMono.trans (le_add_of_nonneg_right (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _)))
  nlinarith only [cellPaid,basePaid,sourcePaid,weightedLow]

/-- A pure-cell endpoint alone is bounded by any larger fixed-loss payment. -/
theorem finiteJetCell_oneHigh_payment (parameters : PhaseParameters)
    (grade loss : ℕ) (lossLarge : 20≤loss) (constant : ℝ) (nonnegative : 0≤constant)
    (rho epsilon : ℝ) (field : ACore parameters 3)
    (source : SmoothQuotient parameters) (core : ACore parameters 3)
    (cell : originalCellNorm parameters grade core≤constant*
      (‖quotientEta parameters (grade+20) source‖+
        physicalBudget parameters field rho epsilon (grade+20)*‖quotientEta parameters 20 source‖)) :
    originalCellNorm parameters grade core≤constant*
      (‖quotientEta parameters (grade+loss) source‖+
        physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖) := by
  exact cell.trans (mul_le_mul_of_nonneg_left (add_le_add
    (referenceSource_norm_mono parameters (by omega : grade+20≤grade+loss) source)
    (mul_le_mul (physicalBudget_monotone parameters field rho epsilon (by omega : grade+20≤grade+loss))
      (referenceSource_norm_mono parameters lossLarge source) (norm_nonneg _)
      (physicalBudget_nonnegative _ _ _ _ _))) nonnegative)

end Grad.OriginalCoreRealization
