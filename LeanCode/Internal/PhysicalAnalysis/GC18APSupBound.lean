import GC18APFaithful
import FP17DiskSup

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apUnscaledDerivative_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (index : CartesianMultiIndex) (orderBound : cartesianOrder index ≤ grade) :
    ‖closedDerivativeL2 index (apWeightedJet sigma gamma ell cell field)‖ ≤
      ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have weighted := apWeighted_word_bound L sigma gamma ell cell field orderBound (cartesianMultiIndexWord index)
  have oneBound : 1 ≤ scaledCellWeight L ell cell ^ (grade - cartesianOrder index) :=
    one_le_pow₀ (scaledCellWeight_one_le L ell cell)
  exact (le_mul_of_one_le_left (norm_nonneg _) oneBound).trans weighted

def apSupConstant : ℝ := diskSupConstant * Real.sqrt 6

theorem apSupConstant_nonnegative : 0 ≤ apSupConstant := mul_nonneg diskSupConstant_pos.le (Real.sqrt_nonneg _)

theorem apWeightedSup_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (large : 2 ≤ grade)
    (cell : ℤ) (field : ClosedJet dimension) :
    ‖(apWeightedJet sigma gamma ell cell field).value‖ ≤
      apSupConstant * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have energyBound : diskSupEnergy (apWeightedJet sigma gamma ell cell field) ≤
      6 * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
    unfold diskSupEnergy
    calc
      _ ≤ ∑ _slot : Fin 6, ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 :=
        Finset.sum_le_sum (fun slot _ => pow_le_pow_left₀ (norm_nonneg _)
          (apUnscaledDerivative_bound L sigma gamma ell cell field (diskSupMultiIndex slot)
            ((diskSupMultiIndex_order_le_two slot).trans large)) 2)
      _ = _ := by simp
  have squareRootBound : Real.sqrt (diskSupEnergy (apWeightedJet sigma gamma ell cell field)) ≤
      Real.sqrt 6 * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)] using energyBound
  apply (ContinuousMap.norm_le _ (mul_nonneg apSupConstant_nonnegative (norm_nonneg _))).mpr
  intro point
  exact (diskSup_bound _ point).trans ((mul_le_mul_of_nonneg_left squareRootBound diskSupConstant_pos.le).trans_eq (mul_assoc _ _ _).symm)

end Grad.GaugeCoefficients.Physical.RadialLedger
