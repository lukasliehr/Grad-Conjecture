import AKCQ4ActualEulerLogarithmicCalculus
import AW3Exponential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped ContDiff BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.AnalyticWeights.Higher

/-- Scalar specialization of the checked finite ordered Faà di Bruno
expansion. Every block retains its exact positive derivative rank. -/
theorem scalarExp_comp_expansion (field : ℝ → ℝ) (smooth : ContDiff ℝ ∞ field)
    (rank : ℕ) (point : ℝ) :
    iteratedFDeriv ℝ rank (fun location => Real.exp (field location)) point =
      ∑ partition : OrderedFinpartition rank,
        partition.compAlongOrderedFinpartition
          (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ (Real.exp (field point)))
          (fun block => iteratedFDeriv ℝ (partition.partSize block) field point) := by
  rw [show (fun location => Real.exp (field location)) = Real.exp ∘ field from rfl,
    iteratedFDeriv_comp Real.contDiff_exp.contDiffAt smooth.contDiffAt (by exact_mod_cast le_top)]
  simp only [FormalMultilinearSeries.taylorComp,FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]
  apply Finset.sum_congr rfl
  intro partition _
  rw [exp_iteratedFDeriv]

def scalarExpJetConstant (constants : ℕ → ℝ) (rank : ℕ) : ℝ :=
  ∑ partition : OrderedFinpartition rank, ∏ block, constants (partition.partSize block)

theorem scalarExpJetConstant_nonnegative (constants : ℕ → ℝ) (nonnegative : ∀ rank, 0 ≤ constants rank)
    (rank : ℕ) : 0 ≤ scalarExpJetConstant constants rank :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => nonnegative _))

/-- Total derivative rank is allocated once among positive phase blocks;
the exponential itself remains the original zeroth phase ratio. -/
theorem scalarExp_iterated_bound (field : ℝ → ℝ) (smooth : ContDiff ℝ ∞ field)
    (constants : ℕ → ℝ) (weight : ℝ) (point : ℝ)
    (bound : ∀ order : ℕ, 1 ≤ order → ‖iteratedDeriv order field point‖ ≤ constants order * weight^order)
    (rank : ℕ) :
    ‖iteratedDeriv rank (fun location => Real.exp (field location)) point‖ ≤
      scalarExpJetConstant constants rank * Real.exp (field point) * weight^rank := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,scalarExp_comp_expansion field smooth]
  calc
    _ ≤ ∑ partition : OrderedFinpartition rank,
        ‖partition.compAlongOrderedFinpartition
          (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ (Real.exp (field point)))
          (fun block => iteratedFDeriv ℝ (partition.partSize block) field point)‖ := norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition rank,
        (∏ block, constants (partition.partSize block)) * Real.exp (field point) * weight^rank := by
      apply Finset.sum_le_sum
      intro partition _
      calc
        _ ≤ ‖ContinuousMultilinearMap.piFieldEquiv ℝ (Fin partition.length) ℝ (Real.exp (field point))‖ *
            ∏ block, ‖iteratedFDeriv ℝ (partition.partSize block) field point‖ :=
          partition.norm_compAlongOrderedFinpartition_le _ _
        _ ≤ Real.exp (field point) * ∏ block, constants (partition.partSize block) * weight^(partition.partSize block) := by
          rw [LinearIsometryEquiv.norm_map,Real.norm_of_nonneg (Real.exp_pos _).le]
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro block _
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          exact bound _ (partition.partSize_pos block)
        _ = _ := by
          rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,partition_size_sum]
          ring
    _ = _ := by
      simp only [scalarExpJetConstant,Finset.sum_mul]

end Grad.OriginalCartesianTameEstimate
