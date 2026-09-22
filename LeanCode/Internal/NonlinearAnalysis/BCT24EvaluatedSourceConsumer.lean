import BCT23EvaluatedPhysicalBoundary

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.RealFixedRanges

/-- The evaluated original-source AH22 consumer. The p norm is the full
mean-free P_R norm, xi has the positive-half norm, and the last term is the
unchanged original prescribed source norm with its actual endpoint trace
constant. All state quantifiers remain after the uniform constant. -/
theorem physicalBoundaryFromPrescribedSource_uniform_bound_sq
    (parameters : PhaseParameters) (L compact : ℝ) (positive : 0 < L)
    (angular cell : ℕ) (large : 3 ≤ angular + cell + 2) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
        (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
        (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
        (p : MeanFreeBoundaryPrimitive parameters angular cell)
        (xi : PositiveTrace parameters angular cell 1)
        (source : sourceRange parameters (angular + cell + 2) large),
      ‖physicalBoundaryFromPrescribedSource parameters L rho alpha delta parameter epsilon compact field
          small compactNonnegative alphaSmall deltaSmall parameterSmall angular cell large p xi source‖ ^ 2 ≤
        constant ^ 2 * (1 + physicalBudget parameters field rho epsilon (angular + cell + 8)) ^ 2 *
          (‖p‖ ^ 2 + 3 * ‖xi‖ ^ 2 +
            sourceOuterTraceConstant L (angular + cell) ^ 2 * ‖source.val‖ ^ 2) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    actualPhysicalBoundaryPR_uniform_bound parameters L compact angular cell
  refine ⟨constant, nonnegative, ?_⟩
  intro rho alpha delta parameter epsilon field small compactNonnegative alphaSmall deltaSmall parameterSmall p xi source
  have squared := pow_le_pow_left₀ (norm_nonneg _)
    (bound rho alpha delta parameter epsilon field small compactNonnegative alphaSmall deltaSmall parameterSmall
      (actualSevenSlotTrace parameters L angular cell p.val xi source.val)) 2
  rw [mul_pow, mul_pow] at squared
  exact squared.trans (mul_le_mul_of_nonneg_left
    (actualSevenSlotTrace_bound_sq parameters L positive angular cell p.val xi source.val)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end Grad.ActualBoundaryPrimitives
