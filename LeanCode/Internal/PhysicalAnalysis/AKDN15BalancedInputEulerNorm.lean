import AKDN14SameNativeBalancedInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness

def balancedInputApply :
    (PhysicalHilbertPair →L[ℂ] CellL2 7) →L[ℝ] PhysicalHilbertPair →L[ℝ] CellL2 7 :=
  ((ContinuousLinearMap.apply ℝ (CellL2 7)).flip).comp
    (ContinuousLinearMap.restrictScalarsIsometry ℂ PhysicalHilbertPair (CellL2 7) ℝ ℝ).toContinuousLinearMap

theorem balancedSevenInput_smooth (parameters : PhaseParameters) :
    ContDiff ℝ ∞ (balancedSevenInput parameters) := by
  rw [show balancedSevenInput parameters = fun point => balancedSevenInput parameters 0+point • balancedSevenInputSlope parameters from
    funext (balancedSevenInput_affine parameters)]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

/-- The actual seven-slot kinematic map consumes no derivative budget.
Its genuine Euler derivatives only produce lower native Euler ranks. -/
theorem balancedInputCurve_EulerBound (parameters : PhaseParameters) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (lower : ℝ) (_positive : 0 < lower) (_bounded : lower < 1)
      (curve : ℝ → PhysicalHilbertPair) (rank : ℕ),
    ContDiffOn ℝ rank curve (Icc lower 1) →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => balancedSevenInput parameters point (curve point)) radius.val‖ ≤
      constant*eulerAllocationSum
        (fun _ inputRank => ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank curve radius.val‖)
        (eulerLeibnizTerms rank) := by
  obtain ⟨constant,constant0,bound⟩ := balancedSevenInputEuler_bound parameters
  refine ⟨constant,constant0,?_⟩
  intro lower positive bounded curve rank curveSmooth radius inside
  have operatorSmooth : ContDiffOn ℝ rank (balancedSevenInput parameters) (Icc lower 1) :=
    contDiffOn_infty.mp (balancedSevenInput_smooth parameters).contDiffOn rank
  have actual := vectorEulerWithin_bilinear balancedInputApply (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') (balancedSevenInput parameters) curve rank operatorSmooth curveSmooth inside
  change vectorEulerWithinIteratedDerivative (Icc lower 1) rank
    (fun point => balancedSevenInput parameters point (curve point)) radius.val = _ at actual
  rw [actual,eulerAllocationSum_mul_left]
  apply (bilinearEulerPolynomial_norm balancedInputApply _ _ _ radius.val).trans
  apply eulerAllocationSum_mono
  intro term _
  change ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.1 (balancedSevenInput parameters) radius.val
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 curve radius.val)‖ ≤ _
  rw [balancedSevenInputEuler_fidelity parameters lower positive bounded term.1 radius.val inside]
  exact ((balancedSevenInputEuler parameters term.1 radius).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (bound term.1 radius) (norm_nonneg _))

end Grad.OriginalCartesianTameEstimate
