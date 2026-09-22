import AAQ10ActualSolutionFluxGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem four_term_nonnegative_bound (a b c d x y z w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    a * x + b * y + c * z + d * w ≤ (a + b + c + d) * (x + y + z + w) := by
  have h1 := mul_le_mul_of_nonneg_left (show x ≤ x + y + z + w by linarith) ha
  have h2 := mul_le_mul_of_nonneg_left (show y ≤ x + y + z + w by linarith) hb
  have h3 := mul_le_mul_of_nonneg_left (show z ≤ x + y + z + w by linarith) hc
  have h4 := mul_le_mul_of_nonneg_left (show w ≤ x + y + z + w by linarith) hd
  nlinarith only [h1, h2, h3, h4]

def annularFluxPhysicalTraceConstant (lower length : ℝ) : ℝ :=
  annularFluxTraceConstant lower *
    (4 * (1 + annularFluxPotentialConstant lower length + lower⁻¹) +
      (annularFluxPotentialConstant lower length + (4 / 3 : ℝ) * lower⁻¹ ^ 2) + 1 + length⁻¹)

section Physical
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularDataFluxTrace_physical_bound (endpoint : Fin 2)
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength) :
    ‖annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data‖ ≤
      annularFluxPhysicalTraceConstant lower length *
        (‖data.val.1‖ + ‖data.val.2.1‖ + ‖data.val.2.2.1‖ + ‖data.val.2.2.2.1‖) := by
  let q := annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength data.val
  let slope := annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength data.val
  let A := 1 + annularFluxPotentialConstant lower length + lower⁻¹
  let B := annularFluxPotentialConstant lower length + (4 / 3 : ℝ) * lower⁻¹ ^ 2
  have aNonnegative : 0 ≤ A := by
    dsimp [A]
    have := annularFluxPotentialConstant_nonnegative lower length
    positivity
  have bNonnegative : 0 ≤ B := add_nonneg (annularFluxPotentialConstant_nonnegative lower length) (by positivity)
  have basic := annularFluxTrace_bound lower positive bounded endpoint
    (annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength data)
  change ‖annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data‖ ≤
    annularFluxTraceConstant lower * (‖q‖ + ‖slope‖) at basic
  have slopeBound := annularFluxSlope_physical_bound parameters lower length positive lengthPositive widthHalf widthLength data.val
  have qBound : ‖q‖ ≤ 3 * ‖data.val.1‖ + ‖data.val.2.1‖ :=
    annularRecoveredQ_bound parameters lower length positive lengthPositive widthHalf widthLength data.val.1 data.val.2.1
  have sumBound : ‖q‖ + ‖slope‖ ≤
      (3 * A + B) * ‖data.val.1‖ + A * ‖data.val.2.1‖ + ‖data.val.2.2.1‖ + length⁻¹ * ‖data.val.2.2.2.1‖ := by
    have scaled := mul_le_mul_of_nonneg_left qBound aNonnegative
    dsimp only [q, slope, A, B] at scaled ⊢
    nlinarith
  have enlarged := four_term_nonnegative_bound (3 * A + B) A 1 length⁻¹
    ‖data.val.1‖ ‖data.val.2.1‖ ‖data.val.2.2.1‖ ‖data.val.2.2.2.1‖
    (by positivity) aNonnegative (by norm_num) (inv_nonneg.mpr lengthPositive.le)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have total := basic.trans (mul_le_mul_of_nonneg_left (sumBound.trans (by simpa only [one_mul] using enlarged))
    (annularFluxTraceConstant_nonnegative lower))
  have rearrange : annularFluxTraceConstant lower *
      ((3 * A + B + A + 1 + length⁻¹) *
        (‖data.val.1‖ + ‖data.val.2.1‖ + ‖data.val.2.2.1‖ + ‖data.val.2.2.2.1‖)) =
      annularFluxPhysicalTraceConstant lower length *
        (‖data.val.1‖ + ‖data.val.2.1‖ + ‖data.val.2.2.1‖ + ‖data.val.2.2.2.1‖) := by
    unfold annularFluxPhysicalTraceConstant
    dsimp only [A, B]
    ring
  exact total.trans_eq rearrange


theorem annularSolutionFluxTrace_physical_bound (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary) :
    ‖annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data‖ ≤
      annularFluxPhysicalTraceConstant lower length *
        (‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data‖ +
          ‖data.1.1‖ + ‖data.1.2.1‖ + ‖data.1.2.2.1‖) :=
  annularDataFluxTrace_physical_bound parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
    (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data)

end Physical
end Grad.AnnularFluxTrace
