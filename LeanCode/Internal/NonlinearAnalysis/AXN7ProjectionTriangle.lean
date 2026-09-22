import AXN6CorrectionIdentity

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

namespace Grad.ChartAxisSourceBound

open Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.RealFixedRanges
open Grad.Q24Realization Grad.SmoothForward Grad.ChartAxisProjections

/-- The final source triangle, kept opaque from the analytic estimates to
avoid unfolding the real-subtype projection inside the large tame theorem. -/
theorem realRangeProjection_triangle
    {parameters : PhaseParameters} (cellLength radius : ℝ)
    (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : Grad.NonlinearQuotientBounds.ChartAxisCondition
      (smoothingChartCore parameters base.2.val))
    (grade : ℕ) (large : 4 ≤ grade) (source : sourceSmoothRange parameters)
    (liftConstant bracket : ℝ)
    (sourceBound :
      ‖sourceSmoothEmbedding parameters grade (forwardLarge large) source‖ ≤ bracket)
    (correctionBound :
      ‖sourceSmoothEmbedding parameters grade (forwardLarge large)
        (realSourceLift radius positive bounded cellLength reference insideR seed insideS
          base axis (realExtraction parameters cellLength source))‖ ≤
        liftConstant * bracket) :
    ‖sourceSmoothEmbedding parameters grade (forwardLarge large)
        (realRangeProjection radius positive bounded cellLength reference insideR seed insideS
          base axis source)‖ ≤ (1 + liftConstant) * bracket := by
  let correction := realSourceLift radius positive bounded cellLength reference insideR
    seed insideS base axis (realExtraction parameters cellLength source)
  have projected :
      realRangeProjection radius positive bounded cellLength reference insideR seed insideS
          base axis source = source + (-1 : ℝ) • correction := by
    unfold realRangeProjection
    rw [splittingProjection_apply]
  have embedded :
      sourceSmoothEmbedding parameters grade (forwardLarge large)
          (source + (-1 : ℝ) • correction) =
        sourceSmoothEmbedding parameters grade (forwardLarge large) source +
          (-1 : ℝ) •
            sourceSmoothEmbedding parameters grade (forwardLarge large) correction := by
    rw [(sourceSmoothEmbedding parameters grade (forwardLarge large)).map_add,
      (sourceSmoothEmbedding parameters grade (forwardLarge large)).map_smul]
  rw [projected, embedded]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  norm_num
  have correctionBound' :
      ‖sourceSmoothEmbedding parameters grade (forwardLarge large) correction‖ ≤
        liftConstant * bracket := by
    change ‖sourceSmoothEmbedding parameters grade (forwardLarge large)
      (realSourceLift radius positive bounded cellLength reference insideR seed insideS
        base axis (realExtraction parameters cellLength source))‖ ≤ _
    exact correctionBound
  exact (add_le_add sourceBound correctionBound').trans_eq (by ring)

end Grad.ChartAxisSourceBound
