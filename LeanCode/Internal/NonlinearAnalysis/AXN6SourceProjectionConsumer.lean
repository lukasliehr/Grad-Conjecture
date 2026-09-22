import AXN5SourceProjectionBound
import AXN6CorrectionIdentity
import AXN7ProjectionTriangle
import AXJ8ExactSplitting

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 4000000

namespace Grad.ChartAxisSourceBound

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.RealFixedRanges
open Grad.Q24Realization Grad.ChartAxisLift Grad.PhysicalCoordinates
open Grad.AxisSourceLift Grad.SmoothForward Grad.ConstrainedGrades
open Grad.ChartAxisSplit Grad.ChartAxisProjections Grad.QuotientProjection

/-- AL29: the exact real source projection has the original nine-loss tame
bound.  The high source appears only at `q+9`, the low source only at grade
seven, and the base only at state grade `q+6`. -/
theorem realRangeProjection_bound_on_patch
    (parameters : PhaseParameters) (cellLength : ℝ) (_positiveLength : 0 < cellLength)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain)
    (curvatureBound stateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR),
        |base.1| ≤ curvatureBound →
        ∀ (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
          (source : sourceSmoothRange parameters),
          ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base.2‖ ≤
              stateBound →
          ‖sourceSmoothEmbedding parameters grade (forwardLarge large)
              (realRangeProjection radius positive bounded cellLength reference insideR
                seed insideS base axis source)‖ ≤
            constant *
              (‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ +
                (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
                  (realHighLarge grade) base.2‖) *
                  ‖sourceSmoothEmbedding parameters 7 (by omega) source‖) := by
  obtain ⟨liftConstant, liftNonnegative, liftBound⟩ :=
    extractedAxisSourceLift_bound_on_patch parameters cellLength radius positive bounded
      reference insideR grade large seedPatch compact insidePatch curvatureBound stateBound
  let constant := 1 + liftConstant
  have constantNonnegative : 0 ≤ constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, constantNonnegative, ?_⟩
  intro seed member insideS base curvature axis source baseLow
  have lifted := liftBound seed member insideS base curvature axis source baseLow
  have highLe :
      ‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ ≤
        ‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ +
          (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
            (realHighLarge grade) base.2‖) *
            ‖sourceSmoothEmbedding parameters 7 (by omega) source‖ :=
    le_add_of_nonneg_right (mul_nonneg (by positivity) (norm_nonneg _))
  have sourceMono :
      ‖sourceSmoothEmbedding parameters grade (forwardLarge large) source‖ ≤
        ‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ := by
    have bound := zLowering_norm_le parameters (show grade ≤ grade + 9 by omega)
      (quotientEta parameters (grade + 9) source.val)
    rw [zLowering_core] at bound
    exact bound
  let realData := realExtraction parameters cellLength source
  let correction := realSourceLift radius positive bounded cellLength reference insideR
    seed insideS base axis realData
  have correctionBound :
      ‖sourceSmoothEmbedding parameters grade (forwardLarge large) correction‖ ≤
        liftConstant *
          (‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ +
            (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
              (realHighLarge grade) base.2‖) *
              ‖sourceSmoothEmbedding parameters 7 (by omega) source‖) := by
    rw [show correction = realSourceLift radius positive bounded cellLength reference insideR
      seed insideS base axis realData from rfl]
    rw [show realData = realExtraction parameters cellLength source from rfl]
    rw [realSourceLift_extraction_eq_axisSourceLift]
    change ‖(sourceSmoothEmbedding parameters grade (forwardLarge large)
        (axisSourceLift parameters cellLength radius positive bounded reference insideR
          seed insideS base axis (extractionData cellLength source.val)
            (extractionData_real cellLength source))).val‖ ≤ _
    change ‖(sourceSmoothEmbedding parameters grade (forwardLarge large)
        (axisSourceLift parameters cellLength radius positive bounded reference insideR
          seed insideS base axis (extractionData cellLength source.val)
            (extractionData_real cellLength source))).val‖ ≤ _ at lifted
    exact lifted
  change _ ≤ (1 + liftConstant) * _
  exact realRangeProjection_triangle cellLength radius positive bounded reference insideR
    seed insideS base axis grade large source liftConstant
      (‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ +
        (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
          (realHighLarge grade) base.2‖) *
          ‖sourceSmoothEmbedding parameters 7 (by omega) source‖)
    (sourceMono.trans highLe) correctionBound

/-- Exact public AL29 consumer: the projection is the literal source minus
the actual forward of the accepted localized right inverse. -/
theorem realRangeProjection_is_source_minus_actual_lift
    {parameters : PhaseParameters} (cellLength radius : ℝ)
    (positive : 0 < radius) (bounded : radius ≤ 1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (source : sourceSmoothRange parameters) :
    realRangeProjection radius positive bounded cellLength reference insideR seed insideS
        base axis source =
      source - axisSourceLift parameters cellLength radius positive bounded reference insideR
        seed insideS base axis (extractionData cellLength source.val)
          (extractionData_real cellLength source) := by
  rw [realRangeProjection_sub,
    realSourceLift_extraction_eq_axisSourceLift cellLength radius positive bounded reference
      insideR seed insideS base axis source]

end Grad.ChartAxisSourceBound
