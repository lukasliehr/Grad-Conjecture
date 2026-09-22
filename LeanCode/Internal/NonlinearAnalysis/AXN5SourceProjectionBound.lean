import AXN4AxisSourceLiftBound
import AXJ8ExactSplitting

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 2400000

namespace Grad.ChartAxisSourceBound

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.RealFixedRanges
open Grad.Q24Realization Grad.ChartAxisLift Grad.PhysicalCoordinates
open Grad.AxisSourceLift Grad.SmoothForward Grad.ConstrainedGrades
open Grad.ChartAxisSplit Grad.ChartAxisProjections
open Grad.QuotientProjection

theorem extractionData_bound_smooth (parameters : PhaseParameters)
    (cellLength : ℝ) (grade : ℕ) (source : sourceSmoothRange parameters) :
    axisDataNorm parameters grade (extractionData cellLength source.val) ≤
      (4 * extractionBoundConstant cellLength) *
        ‖sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade) source‖ := by
  have bound := completedExtraction_bound parameters cellLength grade
    (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade) source)
  rw [completedExtraction_core, axisDataEmbedding_norm] at bound
  exact bound

theorem sourceSmoothEmbedding_mono (parameters : PhaseParameters)
    (lower upper : ℕ) (lowerLarge : 3 ≤ lower) (ordered : lower ≤ upper)
    (source : sourceSmoothRange parameters) :
    ‖sourceSmoothEmbedding parameters lower lowerLarge source‖ ≤
      ‖sourceSmoothEmbedding parameters upper (lowerLarge.trans ordered) source‖ := by
  have bound := sourceLowering_norm_le parameters lowerLarge ordered
    (sourceSmoothEmbedding parameters upper (lowerLarge.trans ordered) source)
  rw [sourceLowering_core] at bound
  exact bound

/-- Applying the AL28 lift to the actual extraction costs exactly the three
grades of AL10: high `q+9`, low seven, and state base `q+6`. -/
theorem extractedAxisSourceLift_bound_on_patch
    (parameters : PhaseParameters) (cellLength : ℝ)
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
              (axisSourceLift parameters cellLength radius positive bounded reference insideR
                seed insideS base axis (extractionData cellLength source.val)
                  (extractionData_real cellLength source))‖ ≤
            constant *
              (‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ +
                (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
                  (realHighLarge grade) base.2‖) *
                  ‖sourceSmoothEmbedding parameters 7 (by omega) source‖) := by
  obtain ⟨liftConstant, liftNonnegative, liftBound⟩ :=
    axisSourceLift_bound_on_patch parameters cellLength radius positive bounded
      reference insideR grade large seedPatch compact insidePatch curvatureBound stateBound
  let extractionConstant := 4 * extractionBoundConstant cellLength
  have extractionNonnegative : 0 ≤ extractionConstant := by
    dsimp [extractionConstant]
    exact mul_nonneg (by norm_num) (extractionBoundConstant_nonneg cellLength)
  let constant := liftConstant * extractionConstant
  have constantNonnegative : 0 ≤ constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, constantNonnegative, ?_⟩
  intro seed member insideS base curvature axis source baseLow
  let realData := realExtraction parameters cellLength source
  let data := realData.val
  have real : RealAxisData data := realData.property
  have lifted := liftBound seed member insideS base curvature axis data real baseLow
  have highExtractionRaw := extractionData_bound_smooth parameters cellLength
    (grade + 6) source
  have highExtraction : axisDataNorm parameters (grade + 6) data ≤
      extractionConstant *
        ‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖ := by
    change axisDataNorm parameters (grade + 6) (extractionData cellLength source.val) ≤
      extractionConstant *
        ‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖
    simpa only [extractionConstant, Nat.add_assoc, Nat.reduceAdd] using
      highExtractionRaw
  have lowExtractionRaw := extractionData_bound_smooth parameters cellLength 4 source
  have lowExtraction : axisDataNorm parameters 4 data ≤
      extractionConstant *
        ‖sourceSmoothEmbedding parameters 7 (by omega) source‖ := by
    change axisDataNorm parameters 4 (extractionData cellLength source.val) ≤
      extractionConstant *
        ‖sourceSmoothEmbedding parameters 7 (by omega) source‖
    simpa only [extractionConstant, Nat.reduceAdd] using lowExtractionRaw
  let highSource :=
    ‖sourceSmoothEmbedding parameters (grade + 9) (by omega) source‖
  let lowSource := ‖sourceSmoothEmbedding parameters 7 (by omega) source‖
  let highBase :=
    ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
      (realHighLarge grade) base.2‖
  let bracket := highSource + (1 + highBase) * lowSource
  exact lifted.trans (by
    have inner : axisDataNorm parameters (grade + 6) data +
          (1 + highBase) * axisDataNorm parameters 4 data ≤
        extractionConstant * bracket := by
      apply (add_le_add highExtraction
        (mul_le_mul_of_nonneg_left lowExtraction (by positivity))).trans_eq
      dsimp [bracket, highSource, lowSource]
      ring
    exact (mul_le_mul_of_nonneg_left inner liftNonnegative).trans_eq (by ring))

end Grad.ChartAxisSourceBound
