import AXN3UniformPhysicalForward
import ASL8SourceLiftConsumer

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 2400000

namespace Grad.ChartAxisSourceBound

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.RealFixedRanges
open Grad.Q24Realization Grad.ChartAxisLift Grad.PhysicalCoordinates
open Grad.AxisSourceLift Grad.SmoothForward
open Grad.ConstrainedGrades

theorem axisDataNorm_mono {parameters : PhaseParameters} {lower upper : ℕ}
    (ordered : lower ≤ upper) (data : AxisData parameters) :
    axisDataNorm parameters lower data ≤ axisDataNorm parameters upper data :=
  add_le_add (axisGradeNorm_mono parameters (by omega) data.1)
    (axisGradeNorm_mono parameters (by omega) data.2)

theorem baseAxisNorm_le_stateNorm (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade)
    (base : stateSmoothRange parameters reference insideR) :
    tangentNorm (grade + 1) (smoothingToTangent parameters base.val.1) ≤
      ‖stateSmoothEmbedding parameters reference insideR grade large base‖ := by
  rw [stateSmoothEmbedding_norm, Grad.ChartAxisLift.axb_stateToGrade_literal_norm]
  exact (le_add_of_nonneg_right
      (originalGradeNorm_nonnegative grade base.val.2.1)).trans
    (le_add_of_nonneg_right
      (originalGradeNorm_nonnegative grade base.val.2.2))

/-- AL28: the literal localized source lift `T_b = A_b E_b` obeys the
original six-loss one-high estimate.  The constant is uniform on the exact
compact seed patch and bounded curvature/low-state set. -/
theorem axisSourceLift_bound_on_patch
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
          (data : AxisData parameters) (real : RealAxisData data),
          ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base.2‖ ≤
              stateBound →
          ‖sourceSmoothEmbedding parameters grade (forwardLarge large)
              (axisSourceLift parameters cellLength radius positive bounded
                reference insideR seed insideS base axis data real)‖ ≤
            constant * (axisDataNorm parameters (grade + 6) data +
              (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
                (realHighLarge grade) base.2‖) * axisDataNorm parameters 4 data) := by
  obtain ⟨forwardConstant, forwardNonnegative, forwardBound⟩ :=
    actualPhysicalSmoothForward_tame_on_patch parameters cellLength reference insideR
      grade large seedPatch compact insidePatch curvatureBound stateBound
  obtain ⟨highConstant, highNonnegative, highBound⟩ :=
    referenceAxisDataCapLift_bound_on_patch parameters radius positive bounded
      (grade + 6) (by omega) reference insideR seedPatch compact insidePatch
  obtain ⟨lowConstant, lowNonnegative, lowBound⟩ :=
    referenceAxisDataCapLift_bound_on_patch parameters radius positive bounded
      4 (by omega) reference insideR seedPatch compact insidePatch
  let liftConstant := highConstant + lowConstant * (2 + |stateBound|)
  have liftNonnegative : 0 ≤ liftConstant := by
    dsimp [liftConstant]
    positivity
  refine ⟨forwardConstant * liftConstant,
    mul_nonneg forwardNonnegative liftNonnegative, ?_⟩
  intro seed member insideS base curvature axis data real baseLow
  let lift := axisDataCapLift parameters radius positive bounded reference insideR
    seed insideS base axis data real
  let highBase :=
    ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
      (realHighLarge grade) base.2‖
  let highData := axisDataNorm parameters (grade + 6) data
  let lowData := axisDataNorm parameters 4 data
  let bracket := highData + (1 + highBase) * lowData
  have highBaseNonnegative : 0 ≤ highBase := norm_nonneg _
  have highDataNonnegative : 0 ≤ highData := axisDataNorm_nonneg _ _ _
  have lowDataNonnegative : 0 ≤ lowData := axisDataNorm_nonneg _ _ _
  have bracketNonnegative : 0 ≤ bracket := by
    dsimp [bracket]
    positivity
  have dataMono : axisDataNorm parameters 0 data ≤ lowData := by
    dsimp [lowData]
    exact axisDataNorm_mono (by omega) data
  have baseAxisHigh :
      tangentNorm ((grade + 6) + 1) (smoothingToTangent parameters base.2.val.1) ≤
        highBase := by
    change tangentNorm ((grade + 6) + 1)
        (smoothingToTangent parameters base.2.val.1) ≤
      ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
        (realHighLarge grade) base.2‖
    exact baseAxisNorm_le_stateNorm parameters reference insideR
      (grade + 6) (realHighLarge grade) base.2
  have highRaw := highBound seed member insideS base axis data real
  have highLift :
      ‖Grad.SmoothingFamily.stateToGrade parameters (grade + 6) lift.val‖ ≤
        highConstant * bracket := by
    apply highRaw.trans
    apply mul_le_mul_of_nonneg_left _ highNonnegative
    change axisDataNorm parameters (grade + 6) data +
        (1 + tangentNorm ((grade + 6) + 1)
          (smoothingToTangent parameters base.2.val.1)) *
            axisDataNorm parameters 0 data ≤
      axisDataNorm parameters (grade + 6) data +
        (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
          (realHighLarge grade) base.2‖) * axisDataNorm parameters 4 data
    apply add_le_add le_rfl
    exact mul_le_mul (add_le_add_right baseAxisHigh 1) dataMono
      (axisDataNorm_nonneg parameters 0 data) (by positivity)
  have baseAxisLow :
      tangentNorm (4 + 1) (smoothingToTangent parameters base.2.val.1) ≤
        |stateBound| := by
    exact (baseAxisNorm_le_stateNorm parameters reference insideR 4 realLowLarge base.2).trans
      (baseLow.trans (le_abs_self stateBound))
  have lowRaw := lowBound seed member insideS base axis data real
  have lowLift :
      ‖Grad.SmoothingFamily.stateToGrade parameters 4 lift.val‖ ≤
        (lowConstant * (2 + |stateBound|)) * lowData := by
    apply lowRaw.trans
    have inner : axisDataNorm parameters 4 data +
        (1 + tangentNorm (4 + 1) (smoothingToTangent parameters base.2.val.1)) *
          axisDataNorm parameters 0 data ≤
        (2 + |stateBound|) * lowData := by
      have product :
          (1 + tangentNorm (4 + 1) (smoothingToTangent parameters base.2.val.1)) *
              axisDataNorm parameters 0 data ≤
            (1 + |stateBound|) * lowData :=
        mul_le_mul (add_le_add_right baseAxisLow 1) dataMono
          (axisDataNorm_nonneg parameters 0 data) (by positivity)
      calc
        axisDataNorm parameters 4 data +
              (1 + tangentNorm (4 + 1)
                (smoothingToTangent parameters base.2.val.1)) *
                axisDataNorm parameters 0 data ≤
            lowData + (1 + |stateBound|) * lowData :=
          add_le_add le_rfl product
        _ = (2 + |stateBound|) * lowData := by ring
    exact (mul_le_mul_of_nonneg_left inner lowNonnegative).trans_eq (by ring)
  let highDirection := stateSmoothEmbedding parameters reference insideR (grade + 6)
    (realHighLarge grade) lift
  have forward := forwardBound seed member insideS base curvature axis baseLow highDirection
  have sourceIdentity := axisSourceLift_actual_forward cellLength radius positive bounded
    reference insideR seed insideS grade large base axis data real
  rw [sourceIdentity] at forward
  rw [stateLowering_core, stateSmoothEmbedding_norm,
    stateSmoothEmbedding_norm] at forward
  have lowTerm : (1 + highBase) *
      ‖Grad.SmoothingFamily.stateToGrade parameters 4 lift.val‖ ≤
      (lowConstant * (2 + |stateBound|)) * bracket := by
    have first := mul_le_mul_of_nonneg_left lowLift (by positivity : 0 ≤ 1 + highBase)
    have omitted : 0 ≤ (lowConstant * (2 + |stateBound|)) * highData := by
      positivity
    dsimp [bracket]
    nlinarith
  have total : (1 + highBase) *
        ‖Grad.SmoothingFamily.stateToGrade parameters 4 lift.val‖ +
      ‖Grad.SmoothingFamily.stateToGrade parameters (grade + 6) lift.val‖ ≤
        liftConstant * bracket := by
    have sum := add_le_add lowTerm highLift
    dsimp [liftConstant]
    nlinarith
  apply forward.trans
  exact (mul_le_mul_of_nonneg_left total forwardNonnegative).trans_eq (by ring)

end Grad.ChartAxisSourceBound
