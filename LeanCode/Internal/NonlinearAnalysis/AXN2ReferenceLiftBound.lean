import AXN1ReverseTransferBound
import AXL23AxisDataLift

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

namespace Grad.ChartAxisSourceBound

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.Q24Realization
open Grad.ChartAxisLift Grad.ConstrainedTransfer
open Grad.NonlinearProduct Grad.Constraints.Gauges

/-- The exact state-core N18 transport back to the fixed reference is
uniformly same-grade bounded on compact moving-seed patches. -/
theorem reverseCoreTransfer_bound_on_patch
    (parameters : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
        (state : Grad.SmoothingFamily.StateCore parameters),
        ‖Grad.SmoothingFamily.stateToGrade parameters grade
            (coreTransfer parameters seed inside reference insideR state)‖ ≤
          constant * ‖Grad.SmoothingFamily.stateToGrade parameters grade state‖ := by
  obtain ⟨vectorConstant, vectorNonnegative, vectorBound⟩ :=
    reverseSeedTransferCore_bound_on_patch parameters grade reference insideR
      seedPatch compact insidePatch
  refine ⟨1 + vectorConstant, by linarith, ?_⟩
  intro seed member inside state
  have vector := vectorBound seed member inside state.2.1
  rw [coreTransfer_apply,
    Grad.ChartAxisLift.axb_stateToGrade_literal_norm,
    Grad.ChartAxisLift.axb_stateToGrade_literal_norm]
  change tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
      originalGradeNorm grade
        (seedTransfer parameters seed inside reference insideR state.2.1) +
      originalGradeNorm grade state.2.2 ≤
    (1 + vectorConstant) *
      (tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
        originalGradeNorm grade state.2.1 + originalGradeNorm grade state.2.2)
  have tangentNonnegative := tangentNorm_nonneg (grade + 1)
    (smoothingToTangent parameters state.1)
  have fieldNonnegative := originalGradeNorm_nonnegative grade state.2.1
  have scalarNonnegative := originalGradeNorm_nonnegative grade state.2.2
  have factor : 1 ≤ 1 + vectorConstant := by linarith
  have vectorFactor : vectorConstant ≤ 1 + vectorConstant := by linarith
  have tangentScale :
      tangentNorm (grade + 1) (smoothingToTangent parameters state.1) ≤
        (1 + vectorConstant) *
          tangentNorm (grade + 1) (smoothingToTangent parameters state.1) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right factor tangentNonnegative
  have fieldScale : vectorConstant * originalGradeNorm grade state.2.1 ≤
      (1 + vectorConstant) * originalGradeNorm grade state.2.1 :=
    mul_le_mul_of_nonneg_right vectorFactor fieldNonnegative
  have scalarScale : originalGradeNorm grade state.2.2 ≤
      (1 + vectorConstant) * originalGradeNorm grade state.2.2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right factor scalarNonnegative
  calc
    tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
          originalGradeNorm grade
            (seedTransfer parameters seed inside reference insideR state.2.1) +
        originalGradeNorm grade state.2.2 ≤
        tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
            vectorConstant * originalGradeNorm grade state.2.1 +
          originalGradeNorm grade state.2.2 :=
      add_le_add (add_le_add le_rfl vector) le_rfl
    _ ≤ (1 + vectorConstant) *
            tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
          (1 + vectorConstant) * originalGradeNorm grade state.2.1 +
        (1 + vectorConstant) * originalGradeNorm grade state.2.2 :=
      add_le_add (add_le_add tangentScale fieldScale) scalarScale
    _ = (1 + vectorConstant) *
        (tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
          originalGradeNorm grade state.2.1 + originalGradeNorm grade state.2.2) := by
      ring

/-- AL27 transported through the actual accepted N18 inverse.  This is the
fixed-reference lift which is fed to the completed physical derivative. -/
theorem referenceAxisDataCapLift_bound_on_patch
    (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (bounded : radius ≤ 1) (grade : ℕ) (gradeMin : 3 ≤ grade)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR)
        (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
        (data : AxisData parameters) (real : RealAxisData data),
        ‖Grad.SmoothingFamily.stateToGrade parameters grade
            (axisDataCapLift parameters radius positive bounded reference insideR
              seed insideS base axis data real).val‖ ≤
          constant * (axisDataNorm parameters grade data +
            (1 + tangentNorm (grade + 1)
              (smoothingToTangent parameters base.2.val.1)) *
                axisDataNorm parameters 0 data) := by
  obtain ⟨transferConstant, transferNonnegative, transferBound⟩ :=
    reverseCoreTransfer_bound_on_patch parameters grade reference insideR
      seedPatch compact insidePatch
  obtain ⟨liftConstant, liftNonnegative, liftBound⟩ :=
    axisDataCapLiftLinear_bound_on_patch (parameters := parameters)
      radius positive grade gradeMin seedPatch compact insidePatch
  refine ⟨transferConstant * liftConstant,
    mul_nonneg transferNonnegative liftNonnegative, ?_⟩
  intro seed member insideS base axis data real
  let raw := axisDataCapLiftLinear parameters radius positive seed insideS
    (smoothingToTangent parameters base.2.val.1) data
  have transported := transferBound seed member insideS raw
  have rawBound := liftBound seed member insideS
    (smoothingToTangent parameters base.2.val.1) axis data
  have identify :
      (axisDataCapLift parameters radius positive bounded reference insideR
        seed insideS base axis data real).val =
      coreTransfer parameters seed insideS reference insideR raw := rfl
  rw [identify]
  exact transported.trans
    ((mul_le_mul_of_nonneg_left rawBound transferNonnegative).trans_eq (by ring))

end Grad.ChartAxisSourceBound
