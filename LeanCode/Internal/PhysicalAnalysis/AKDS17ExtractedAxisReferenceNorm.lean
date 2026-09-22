import AKDS16ActualFlatSourceReferenceNorm
import AXN5SourceProjectionBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.ChartAxisLift Grad.ChartAxisSourceBound Grad.ChartAxisProjections
open Grad.AxisSplit Grad.Q24Realization Grad.SmoothingFamily Grad.QuotientProjection

/-- The actual axis correction extracted from a full original source has
its same-reference tame estimate; the high state enters only once. -/
theorem extractedAxis_reference_bound (parameters : PhaseParameters) (length radius : ℝ)
    (positive : 0<radius) (bounded : radius≤1) (grade : ℕ) (large : 3≤grade)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ,0≤constant ∧ ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
      (base : RealJointCore parameters reference insideR)
      (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
      (source : sourceSmoothRange parameters),
      ‖stateToGrade parameters grade
        (realLift parameters radius positive bounded reference insideR seed insideS base axis
          (realExtraction parameters length source)).val‖ ≤
        constant*(‖quotientEta parameters (grade+3) source.val‖+
          (1+‖stateToGrade parameters grade base.2.val‖)*‖quotientEta parameters 3 source.val‖) := by
  obtain ⟨liftConstant,liftNonnegative,liftBound⟩ := referenceAxisDataCapLift_bound_on_patch parameters radius positive bounded
    grade large reference insideR seedPatch compact insidePatch
  let extractionConstant := 4*extractionBoundConstant length
  have extractionNonnegative : 0≤extractionConstant :=
    mul_nonneg (by norm_num) (extractionBoundConstant_nonneg length)
  refine ⟨liftConstant*extractionConstant,mul_nonneg liftNonnegative extractionNonnegative,?_⟩
  intro seed seedIn insideS base axis source
  let data := realExtraction parameters length source
  have lifted := liftBound seed seedIn insideS base axis data.val data.property
  have high := extractionData_bound_smooth parameters length grade source
  have low := extractionData_bound_smooth parameters length 0 source
  change axisDataNorm parameters grade data.val ≤ extractionConstant*‖quotientEta parameters (grade+3) source.val‖ at high
  change axisDataNorm parameters 0 data.val ≤ extractionConstant*‖quotientEta parameters 3 source.val‖ at low
  have tangentBound : tangentNorm (grade+1) (smoothingToTangent parameters base.2.val.1) ≤
      ‖stateToGrade parameters grade base.2.val‖ := by
    rw [axb_stateToGrade_literal_norm]
    linarith [originalGradeNorm_nonnegative grade base.2.val.2.1,originalGradeNorm_nonnegative grade base.2.val.2.2]
  have lowPaid := (mul_le_mul_of_nonneg_left low
    (add_nonneg zero_le_one (tangentNorm_nonneg _ _))).trans
      (mul_le_mul_of_nonneg_right (add_le_add_right tangentBound 1)
        (mul_nonneg extractionNonnegative (norm_nonneg _)))
  have paid := lifted.trans (mul_le_mul_of_nonneg_left (add_le_add high lowPaid) liftNonnegative)
  rw [realLift_eq_axisDataCapLift]
  exact paid.trans_eq (by dsimp only [extractionConstant]; ring)

end Grad.OriginalCoreRealization
