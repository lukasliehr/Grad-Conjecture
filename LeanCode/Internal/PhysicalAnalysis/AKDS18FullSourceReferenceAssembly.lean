import AKDS17ExtractedAxisReferenceNorm
import AXJ8ExactSplitting

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RealFixedRanges
open Grad.ChartAxisLift Grad.ChartAxisProjections Grad.Q24Realization Grad.SmoothingFamily
open Grad.QuotientProjection Grad.PhysicalCoordinates

/-- The actual axis extraction and any solution of the literal projected
source assemble a full original preimage, with the same reference norm.
The flat payment is retained explicitly for the analytic inverse consumer. -/
theorem fullSource_reference_assembly (parameters : PhaseParameters) (length radius : ℝ)
    (positive : 0<radius) (bounded : radius≤1)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constants : ℕ→ℝ, (∀ grade,0≤constants grade) ∧
      ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR)
        (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
        (source : sourceSmoothRange parameters)
        (flatState : stateSmoothRange parameters reference insideR)
        (flatPayment : ℕ→ℝ),
        literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis flatState =
          realRangeProjection radius positive bounded length reference insideR seed insideS base axis source →
        (∀ grade, ‖stateToGrade parameters grade flatState.val‖ ≤ flatPayment grade) →
        ∃ reconstructed : stateSmoothRange parameters reference insideR,
          literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis reconstructed=source ∧
          ∀ grade, 3≤grade → ‖stateToGrade parameters grade reconstructed.val‖ ≤
            constants grade*(‖quotientEta parameters (grade+3) source.val‖+
              (1+‖stateToGrade parameters grade base.2.val‖)*‖quotientEta parameters 3 source.val‖)+
              flatPayment grade := by
  let constants := fun grade => (extractedAxis_reference_bound parameters length radius positive bounded
    (max 3 grade) (le_max_left _ _) reference insideR seedPatch compact insidePatch).choose
  have constantsNonnegative : ∀ grade,0≤constants grade := fun grade =>
    (extractedAxis_reference_bound parameters length radius positive bounded (max 3 grade)
      (le_max_left _ _) reference insideR seedPatch compact insidePatch).choose_spec.1
  refine ⟨constants,constantsNonnegative,?_⟩
  intro seed seedIn insideS base axis source flatState flatPayment flatLaw flatBound
  let axisState := realLift parameters radius positive bounded reference insideR seed insideS base axis
    (realExtraction parameters length source)
  refine ⟨axisState+flatState,?_,?_⟩
  · rw [map_add,flatLaw,realRangeProjection_sub]
    have axisLaw : literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis axisState =
        realSourceLift radius positive bounded length reference insideR seed insideS base axis
          (realExtraction parameters length source) :=
      (realSourceLift_apply radius positive bounded length reference insideR seed insideS base axis _).symm
    rw [axisLaw]
    abel
  · intro grade large
    have axisBound := (extractedAxis_reference_bound parameters length radius positive bounded
      (max 3 grade) (le_max_left _ _) reference insideR seedPatch compact insidePatch).choose_spec.2
      seed seedIn insideS base axis source
    change ‖stateToGrade parameters (max 3 grade) axisState.val‖ ≤ constants grade*_
      at axisBound
    rw [max_eq_right large] at axisBound
    change ‖stateToGrade parameters grade (axisState.val+flatState.val)‖ ≤ _
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add axisBound (flatBound grade))

end Grad.OriginalCoreRealization
