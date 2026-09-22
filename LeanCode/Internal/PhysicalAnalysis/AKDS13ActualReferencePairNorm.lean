import AKDS12ActualOriginalUSOneHigh
import AKCU3NativeReferenceSolution
import AXN2ReferenceLiftBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RealFixedRanges
open Grad.PhysicalCoordinates Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisSourceBound
open Grad.Q24Realization Grad.SmoothingFamily Grad.NonlinearProduct

/-- Original reference norm for the SAME recovered physical pair, uniformly
on the existing compact seed patch. The inverse N18 transfer costs no grade. -/
theorem actualReferencePair_bound_on_patch (parameters : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ,0≤constant ∧ ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
      (correction : stateSmoothRange parameters reference insideR)
      (vector : ACore parameters 3) (scalar : ACore parameters 1),
      (constrainedCoreTransfer parameters reference insideR seed insideS correction).val=
        (0,toPhysicalCore parameters vector,scalar) →
      ‖stateToGrade parameters grade correction.val‖ ≤
        constant*(originalGradeNorm grade vector+originalGradeNorm grade scalar) := by
  obtain ⟨constant,nonnegative,bounded⟩ := reverseCoreTransfer_bound_on_patch parameters grade reference insideR
    seedPatch compact insidePatch
  refine ⟨constant,nonnegative,?_⟩
  intro seed seedIn insideS correction vector scalar same
  have reverse : coreTransfer parameters seed insideS reference insideR
      (constrainedCoreTransfer parameters reference insideR seed insideS correction).val=correction.val :=
    congrArg Subtype.val (constrainedCoreTransfer_reverse parameters reference insideR seed insideS correction)
  have bound := bounded seed seedIn insideS
    (constrainedCoreTransfer parameters reference insideR seed insideS correction).val
  rw [reverse,same,axb_stateToGrade_literal_norm grade (0,toPhysicalCore parameters vector,scalar)] at bound
  have zeroTangent : tangentNorm (grade+1) (0:TangentCoefficient parameters)=0 := by
    rw [← tangentToGrade_norm]
    simp only [map_zero,norm_zero]
  simpa only [map_zero,zeroTangent,zero_add,toPhysicalCore_norm] using bound

end Grad.OriginalCoreRealization
