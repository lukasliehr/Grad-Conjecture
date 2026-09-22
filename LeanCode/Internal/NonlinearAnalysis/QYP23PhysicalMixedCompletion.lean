import Q23PhysicalInnerGenuine
import QYP14PhysicalCoreTower
import QYP8PhysicalPublicContract

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.ConstrainedGrades Grad.QuotientProjection
open Grad.Q24Realization Grad.MixedQuotientComposition

/-- Every actual completed mixed derivative agrees with the literal finite
allocation/partition tower on the core, in the original quotient completion. -/
theorem completedPhysicalMixedSlice_derivative_core
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade order : ℕ) (base : Input parameters) (admissible : CoreAdmissible base)
    (directions : Fin order → Input parameters) :
    iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
      (mixedCoreEmbed parameters (grade + 6) base)
      (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade (physicalMixedSliceCoreTower parameters cellLength reference insideR
        order base (fun position => directions position.rev)) := by
  exact physicalMixedComposedDerivative_core
    (physicalMixedInnerFamily parameters reference insideR) reference insideR
    (fun point inside _ tuple => physicalMixedInnerFamily_zero parameters reference insideR point inside tuple)
    (physicalMixedInnerFamily_genuine parameters reference insideR)
    cellLength grade order base admissible directions

/-- The actual mixed Banach derivatives obey the exact loss-six estimate,
uniform on any compact admissible seed patch and bounded low-state ball.
No openness of the compact patch or high-state bound is assumed. -/
theorem completedPhysicalMixedSlice_derivative_bound
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade order : ℕ) (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound stateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : MixedAmbient parameters (grade + 6))
        (directions : Fin order → MixedAmbient parameters (grade + 6)),
        mixedSeed parameters (grade + 6) base ∈ seedPatch →
        ‖(mixedJoint parameters (grade + 6) base).ofLp.1‖ ≤ curvatureBound →
        base ∈ mixedDomain parameters (grade + 6) →
        ‖xLowering parameters (realLowLeHigh grade) (mixedStatePart parameters (grade + 6) base)‖ ≤ stateBound →
        ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade) base directions‖ ≤
          constant * mixedCompletedOneHigh parameters grade order base directions := by
  apply physicalMixedComposedDerivative_bound_on_patch
    (physicalMixedInnerFamily parameters reference insideR) reference insideR
    (fun point inside _ tuple => physicalMixedInnerFamily_zero parameters reference insideR point inside tuple)
    (physicalMixedInnerFamily_genuine parameters reference insideR)
    seedPatch curvatureBound stateBound
  intro q count
  obtain ⟨constant, nonneg, estimate⟩ := physicalMixedInnerFamily_bound
    parameters reference insideR q count seedPatch compact insidePatch curvatureBound
  exact ⟨constant, nonneg, fun base directions inPatch curvature admissible _ =>
    estimate base directions inPatch curvature admissible.2⟩

/-- Q23 for the actual physical real constrained Q24 realization. The high
base factor contains only the state, and direction norms retain the literal
seed-coordinate ℓ¹, curvature and original constrained-state terms. -/
theorem physicalMixedDerivativeEstimate
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    PhysicalMixedDerivativeEstimate parameters cellLength reference insideR := by
  intro grade large order seedPatch compact insidePatch curvatureBound stateBound
  obtain ⟨constant, nonneg, estimate⟩ := completedPhysicalMixedSlice_derivative_bound
    parameters cellLength reference insideR grade order seedPatch compact insidePatch curvatureBound stateBound
  refine ⟨constant, nonneg, fun base directions inPatch curvature inside bounded => ?_⟩
  exact completedRealPhysicalMixedSlice_bound_of_ambient parameters cellLength reference insideR grade
    (by omega) order seedPatch curvatureBound stateBound constant estimate base directions inPatch curvature inside bounded

/-- The complete physical Q24 real compatible Banach realization, with
unconditional actual mixed Q23 estimates and the literal core residual. -/
theorem physicalMixedBanachRealization
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    PhysicalMixedBanachRealization parameters cellLength reference insideR where
  smooth grade large :=
    completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR grade (by omega)
  literal grade large base insideS axis :=
    completedRealPhysicalMixedSlice_core parameters cellLength reference insideR grade (by omega) base insideS axis
  compatible lower upper large ordered base inside :=
    completedRealPhysicalMixedSlice_gradeCompatibility parameters cellLength reference insideR
      (by omega) ordered base inside
  derivativesCompatible lower upper large ordered order base inside directions :=
    completedRealPhysicalMixedSlice_derivative_gradeCompatibility parameters cellLength reference insideR
      (by omega) ordered order base inside directions
  tame := physicalMixedDerivativeEstimate parameters cellLength reference insideR

end Grad.PhysicalCoordinates
