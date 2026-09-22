import QY17MixedOuterCoreBound
import QY11MixedBoundCompletion

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.ConstrainedGrades Grad.SmoothingFamily

variable {parameters : PhaseParameters}

/-- Complete the exact mixed one-high bound of a genuine inner family.
The core estimate may depend on a compact seed patch and finite curvature
bound; those finite coordinates never move in the completion argument. -/
theorem mixedComposedDerivative_bound_on_patch
    (family : (order : ℕ) → Input parameters →
      (Fin order → Input parameters) → QuotientState parameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (zeroth : ∀ (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain),
      ChartAxisCondition base.2.2 → ∀ directions,
        family 0 base directions = referenceState parameters reference insideR base.1 insideS base.2)
    (genuine : ∀ order base (directions : Fin (order + 1) → Input parameters),
      CoreAdmissible base → IsStateDirectionalDerivative
        (fun point => family order point (fun position => directions position.castSucc))
        base (directions (Fin.last order)) (family (order + 1) base directions))
    (seedPatch : Set Seed.Parameters) (curvatureBound stateBound : ℝ)
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound → CoreAdmissible base →
        baseNorm 4 base ≤ stateBound + 1 →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple)
    (cellLength : ℝ) (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : MixedAmbient parameters (grade + 6))
        (directions : Fin order → MixedAmbient parameters (grade + 6)),
        mixedSeed parameters (grade + 6) base ∈ seedPatch →
        ‖(mixedJoint parameters (grade + 6) base).ofLp.1‖ ≤ curvatureBound →
        base ∈ mixedDomain parameters (grade + 6) →
        ‖xLowering parameters (realLowLeHigh grade) (mixedStatePart parameters (grade + 6) base)‖ ≤ stateBound →
        ‖iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade) base directions‖ ≤
          constant * mixedCompletedOneHigh parameters grade order base directions := by
  let Admissible : Input parameters → Prop := fun base =>
    base.1 ∈ seedPatch ∧ ‖base.2.1‖ ≤ curvatureBound ∧ CoreAdmissible base ∧
      baseNorm 4 base ≤ stateBound + 1
  have coreAdmissible : ∀ base, Admissible base → CoreAdmissible base := fun _ member => member.2.2.1
  have inner : ∀ (q count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters), Admissible base →
        stateNorm q (family count base tuple) ≤ constant * inputOneHigh q 4 base tuple := by
    intro q count
    obtain ⟨constant, nonneg, bound⟩ := innerBound q count
    exact ⟨constant, nonneg, fun base tuple member =>
      bound base tuple member.1 member.2.1 member.2.2.1 member.2.2.2⟩
  obtain ⟨constant, nonneg, bound⟩ := mixedComposedDerivative_core_bound
    family reference insideR zeroth genuine Admissible coreAdmissible inner cellLength grade order (stateBound + 1)
  refine ⟨constant, nonneg, fun base directions inPatch curvature inside bounded => ?_⟩
  apply completedMixedSlice_bound_of_core parameters cellLength reference grade order
    seedPatch curvatureBound stateBound constant _ base directions inPatch curvature inside bounded
  intro point tuple inPatch curvature inside bounded
  exact bound point tuple
    ⟨inPatch, curvature, (CoreAdmissible_iff_domain (grade + 6) point).2 inside, bounded⟩ bounded

end Grad.MixedQuotientComposition
