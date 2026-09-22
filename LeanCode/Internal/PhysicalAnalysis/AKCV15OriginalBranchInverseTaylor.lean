import AKCV14OriginalInverseTaylorConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
open Set Filter
open scoped Topology ContDiff
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

/-- Continuity of the actual mixed branch is exactly completed-state
continuity together with the original finite parameters. -/
theorem originalMixedBranch_continuousAt
    (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference insideR)
    (base : OriginalFiniteParameter)
    (continuous : ContinuousAt (fun point => stateSmoothEmbedding parameters reference insideR grade large (branch point)) base) :
    ContinuousAt (fun point => realMixedCoreEmbed parameters reference insideR grade large
      (point.1,point.2,branch point)) base := by
  change ContinuousAt (fun point : OriginalFiniteParameter =>
    WithLp.toLp 1 (WithLp.toLp 1 point.1,WithLp.toLp 1
      (point.2,stateSmoothEmbedding parameters reference insideR grade large (branch point)))) base
  fun_prop

/-- The exact original branch inverse-Taylor premise used in CV3/CT is
now a consequence of the actual tame inverse bound and completed continuity.
Neither branch differentiability nor an independent Taylor estimate appears. -/
theorem originalBranch_inverseTaylor
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (sourceGrade : ℕ) (sourceLarge : 4 ≤ sourceGrade)
    (outputGrade : ℕ) (outputLarge : 3 ≤ outputGrade)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference insideR)
    (base : OriginalFiniteParameter) (baseInside : base.1 ∈ Seed.parameterDomain)
    (baseAxis : ChartAxisCondition (smoothingChartCore parameters (branch base).val))
    (continuous : ContinuousAt (fun point => stateSmoothEmbedding parameters reference insideR
      (sourceGrade+6) (realHighLarge sourceGrade) (branch point)) base)
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR)
    (inverseConstant stateWeight : ℝ) (inverseNonnegative : 0 ≤ inverseConstant) (stateNonnegative : 0 ≤ stateWeight)
    (inverseBound : ∀ source,
      ‖stateSmoothEmbedding parameters reference insideR outputGrade outputLarge (inverse source)‖ ≤
      inverseConstant*(‖sourceSmoothEmbedding parameters sourceGrade (Nat.le_of_succ_le sourceLarge) source‖+
        stateWeight*‖sourceSmoothEmbedding parameters 4 realLowLarge source‖)) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ᶠ point in 𝓝 base,
      ‖stateSmoothEmbedding parameters reference insideR outputGrade outputLarge
        (inverse (originalLiteralTaylorRemainder parameters cellLength reference insideR
          (base.1,base.2,branch base) baseInside baseAxis (point.1,point.2,branch point)))‖ ≤
      constant * (‖point-base‖+
        ‖stateSmoothEmbedding parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) (branch point-branch base)‖) *
        (‖point-base‖+
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (branch point-branch base)‖) := by
  obtain ⟨constant,nonnegative,neighborhood,near,estimate⟩ := originalInverseTaylorRemainder_local
    parameters cellLength reference insideR sourceGrade sourceLarge outputGrade outputLarge
    (base.1,base.2,branch base) baseInside baseAxis inverse inverseConstant stateWeight inverseNonnegative stateNonnegative inverseBound
  refine ⟨constant,nonnegative,?_⟩
  filter_upwards [(originalMixedBranch_continuousAt parameters reference insideR (sourceGrade+6)
    (realHighLarge sourceGrade) branch base continuous).eventually near] with point pointNear
  exact estimate (point.1,point.2,branch point) pointNear

end Grad.NashMoser.OriginalLimit
