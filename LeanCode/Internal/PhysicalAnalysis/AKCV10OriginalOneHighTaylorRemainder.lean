import AKCV9ActualMixedSecondOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
open Set
open scoped ContDiff
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds
open Grad.NashMoser.BranchDerivative

variable (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 4 ≤ grade)

/-- Uniform actual nonlinear Taylor estimate on admissible segments.
The source loss remains six and its two displacement factors have grades
high and four. Local high-state control is displayed separately. -/
theorem originalCompletedTaylorRemainder_bound
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (patchInside : seedPatch ⊆ Seed.parameterDomain) (curvatureBound lowStateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base point : RealMixedAmbient parameters reference insideR (grade+6) (realHighLarge grade))
        (highStateBound : ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1,
        realMixedSeed parameters reference insideR (grade+6) (realHighLarge grade) (base+t•(point-base)) ∈ seedPatch ∧
        ‖(base+t•(point-base)).ofLp.2.ofLp.1‖ ≤ curvatureBound ∧
        base+t•(point-base) ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade) ∧
        ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade)
          (base+t•(point-base)).ofLp.2.ofLp.2‖ ≤ lowStateBound ∧
        ‖(base+t•(point-base)).ofLp.2.ofLp.2‖ ≤ highStateBound) →
      ‖completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large) point -
        completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large) base -
        fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large)) base (point-base)‖ ≤
      constant * ((1+highStateBound) *
        ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖^2 +
        2*‖point-base‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalMixedSecond_bound parameters cellLength reference insideR
    grade large seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun base point highStateBound segment => ?_⟩
  have result := segment_taylor_remainder_bound
    (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large))
    (realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade))
    (realMixedDomain_isOpen parameters reference insideR _ _)
    (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR grade (Nat.le_of_succ_le large))
    base (point-base) (fun t ht => (segment t ht).2.2.1)
    (constant * ((1+highStateBound) *
      ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖^2 +
      2*‖point-base‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖)) ?_
  · simpa only [add_sub_cancel] using result
  intro t ht
  have bounds := segment t ht
  exact (estimate (base+t•(point-base)) (point-base) bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.1).trans
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl bounds.2.2.2.2) (sq_nonneg _)) le_rfl) nonnegative)

/-- Exact original smooth-core consumer of the nonlinear one-high Taylor
estimate. Every term is the literal original residual/derivative from CV7. -/
theorem originalLiteralTaylorRemainder_bound
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (patchInside : seedPatch ⊆ Seed.parameterDomain) (curvatureBound lowStateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base point : RealMixedCore parameters reference insideR)
        (baseInside : base.1 ∈ Seed.parameterDomain)
        (baseAxis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))
        (_pointInside : point.1 ∈ Seed.parameterDomain)
        (_pointAxis : ChartAxisCondition (smoothingChartCore parameters point.2.2.val))
        (highStateBound : ℝ),
      let x := realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base
      let y := realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) point
      (∀ t ∈ Icc (0 : ℝ) 1,
        realMixedSeed parameters reference insideR (grade+6) (realHighLarge grade) (x+t•(y-x)) ∈ seedPatch ∧
        ‖(x+t•(y-x)).ofLp.2.ofLp.1‖ ≤ curvatureBound ∧
        x+t•(y-x) ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade) ∧
        ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade)
          (x+t•(y-x)).ofLp.2.ofLp.2‖ ≤ lowStateBound ∧
        ‖(x+t•(y-x)).ofLp.2.ofLp.2‖ ≤ highStateBound) →
      ‖sourceSmoothEmbedding parameters grade (Nat.le_of_succ_le large)
        (originalLiteralTaylorRemainder parameters cellLength reference insideR base baseInside baseAxis point)‖ ≤
      constant * ((1+highStateBound) *
        ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (y-x)‖^2 +
        2*‖y-x‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (y-x)‖) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalCompletedTaylorRemainder_bound parameters cellLength reference insideR
    grade large seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun base point baseInside baseAxis pointInside pointAxis highStateBound segment => ?_⟩
  rw [originalLiteralTaylorRemainder_completed parameters cellLength reference insideR base baseInside baseAxis point pointInside pointAxis]
  exact estimate _ _ highStateBound segment

end Grad.NashMoser.OriginalLimit
