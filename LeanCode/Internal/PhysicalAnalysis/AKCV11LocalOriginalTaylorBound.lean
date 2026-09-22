import AKCV10OriginalOneHighTaylorRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
open Set Filter
open scoped Topology ContDiff
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

private theorem segment_mem_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (base : E) (neighborhood : Set E) (near : neighborhood ∈ 𝓝 base) :
    ∀ᶠ point in 𝓝 base, ∀ t ∈ Icc (0 : ℝ) 1, base+t•(point-base) ∈ neighborhood := by
  obtain ⟨radius,positive,included⟩ := Metric.mem_nhds_iff.mp near
  filter_upwards [Metric.ball_mem_nhds base positive] with point pointNear
  intro t inside
  apply included
  rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg inside.1]
  have close : ‖point-base‖ < radius := by simpa only [Metric.mem_ball,dist_eq_norm] using pointNear
  have bound : t*‖point-base‖ ≤ ‖point-base‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right inside.2 (norm_nonneg (point-base))
  exact bound.trans_lt close

/-- The actual nonlinear two-scale Taylor bound holds locally at EVERY
admissible original completed point. Compact seed control, the segment's
admissibility and its low/high state bounds are derived from continuity.
No separate Taylor or segment-control premise remains. -/
theorem originalCompletedTaylorRemainder_local
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 4 ≤ grade)
    (base : RealMixedAmbient parameters reference insideR (grade+6) (realHighLarge grade))
    (inside : base ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade)) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ᶠ point in 𝓝 base,
      ‖completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large) point -
        completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large) base -
        fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large))
          base (point-base)‖ ≤
      constant * ‖point-base‖ *
        ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖ := by
  let seed := realMixedSeed parameters reference insideR (grade+6) (realHighLarge grade)
  let lowMap := stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade)
  have seedInside : seed base ∈ Seed.parameterDomain := inside.1
  obtain ⟨radius,positive,patchInside⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Seed.parameterDomain_isOpen.mem_nhds seedInside)
  let patch := Metric.closedBall (seed base) radius
  have compact : IsCompact patch := isCompact_closedBall _ _
  let curvatureBound := ‖base.ofLp.2.ofLp.1‖+1
  let lowBound := ‖lowMap base.ofLp.2.ofLp.2‖+1
  let highBound := ‖base.ofLp.2.ofLp.2‖+1
  have seedNear : ∀ᶠ point in 𝓝 base, seed point ∈ patch :=
    seed.continuous.continuousAt.eventually (Metric.closedBall_mem_nhds (seed base) positive)
  have curvatureContinuous : Continuous (fun point : RealMixedAmbient parameters reference insideR
      (grade+6) (realHighLarge grade) => ‖point.ofLp.2.ofLp.1‖) := by fun_prop
  have lowContinuous : Continuous (fun point : RealMixedAmbient parameters reference insideR
      (grade+6) (realHighLarge grade) => ‖lowMap point.ofLp.2.ofLp.2‖) := by fun_prop
  have highContinuous : Continuous (fun point : RealMixedAmbient parameters reference insideR
      (grade+6) (realHighLarge grade) => ‖point.ofLp.2.ofLp.2‖) := by fun_prop
  have curvatureNear : ∀ᶠ point in 𝓝 base, ‖point.ofLp.2.ofLp.1‖ < curvatureBound :=
    curvatureContinuous.continuousAt.eventually (Iio_mem_nhds (lt_add_one ‖base.ofLp.2.ofLp.1‖))
  have lowNear : ∀ᶠ point in 𝓝 base, ‖lowMap point.ofLp.2.ofLp.2‖ < lowBound :=
    lowContinuous.continuousAt.eventually (Iio_mem_nhds (lt_add_one ‖lowMap base.ofLp.2.ofLp.2‖))
  have highNear : ∀ᶠ point in 𝓝 base, ‖point.ofLp.2.ofLp.2‖ < highBound :=
    highContinuous.continuousAt.eventually (Iio_mem_nhds (lt_add_one ‖base.ofLp.2.ofLp.2‖))
  let neighborhood := {point | seed point ∈ patch ∧ ‖point.ofLp.2.ofLp.1‖ ≤ curvatureBound ∧
    point ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade) ∧
    ‖lowMap point.ofLp.2.ofLp.2‖ ≤ lowBound ∧ ‖point.ofLp.2.ofLp.2‖ ≤ highBound}
  have common : neighborhood ∈ 𝓝 base := by
    filter_upwards [seedNear,curvatureNear,lowNear,highNear,
      (realMixedDomain_isOpen parameters reference insideR _ _).mem_nhds inside]
      with point seedMem curvature low high admissible
    exact ⟨seedMem,curvature.le,admissible,low.le,high.le⟩
  obtain ⟨constant,nonnegative,estimate⟩ := originalCompletedTaylorRemainder_bound
    parameters cellLength reference insideR grade large patch compact patchInside curvatureBound lowBound
  have highNonnegative : 0 ≤ highBound := add_nonneg (norm_nonneg _) zero_le_one
  refine ⟨constant*(highBound+3),mul_nonneg nonnegative (add_nonneg highNonnegative (by norm_num)),?_⟩
  filter_upwards [segment_mem_eventually base neighborhood common] with point segment
  have result := estimate base point highBound segment
  have lowLeHigh := realMixedLowering_norm_le parameters reference insideR realLowLarge
    (realLowLeHigh grade) (point-base)
  have square : ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖^2 ≤
      ‖point-base‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right lowLeHigh (norm_nonneg
      (realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)))]
  calc
    _ ≤ _ := result
    _ ≤ constant*((1+highBound)*(‖point-base‖*
        ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖)+
        2*‖point-base‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-base)‖) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left square (add_nonneg zero_le_one highNonnegative)) le_rfl) nonnegative
    _ = _ := by ring

end Grad.NashMoser.OriginalLimit
