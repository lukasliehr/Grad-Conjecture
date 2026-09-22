import AKCV12OriginalMixedDifferenceNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
open Set Filter
open scoped Topology ContDiff
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

/-- Local Taylor estimate for the literal original residual in the exact
parameter norm and original state grades used by the Newton argument.
The low direction always uses grade four, regardless of the output grade;
all segment and admissibility control is actually derived. -/
theorem originalLiteralTaylorRemainder_local
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 4 ≤ grade)
    (base : RealMixedCore parameters reference insideR) (baseInside : base.1 ∈ Seed.parameterDomain)
    (baseAxis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val)) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∃ neighborhood : Set (RealMixedAmbient parameters reference insideR (grade+6) (realHighLarge grade)),
      neighborhood ∈ 𝓝 (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base) ∧
      ∀ point : RealMixedCore parameters reference insideR,
      realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) point ∈ neighborhood →
      ‖sourceSmoothEmbedding parameters grade (Nat.le_of_succ_le large)
        (originalLiteralTaylorRemainder parameters cellLength reference insideR base baseInside baseAxis point)‖ ≤
      constant * (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR (grade+6) (realHighLarge grade) (point.2.2-base.2.2)‖) *
        (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (point.2.2-base.2.2)‖) := by
  let x := realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base
  have inside : x ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade) :=
    (realMixedDomain_core_iff parameters reference insideR _ _ base).2 ⟨baseInside,baseAxis⟩
  obtain ⟨constant,nonnegative,bound⟩ := originalCompletedTaylorRemainder_local
    parameters cellLength reference insideR grade large x inside
  let highFactor := ‖originalFiniteDirectionCompleted parameters reference insideR (grade+6) (realHighLarge grade)‖+1
  let lowFactor := ‖originalFiniteDirectionCompleted parameters reference insideR 4 realLowLarge‖+1
  have highNonnegative : 0 ≤ highFactor := add_nonneg
    (norm_nonneg (originalFiniteDirectionCompleted parameters reference insideR (grade+6) (realHighLarge grade))) zero_le_one
  have lowNonnegative : 0 ≤ lowFactor := add_nonneg
    (norm_nonneg (originalFiniteDirectionCompleted parameters reference insideR 4 realLowLarge)) zero_le_one
  let neighborhood := {point | ‖completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large) point -
      completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large) x -
      fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (Nat.le_of_succ_le large)) x (point-x)‖ ≤
      constant*‖point-x‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (point-x)‖ ∧
      point ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade)}
  have near : neighborhood ∈ 𝓝 x :=
    inter_mem bound ((realMixedDomain_isOpen parameters reference insideR _ _).mem_nhds inside)
  refine ⟨constant*highFactor*lowFactor,mul_nonneg (mul_nonneg nonnegative highNonnegative) lowNonnegative,
    neighborhood,near,fun point pointNear => ?_⟩
  have pointAdmissible := (realMixedDomain_core_iff parameters reference insideR _ _ point).1 pointNear.2
  rw [originalLiteralTaylorRemainder_completed parameters cellLength reference insideR base baseInside baseAxis
    point pointAdmissible.1 pointAdmissible.2]
  rw [originalMixedCoreEmbed_difference parameters reference insideR (grade+6) (realHighLarge grade) base point]
  have result := pointNear.1
  rw [originalMixedCoreEmbed_difference parameters reference insideR (grade+6) (realHighLarge grade) base point,
    originalMixedCoreEmbed_lowering] at result
  have high := originalMixedCoreEmbed_norm_bound parameters reference insideR (grade+6) (realHighLarge grade) (point-base)
  have low := originalMixedCoreEmbed_norm_bound parameters reference insideR 4 realLowLarge (point-base)
  change ‖realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) (point-base)‖ ≤
    highFactor*(‖(point.1,point.2.1)-(base.1,base.2.1)‖+
      ‖stateSmoothEmbedding parameters reference insideR (grade+6) (realHighLarge grade) (point.2.2-base.2.2)‖) at high
  change ‖realMixedCoreEmbed parameters reference insideR 4 realLowLarge (point-base)‖ ≤
    lowFactor*(‖(point.1,point.2.1)-(base.1,base.2.1)‖+
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (point.2.2-base.2.2)‖) at low
  have product := mul_le_mul high low (norm_nonneg _) (mul_nonneg highNonnegative (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have paid := mul_le_mul_of_nonneg_left product nonnegative
  calc
    _ ≤ _ := result
    _ = constant*(‖realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) (point-base)‖*
      ‖realMixedCoreEmbed parameters reference insideR 4 realLowLarge (point-base)‖) := by ring
    _ ≤ _ := paid
    _ = _ := by ring

end Grad.NashMoser.OriginalLimit
