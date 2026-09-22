import AKCV13OriginalCoreLocalTaylorConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
open Set Filter
open scoped Topology ContDiff
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

/-- The actual inverse estimate alone supplies NM11's local inverse-Taylor
remainder estimate. The nonlinear Taylor bounds and local admissible segment
are derived, with one high displacement and the fixed grade-four low one.
The quantitative inverse remains an explicit application prerequisite. -/
theorem originalInverseTaylorRemainder_local
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (sourceGrade : ℕ) (sourceLarge : 4 ≤ sourceGrade)
    (outputGrade : ℕ) (outputLarge : 3 ≤ outputGrade)
    (base : RealMixedCore parameters reference insideR) (baseInside : base.1 ∈ Seed.parameterDomain)
    (baseAxis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR)
    (inverseConstant stateWeight : ℝ) (inverseNonnegative : 0 ≤ inverseConstant) (stateNonnegative : 0 ≤ stateWeight)
    (inverseBound : ∀ source,
      ‖stateSmoothEmbedding parameters reference insideR outputGrade outputLarge (inverse source)‖ ≤
      inverseConstant*(‖sourceSmoothEmbedding parameters sourceGrade (Nat.le_of_succ_le sourceLarge) source‖+
        stateWeight*‖sourceSmoothEmbedding parameters 4 realLowLarge source‖)) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∃ neighborhood : Set (RealMixedAmbient parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade)),
      neighborhood ∈ 𝓝 (realMixedCoreEmbed parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) base) ∧
      ∀ point : RealMixedCore parameters reference insideR,
      realMixedCoreEmbed parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) point ∈ neighborhood →
      ‖stateSmoothEmbedding parameters reference insideR outputGrade outputLarge
        (inverse (originalLiteralTaylorRemainder parameters cellLength reference insideR base baseInside baseAxis point))‖ ≤
      constant * (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) (point.2.2-base.2.2)‖) *
        (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (point.2.2-base.2.2)‖) := by
  obtain ⟨highConstant,highNonnegative,highSet,highNear,highBound⟩ :=
    originalLiteralTaylorRemainder_local parameters cellLength reference insideR sourceGrade sourceLarge base baseInside baseAxis
  obtain ⟨lowConstant,lowNonnegative,lowSet,lowNear,lowBound⟩ :=
    originalLiteralTaylorRemainder_local parameters cellLength reference insideR 4 (le_refl 4) base baseInside baseAxis
  let lowering := realMixedLowering parameters reference insideR (realHighLarge 4)
    (Nat.add_le_add_right sourceLarge 6)
  have lowerNear : lowering ⁻¹' lowSet ∈
      𝓝 (realMixedCoreEmbed parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) base) :=
    lowering.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [lowering,originalMixedCoreEmbed_lowering] using lowNear)
  refine ⟨inverseConstant*(highConstant+stateWeight*lowConstant),
    mul_nonneg inverseNonnegative (add_nonneg highNonnegative (mul_nonneg stateNonnegative lowNonnegative)),
    highSet ∩ lowering ⁻¹' lowSet,inter_mem highNear lowerNear,fun point pointNear => ?_⟩
  have high := highBound point pointNear.1
  have lowerPoint : realMixedCoreEmbed parameters reference insideR (4+6) (realHighLarge 4) point ∈ lowSet := by
    simpa only [mem_preimage,lowering,originalMixedCoreEmbed_lowering] using pointNear.2
  have low := lowBound point lowerPoint
  have monotone := stateLowering_norm_le parameters reference insideR (realHighLarge 4)
    (Nat.add_le_add_right sourceLarge 6)
    (stateSmoothEmbedding parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) (point.2.2-base.2.2))
  rw [stateLowering_core] at monotone
  have lowPaid : ‖sourceSmoothEmbedding parameters 4 realLowLarge
      (originalLiteralTaylorRemainder parameters cellLength reference insideR base baseInside baseAxis point)‖ ≤
      lowConstant*(‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) (point.2.2-base.2.2)‖)*
        (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (point.2.2-base.2.2)‖) :=
    low.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl monotone) lowNonnegative)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ _ := inverseBound _
    _ ≤ inverseConstant*(highConstant*(‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) (point.2.2-base.2.2)‖)*
        (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (point.2.2-base.2.2)‖)+
      stateWeight*(lowConstant*(‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade) (point.2.2-base.2.2)‖)*
        (‖(point.1,point.2.1)-(base.1,base.2.1)‖+
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge (point.2.2-base.2.2)‖))) :=
      mul_le_mul_of_nonneg_left (add_le_add high (mul_le_mul_of_nonneg_left lowPaid stateNonnegative)) inverseNonnegative
    _ = _ := by ring

end Grad.NashMoser.OriginalLimit
