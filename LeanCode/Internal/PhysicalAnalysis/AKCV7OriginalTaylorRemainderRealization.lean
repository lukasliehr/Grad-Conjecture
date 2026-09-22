import AKCV6OriginalParameterStateDerivativeSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds
open Grad.NashMoser.BranchDerivative

variable (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (base : RealMixedCore parameters reference insideR) (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))

/-- The actual original nonlinear Taylor remainder, with the exact finite
parameter derivative and the literal original state-forward operator. -/
def originalLiteralTaylorRemainder (point : RealMixedCore parameters reference insideR) :
    sourceSmoothRange parameters :=
  coreTaylorRemainder (originalNonlinearSource parameters cellLength reference insideR)
    (base.1, base.2.1) (point.1, point.2.1) base.2.2 point.2.2
    (originalParameterDerivative parameters reference insideR cellLength base insideS axis)
    (literalPhysicalSmoothForward parameters cellLength reference insideR base.1 insideS base.2 axis)

theorem originalLiteralTaylorRemainder_eq (point : RealMixedCore parameters reference insideR) :
    originalLiteralTaylorRemainder parameters cellLength reference insideR base insideS axis point =
      originalNonlinearSource parameters cellLength reference insideR (point.1,point.2.1) point.2.2 -
      originalNonlinearSource parameters cellLength reference insideR (base.1,base.2.1) base.2.2 -
      originalMixedDerivative parameters cellLength reference insideR base insideS axis (point-base) := by
  have split : point-base =
      originalFiniteDirection parameters reference insideR ((point.1,point.2.1)-(base.1,base.2.1)) +
      originalStateDirection parameters reference insideR (point.2.2-base.2.2) := by
    change (point.1-base.1,point.2.1-base.2.1,point.2.2-base.2.2) =
      (point.1-base.1+0,point.2.1-base.2.1+0,0+(point.2.2-base.2.2))
    simp only [add_zero,zero_add]
  rw [split,originalMixedDerivative_split]
  unfold originalLiteralTaylorRemainder coreTaylorRemainder
  abel

/-- The SAME smooth-core remainder is exactly the ordinary Banach Taylor
remainder of the accepted Q24 realization, at each original source grade.
This is the direct consumer for local one-high second-derivative bounds. -/
theorem originalLiteralTaylorRemainder_completed
    (point : RealMixedCore parameters reference insideR) (pointInside : point.1 ∈ Seed.parameterDomain)
    (pointAxis : ChartAxisCondition (smoothingChartCore parameters point.2.2.val))
    (grade : ℕ) (large : 3 ≤ grade) :
    sourceSmoothEmbedding parameters grade large
      (originalLiteralTaylorRemainder parameters cellLength reference insideR base insideS axis point) =
      completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) point) -
      completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base) -
      (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base))
        (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) point -
          realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade) base) := by
  rw [originalLiteralTaylorRemainder_eq]
  have outer := map_sub (sourceSmoothEmbedding parameters grade large)
    (originalNonlinearSource parameters cellLength reference insideR (point.1,point.2.1) point.2.2 -
      originalNonlinearSource parameters cellLength reference insideR (base.1,base.2.1) base.2.2)
    (originalMixedDerivative parameters cellLength reference insideR base insideS axis (point-base))
  have inner := map_sub (sourceSmoothEmbedding parameters grade large)
    (originalNonlinearSource parameters cellLength reference insideR (point.1,point.2.1) point.2.2)
    (originalNonlinearSource parameters cellLength reference insideR (base.1,base.2.1) base.2.2)
  rw [outer, inner,
    originalNonlinearSource_completed parameters cellLength reference insideR (point.1,point.2.1)
      point.2.2 pointInside pointAxis,
    originalNonlinearSource_completed parameters cellLength reference insideR (base.1,base.2.1)
      base.2.2 insideS axis,
    originalMixedDerivative_completed]
  have difference := (originalMixedCoreEmbedding parameters reference insideR (grade+6)
    (realHighLarge grade)).map_sub point base
  simp only [originalMixedCoreEmbedding_apply] at difference
  rw [difference]

end Grad.NashMoser.OriginalLimit
