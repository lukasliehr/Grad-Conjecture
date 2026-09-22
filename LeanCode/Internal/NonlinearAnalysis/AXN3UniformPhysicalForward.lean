import AXN2ReferenceLiftBound
import QYP24PhysicalMixedConsumer

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open scoped BigOperators ContDiff

namespace Grad.ChartAxisSourceBound

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.ConstrainedGrades Grad.Q24Realization Grad.NonlinearQuotientBounds
open Grad.SmoothForward Grad.PhysicalCoordinates

/-- The actual state derivative of the corrected physical residual, uniform
in a compact moving-seed patch and a bounded real curvature slot.  This is
the order-one, state-only specialization of the accepted mixed Q23 estimate;
it is not obtained from a crude operator-norm product. -/
theorem actualPhysicalSmoothForward_tame_on_patch
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain)
    (curvatureBound stateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (_insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR),
        |base.1| ≤ curvatureBound →
        ChartAxisCondition (smoothingChartCore parameters base.2.val) →
        ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base.2‖ ≤
            stateBound →
        ∀ direction : stateRange parameters reference insideR (grade + 6)
          (realHighLarge grade),
          ‖actualPhysicalSmoothForward parameters cellLength reference insideR seed
              grade large base direction‖ ≤
            constant *
              ((1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6)
                (realHighLarge grade) base.2‖) *
                  ‖stateLowering parameters reference insideR realLowLarge
                    (realLowLeHigh grade) direction‖ + ‖direction‖) := by
  obtain ⟨constant, nonnegative, estimate⟩ :=
    physicalMixedDerivativeEstimate parameters cellLength reference insideR
      grade large 1 seedPatch compact insidePatch curvatureBound stateBound
  refine ⟨constant, nonnegative, ?_⟩
  intro seed member insideS base curvature axis lowBound direction
  let point := realMixedCoreEmbed parameters reference insideR (grade + 6)
    (realHighLarge grade) (seed, base)
  have domain : point ∈ realMixedDomain parameters reference insideR
      (grade + 6) (realHighLarge grade) :=
    (realMixedDomain_core_iff parameters reference insideR (grade + 6)
      (realHighLarge grade) (seed, base)).2 ⟨insideS, axis⟩
  have low : ‖stateLowering parameters reference insideR realLowLarge
      (realLowLeHigh grade) point.ofLp.2.ofLp.2‖ ≤ stateBound := by
    change ‖stateLowering parameters reference insideR realLowLarge
      (realLowLeHigh grade)
      (stateSmoothEmbedding parameters reference insideR (grade + 6)
        (realHighLarge grade) base.2)‖ ≤ stateBound
    rw [stateLowering_core]
    exact lowBound
  have result := estimate point
    (fun _ => physicalStateDirection parameters reference insideR (grade + 6)
      (realHighLarge grade) direction) member (by
        change ‖base.1‖ ≤ curvatureBound
        simpa only [Real.norm_eq_abs] using curvature) domain low
  rw [iteratedFDeriv_one_apply, physicalStateDirection_oneHigh] at result
  rw [actualPhysicalSmoothForward_mixed parameters cellLength reference insideR
    seed insideS grade large base axis]
  exact result

end Grad.ChartAxisSourceBound
