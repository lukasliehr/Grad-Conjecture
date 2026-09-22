import AKDS19PhysicalBudgetReferenceBound
import AXN6SourceProjectionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.RealFixedRanges
open Grad.ChartAxisLift Grad.ChartAxisSourceBound Grad.ChartAxisProjections Grad.Q24Realization
open Grad.SmoothingFamily Grad.PhysicalCoordinates Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.ConstrainedGrades

theorem referenceState_norm_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (ordered : lower≤upper) (state : StateCore parameters) :
    ‖stateToGrade parameters lower state‖≤‖stateToGrade parameters upper state‖ := by
  have bound := xLowering_norm_le parameters ordered (stateToGrade parameters upper state)
  rw [xLowering_core] at bound
  exact bound

theorem referenceSource_norm_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (ordered : lower≤upper) (source : SmoothQuotient parameters) :
    ‖quotientEta parameters lower source‖≤‖quotientEta parameters upper source‖ := by
  have bound := zLowering_norm_le parameters ordered (quotientEta parameters upper source)
  rw [zLowering_core] at bound
  exact bound

/-- The actual projected source and its physical one-high low payment are
bounded by the full source. Only one fixed low state grade is bounded; the
output high state appears once, and the original analytic width is unchanged. -/
theorem actualProjectedSource_oneHigh_payment (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0<length) (radius : ℝ) (positive : 0<radius) (bounded : radius≤1)
    (high low : ℕ) (lowLarge : 4≤low) (ordered : low≤high)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound seedBound stateBound : ℝ)
    (stateNonnegative : 0≤stateBound) :
    ∃ constant : ℝ,0≤constant ∧ ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
      (base : RealJointCore parameters reference insideR), |base.1|≤curvatureBound → |seed 0|≤seedBound →
      ∀ (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
        (source : sourceSmoothRange parameters),
      ‖stateToGrade parameters (low+6) base.2.val‖≤stateBound →
      let projected := realRangeProjection radius positive bounded length reference insideR seed insideS base axis source
      ‖quotientEta parameters high projected.val‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 high)*‖quotientEta parameters low projected.val‖ ≤
      constant*(‖quotientEta parameters (high+9) source.val‖+
        (1+‖stateToGrade parameters (high+9) base.2.val‖)*‖quotientEta parameters (low+9) source.val‖) := by
  obtain ⟨highConstant,highNonnegative,highBound⟩ := realRangeProjection_bound_on_patch parameters length lengthPositive
    radius positive bounded reference insideR high (lowLarge.trans ordered) seedPatch compact insidePatch curvatureBound stateBound
  obtain ⟨lowConstant,lowNonnegative,lowBound⟩ := realRangeProjection_bound_on_patch parameters length lengthPositive
    radius positive bounded reference insideR low lowLarge seedPatch compact insidePatch curvatureBound stateBound
  obtain ⟨budgetConstant,budgetNonnegative,budgetBound⟩ := actualPhysicalBudget_reference_bound parameters high
    reference insideR seedPatch compact insidePatch curvatureBound seedBound
  let paidLow := lowConstant*(2+stateBound)
  have paidLowNonnegative : 0≤paidLow := mul_nonneg lowNonnegative (by linarith)
  refine ⟨highConstant+(1+budgetConstant)*paidLow,
    add_nonneg highNonnegative (mul_nonneg (by linarith) paidLowNonnegative),?_⟩
  intro seed seedIn insideS base curvature seedSmall axis source stateLow
  let projected := realRangeProjection radius positive bounded length reference insideR seed insideS base axis source
  have stateFour := (referenceState_norm_mono parameters (by omega : 4≤low+6) base.2.val).trans stateLow
  have projectedHigh := highBound seed seedIn insideS base curvature axis source stateFour
  have projectedLow := lowBound seed seedIn insideS base curvature axis source stateFour
  change ‖quotientEta parameters high projected.val‖ ≤ highConstant*
    (‖quotientEta parameters (high+9) source.val‖+
      (1+‖stateToGrade parameters (high+6) base.2.val‖)*‖quotientEta parameters 7 source.val‖) at projectedHigh
  change ‖quotientEta parameters low projected.val‖ ≤ lowConstant*
    (‖quotientEta parameters (low+9) source.val‖+
      (1+‖stateToGrade parameters (low+6) base.2.val‖)*‖quotientEta parameters 7 source.val‖) at projectedLow
  have sourceSeven := referenceSource_norm_mono parameters (by omega : 7≤low+9) source.val
  have stateHigh := referenceState_norm_mono parameters (by omega : high+6≤high+9) base.2.val
  have lowProduct := mul_le_mul (add_le_add_right stateLow 1) sourceSeven
    (norm_nonneg _) (by linarith : 0≤1+stateBound)
  have lowPaid : ‖quotientEta parameters low projected.val‖ ≤
      paidLow*‖quotientEta parameters (low+9) source.val‖ := by
    apply projectedLow.trans
    have bound := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl ‖quotientEta parameters (low+9) source.val‖) lowProduct) lowNonnegative
    exact bound.trans_eq (by dsimp only [paidLow]; ring)
  let payment := ‖quotientEta parameters (high+9) source.val‖+
    (1+‖stateToGrade parameters (high+9) base.2.val‖)*‖quotientEta parameters (low+9) source.val‖
  have highProduct := mul_le_mul (add_le_add_right stateHigh 1) sourceSeven
    (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg _))
  have highPaid : ‖quotientEta parameters high projected.val‖ ≤ highConstant*payment :=
    projectedHigh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl highProduct) highNonnegative)
  have budget := budgetBound seed seedIn insideS base curvature seedSmall axis
  have stateMono := referenceState_norm_mono parameters (by omega : high≤high+9) base.2.val
  have budgetHigh : 1+physicalBudget parameters
      (actualFiniteCurrentField parameters reference insideR seed insideS base) (seed 0) base.1 high ≤
      (1+budgetConstant)*(1+‖stateToGrade parameters (high+9) base.2.val‖) := by
    have mono := mul_le_mul_of_nonneg_left (add_le_add_right stateMono 1) budgetNonnegative
    nlinarith [norm_nonneg (stateToGrade parameters (high+9) base.2.val)]
  have weighted := mul_le_mul budgetHigh lowPaid (norm_nonneg _)
    (mul_nonneg (by linarith) (add_nonneg zero_le_one (norm_nonneg _)))
  have weightedPaid : (1+physicalBudget parameters
      (actualFiniteCurrentField parameters reference insideR seed insideS base) (seed 0) base.1 high)*
      ‖quotientEta parameters low projected.val‖ ≤ (1+budgetConstant)*paidLow*payment := by
    apply weighted.trans
    have paymentLarge : (1+‖stateToGrade parameters (high+9) base.2.val‖)*
        ‖quotientEta parameters (low+9) source.val‖ ≤ payment := le_add_of_nonneg_left (norm_nonneg _)
    have paid := mul_le_mul_of_nonneg_left paymentLarge
      (mul_nonneg (by linarith : 0≤1+budgetConstant) paidLowNonnegative)
    exact (by convert paid using 1; ring)
  exact (add_le_add highPaid weightedPaid).trans_eq (by ring)

end Grad.OriginalCoreRealization
