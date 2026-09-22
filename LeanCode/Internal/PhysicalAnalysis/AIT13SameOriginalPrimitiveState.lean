import AIT12OriginalHighCrossWeakEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.AnnularCurrentInverse Grad.GaugeCoefficients.Physical.Allocation

/-- The one coupled B8 ball constructs all actual retained inverses from the
unchanged primitive coefficient state. -/
def coupledRetainedState (parameters : PhaseParameters) (length compact : ℝ)
    (state : BoundaryReconstructionState parameters length compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact) :
    RetainedInverseState parameters length compact :=
  currentAnnularState parameters length compact state (small.trans (min_le_left _ _))

theorem coupledRetainedState_same (parameters : PhaseParameters) (length compact : ℝ)
    (state : BoundaryReconstructionState parameters length compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact) :
    (coupledRetainedState parameters length compact state small).val.val = state := rfl

theorem coupledRetainedState_small (parameters : PhaseParameters) (length compact : ℝ)
    (state : BoundaryReconstructionState parameters length compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact) :
    physicalBudget parameters (coupledRetainedState parameters length compact state small).val.val.field
      (coupledRetainedState parameters length compact state small).val.val.rho
      (coupledRetainedState parameters length compact state small).val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact := small

end Grad.AnnularCoupledInverse
