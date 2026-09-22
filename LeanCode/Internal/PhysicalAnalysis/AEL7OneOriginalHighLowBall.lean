import AEL3CoerciveDualConstruction
import AEI29OriginalPhysicalCurrentInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularLowVolterra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryKernelAction

/-- A single original physical neighborhood for BOTH actual diagonal blocks,
chosen before the radius and data. The cross-map smallness is added separately. -/
def currentAnnularPrimitiveRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (currentHighPrimitiveRadius parameters L compact) (lowCurrentNeighborhood parameters L compact)

theorem currentAnnularPrimitiveRadius_positive (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) : 0 < currentAnnularPrimitiveRadius parameters L compact :=
  lt_min (currentHighPrimitiveRadius_positive parameters L compact)
    (lowCurrentNeighborhood_pos parameters L compact lengthPositive)

def currentAnnularState (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentAnnularPrimitiveRadius parameters L compact) : RetainedInverseState parameters L compact :=
  currentHighRetainedState parameters L compact state (small.trans (min_le_left _ _))

theorem currentAnnularState_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentAnnularPrimitiveRadius parameters L compact) :
    (currentAnnularState parameters L compact state small).val.val = state := rfl

theorem currentAnnularState_high_small (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentAnnularPrimitiveRadius parameters L compact) :
    (currentAnnularState parameters L compact state small).val.errorBudget 1 ≤
      currentHighPrimitiveRadius parameters L compact :=
  small.trans (min_le_left _ _)

theorem currentAnnularState_low_small (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentAnnularPrimitiveRadius parameters L compact) :
    physicalBudget parameters (currentAnnularState parameters L compact state small).val.val.field
      (currentAnnularState parameters L compact state small).val.val.rho
      (currentAnnularState parameters L compact state small).val.val.epsilon 8 ≤
        lowCurrentNeighborhood parameters L compact :=
  small.trans (min_le_right _ _)

/-- The same physical state supplies the genuine current low inverse with
both laws on every original annulus, within the shared high/low neighborhood. -/
theorem currentAnnularState_low_inverse (parameters : PhaseParameters) (L compact lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower < 1)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentAnnularPrimitiveRadius parameters L compact) :
    let retained := currentAnnularState parameters L compact state small
    (lowCurrentInverse parameters L compact lower lengthPositive positive bounded retained).comp
      (lowCurrentDataOperator parameters L compact lower lengthPositive positive bounded retained) = ContinuousLinearMap.id ℂ _ ∧
    (lowCurrentDataOperator parameters L compact lower lengthPositive positive bounded retained).comp
      (lowCurrentInverse parameters L compact lower lengthPositive positive bounded retained) = ContinuousLinearMap.id ℂ _ ∧
    ‖lowCurrentInverse parameters L compact lower lengthPositive positive bounded retained‖ ≤
      2 * Real.sqrt (lowReferenceGraphConstant parameters L) := by
  dsimp only
  have budget := currentAnnularState_low_small parameters L compact state small
  exact ⟨lowCurrentInverse_left parameters L compact lower lengthPositive positive bounded _ budget,
    lowCurrentInverse_right parameters L compact lower lengthPositive positive bounded _ budget,
    lowCurrentInverse_bound parameters L compact lower lengthPositive positive bounded _ budget⟩

end Grad.AnnularCurrentInverse
