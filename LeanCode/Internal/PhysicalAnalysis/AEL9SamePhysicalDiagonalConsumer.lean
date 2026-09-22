import AEL7OneOriginalHighLowBall
import AEL8ActualComplexSolutionAndUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentLow Grad.AnnularLowVolterra
open Grad.AnnularUniformBoundary Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryKernelAction

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  currentZero_normedGroup currentZero_seminormedGroup currentZero_realNormedSpace

/-- Exact immediate diagonal consumer: one actual physical coefficient state
and one radius-independent primitive ball provide both current inverse bounds
and literal high coercivity. The coupled inverse is a separate later result. -/
theorem samePhysicalHighLow_inverse_bounds (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤ currentAnnularPrimitiveRadius parameters L compact) :
    let retained := currentAnnularState parameters L compact state small
    let highSmall := currentAnnularState_high_small parameters L compact state small
    retained.val.val = state ∧
    (∀ field : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      (1 / 32 : ℝ) * ‖field‖ ^ 2 ≤
        (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained field.val field.val).re) ∧
    ‖currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained highSmall‖ ≤ 32 ∧
    ‖lowCurrentInverse parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) retained‖ ≤
      2 * Real.sqrt (lowReferenceGraphConstant parameters L) := by
  dsimp only
  exact ⟨rfl,
    currentHighFormValue_coercive parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength _
      (currentAnnularState_high_small parameters L compact state small),
    currentHighDualInverse_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength _
      (currentAnnularState_high_small parameters L compact state small),
    lowCurrentInverse_bound parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) _
      (currentAnnularState_low_small parameters L compact state small)⟩

end Grad.AnnularCurrentInverse
