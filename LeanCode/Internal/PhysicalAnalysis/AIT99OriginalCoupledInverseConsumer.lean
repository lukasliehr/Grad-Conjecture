import AIT13SameOriginalPrimitiveState

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Allocation

/-- One original primitive B8 neighborhood, selected before every collar,
with the SAME physical state and the actual two-sided coupled residual inverse. -/
theorem originalCoupledInverse_oneBall (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    0 < coupledPrimitiveRadius parameters length compact ∧
    ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
      (state : BoundaryReconstructionState parameters length compact)
      (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact),
      let retained := coupledRetainedState parameters length compact state small
      let retainedSmall := coupledRetainedState_small parameters length compact state small
      let inverse := actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength retained retainedSmall
      let operator := coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength retained retainedSmall
      retained.val.val = state ∧ ‖operator‖ ≤ 1 / 2 ∧ ‖inverse‖ ≤ 2 ∧
        inverse.comp (1 - operator) = 1 ∧ (1 - operator).comp inverse = 1 ∧
        HasSum (fun degree : ℕ => operator ^ degree) inverse := by
  refine ⟨coupledPrimitiveRadius_positive parameters length compact lengthPositive, ?_⟩
  intro lower positive lowerHalf state small
  dsimp only
  exact ⟨coupledRetainedState_same parameters length compact state small,
    coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength _ _,
    actualCoupledInverse_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength _ _,
    actualCoupledInverse_left parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength _ _,
    actualCoupledInverse_right parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength _ _,
    actualCoupledInverse_hasSum parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength _ _⟩

/-- Immediate completion consumer for an arbitrary actual diagonal response.
The known-source construction is supplied by AIU, while this factor contributes
exactly the uniform factor two and arbitrary-Xalpha fixed-point uniqueness. -/
theorem originalCoupledInverse_solution (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (known : CoupledSpace lower length positive lengthPositive) :
    let inverse := actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small
    let operator := coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small
    ‖inverse known‖ ≤ 2 * ‖known‖ ∧ inverse known = known + operator (inverse known) ∧
      ∀ candidate, candidate = known + operator candidate → candidate = inverse known := by
  dsimp only
  exact ⟨actualCoupledInverse_apply_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known,
    actualCoupledInverse_fixedPoint parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known,
    actualCoupledInverse_unique parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known⟩

end Grad.AnnularCoupledInverse
