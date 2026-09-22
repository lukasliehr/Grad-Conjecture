import BCI21ExactSevenSlotBoundaryEquation

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable {parameters : PhaseParameters} {L compact : ℝ}

def actualBoundaryNOnHigh (state : PhysicalBoundaryState parameters L compact) (angular cell : ℕ) :
    NegativeTrace parameters angular cell 3 →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  (fullNegativeKernelAction parameters angular cell (actualBoundaryN state)).codRestrict
    (highAngularSubmodule parameters angular cell 1)
    (highKernelAction parameters angular cell _ (actualBoundaryN_high state))

def actualBoundaryHOnHigh (state : PhysicalBoundaryState parameters L compact) (angular cell : ℕ) :
    NegativeTrace parameters angular cell 3 →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  (fullNegativeKernelAction parameters angular cell (actualBoundaryH state)).codRestrict
    (highAngularSubmodule parameters angular cell 1)
    (highKernelAction parameters angular cell _ (actualBoundaryH_high state))

def actualRetainedBoundaryTerm (state : BoundaryInverseState parameters L compact) (angular cell : ℕ) :
    NegativeTrace parameters angular cell 3 →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  -(actualBoundaryInverseOnHigh state angular cell).comp (actualBoundaryNOnHigh state.val angular cell)

def actualSourceBoundaryTerm (state : BoundaryInverseState parameters L compact) (angular cell : ℕ) :
    NegativeTrace parameters angular cell 3 →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  -(actualBoundaryInverseOnHigh state angular cell).comp (actualBoundaryHOnHigh state.val angular cell)

theorem actualRetainedBoundaryTerm_kernel (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (retained : NegativeTrace parameters angular cell 3) :
    (actualRetainedBoundaryTerm state angular cell retained).val =
      fullNegativeKernelAction parameters angular cell (actualRetainedBoundaryLiftKernel state) retained := by
  change -fullNegativeKernelAction parameters angular cell (actualHighBoundaryInverse state.val state.property)
    (fullNegativeKernelAction parameters angular cell (actualBoundaryN state.val) retained) = _
  rw [actualRetainedBoundaryLiftKernel, fullNegativeKernelAction_neg, fullNegativeKernelAction_comp]
  rfl

theorem actualSourceBoundaryTerm_kernel (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : NegativeTrace parameters angular cell 3) :
    (actualSourceBoundaryTerm state angular cell source).val =
      fullNegativeKernelAction parameters angular cell (actualSourceBoundaryLiftKernel state) source := by
  change -fullNegativeKernelAction parameters angular cell (actualHighBoundaryInverse state.val state.property)
    (fullNegativeKernelAction parameters angular cell (actualBoundaryH state.val) source) = _
  rw [actualSourceBoundaryLiftKernel, fullNegativeKernelAction_neg, fullNegativeKernelAction_comp]
  rfl

/-- AI11, in both directions, on the complete exact high negative-half
carrier with the original source tuple and the differentiated physical datum. -/
theorem actualAI11_boundary_equivalence (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (x datum : HighBoundaryPrimitive parameters angular cell)
    (retained source : NegativeTrace parameters angular cell 3) :
    actualBoundaryTOnHigh state.val angular cell x + actualBoundaryNOnHigh state.val angular cell retained +
        actualBoundaryHOnHigh state.val angular cell source = datum ↔
      x = actualRetainedBoundaryTerm state angular cell retained +
        (actualBoundaryInverseOnHigh state angular cell datum + actualSourceBoundaryTerm state angular cell source) := by
  constructor
  · intro equation
    have inverted := congrArg (actualBoundaryInverseOnHigh state angular cell) equation
    rw [map_add, map_add, actualBoundaryInverseOnHigh_left] at inverted
    have solved := eq_sub_of_add_eq (eq_sub_of_add_eq inverted)
    apply solved.trans
    change _ = -(actualBoundaryInverseOnHigh state angular cell (actualBoundaryNOnHigh state.val angular cell retained)) +
      (actualBoundaryInverseOnHigh state angular cell datum -
        actualBoundaryInverseOnHigh state angular cell (actualBoundaryHOnHigh state.val angular cell source))
    abel
  · intro equation
    rw [equation]
    change actualBoundaryTOnHigh state.val angular cell
      (-(actualBoundaryInverseOnHigh state angular cell (actualBoundaryNOnHigh state.val angular cell retained)) +
        (actualBoundaryInverseOnHigh state angular cell datum -
          actualBoundaryInverseOnHigh state angular cell (actualBoundaryHOnHigh state.val angular cell source))) +
      actualBoundaryNOnHigh state.val angular cell retained + actualBoundaryHOnHigh state.val angular cell source = datum
    rw [map_add, map_neg, map_sub, actualBoundaryInverseOnHigh_right, actualBoundaryInverseOnHigh_right,
      actualBoundaryInverseOnHigh_right]
    abel

end Grad.ActualBoundaryInverse
