import AJD22SameCoupledInverseFrechetCalculus
import AJD26UniformCoordinateCalculus
import GC15BudgetAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Exactly the already used parameters and original B8 hypothesis. -/
def coupledCoordinatePredicate (parameters : PhaseParameters) (L compact : ℝ)
    (packet : ℝ × RetainedInverseState parameters L compact) : Prop :=
  0 < packet.1 ∧ packet.1 ≤ 1 / 2 ∧ 0 < L ∧ parameters.gamma ≤ 1 / 2 ∧
    parameters.gamma ≤ Real.sqrt 5 / (6 * L) ∧
    physicalBudget parameters packet.2.val.val.field packet.2.val.val.rho packet.2.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact

/-- Existing products and a subtype package the same hypotheses without
asking Lean to generate recursors for the deeply nested physical state. -/
def CoupledCoordinateContext (parameters : PhaseParameters) (L compact : ℝ) : Type :=
  {packet : ℝ × RetainedInverseState parameters L compact // coupledCoordinatePredicate parameters L compact packet}

namespace CoupledCoordinateContext
variable {parameters : PhaseParameters} {L compact : ℝ}

def lower (context : CoupledCoordinateContext parameters L compact) : ℝ := context.val.1

def state (context : CoupledCoordinateContext parameters L compact) : RetainedInverseState parameters L compact := context.val.2

theorem positive (context : CoupledCoordinateContext parameters L compact) : 0 < context.lower := context.property.1

theorem lowerHalf (context : CoupledCoordinateContext parameters L compact) : context.lower ≤ 1 / 2 := context.property.2.1

theorem lengthPositive (context : CoupledCoordinateContext parameters L compact) : 0 < L := context.property.2.2.1

theorem widthHalf (context : CoupledCoordinateContext parameters L compact) : parameters.gamma ≤ 1 / 2 := context.property.2.2.2.1

theorem widthLength (context : CoupledCoordinateContext parameters L compact) : parameters.gamma ≤ Real.sqrt 5 / (6 * L) := context.property.2.2.2.2.1

theorem small (context : CoupledCoordinateContext parameters L compact) :
    physicalBudget parameters context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact := context.property.2.2.2.2.2

def budget (context : CoupledCoordinateContext parameters L compact) (order : ℕ) : ℝ :=
  physicalBudget parameters context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon (8 + order)

theorem budget_nonnegative (context : CoupledCoordinateContext parameters L compact) (order : ℕ) :
    0 ≤ context.budget order := physicalBudget_nonnegative _ _ _ _ _

theorem budget_monotone (context : CoupledCoordinateContext parameters L compact) : Monotone context.budget :=
  fun _ _ ordered => physicalBudget_monotone _ _ _ _ (Nat.add_le_add_left ordered 8)

theorem budget_zero_le_one (context : CoupledCoordinateContext parameters L compact) : context.budget 0 ≤ 1 :=
  coupledPrimitive_budget_one parameters L compact context.state context.small

theorem budget_pair (context : CoupledCoordinateContext parameters L compact) (first second : ℕ) :
    context.budget first * context.budget second ≤ pairBudgetConstant 8 (first + second) 1 * context.budget (first + second) :=
  physical_budget_pair 8 (first + second) first second le_rfl parameters context.state.val.val.field
    context.state.val.val.rho context.state.val.val.epsilon 1 (by norm_num) context.budget_zero_le_one

theorem size_zero_le_two (context : CoupledCoordinateContext parameters L compact) :
    context.state.val.val.size 0 ≤ 2 := by
  have grade : physicalBudget parameters context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon 7 ≤ context.budget 0 :=
    physicalBudget_monotone _ _ _ _ (by norm_num)
  have small := context.budget_zero_le_one
  change 1 + physicalBudget parameters context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon 7 ≤ 2
  linarith
end CoupledCoordinateContext
end Grad.AnnularCrossOrbit
