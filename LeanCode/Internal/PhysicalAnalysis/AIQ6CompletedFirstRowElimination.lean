import AIQ5SameGraphPhysicalBoundaryConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularKernelContinuity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ)

/-- Actual completed Q(xi_r−Jz−Ss−f), in the unchanged normalized eight-input order. -/
def eliminationRightHandAction : DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (radialEliminationRightHandKernel parameters L compact state)
    (radialEliminationRightHandKernel_regular parameters L compact state)

theorem eliminatedXAction_eq_regular :
    eliminatedXAction parameters L compact lower positive bounded state power =
      regularRadialBulkAction parameters power lower positive bounded
        (radialEliminatedXKernel parameters L compact state)
        (radialEliminatedXKernel_regular parameters L compact state) := by
  unfold eliminatedXAction eliminatedXFamily
  symm
  apply regularRadialBulkAction_eq_completed

theorem eliminatedXAction_eq_inverse :
    eliminatedXAction parameters L compact lower positive bounded state power =
      (retainedInverseAction parameters L compact lower positive bounded state power).comp
        (eliminationRightHandAction parameters L compact lower positive bounded state power) := by
  rw [eliminatedXAction_eq_regular, retainedInverseAction_eq_regular]
  exact regularRadialBulkAction_comp parameters power lower positive bounded _ _ _ _

/-- The SAME completed x action solves the actual first row on arbitrary complete normalized inputs. -/
theorem eliminatedXAction_solves :
    (retainedAAction parameters power lower positive bounded L compact state).comp
      (eliminatedXAction parameters L compact lower positive bounded state power) =
      eliminationRightHandAction parameters L compact lower positive bounded state power := by
  rw [eliminatedXAction_eq_regular, retainedAAction, ← regularRadialBulkAction_comp]
  apply regularRadialBulkAction_congr
  exact radialEliminatedXKernel_solves parameters L compact state

theorem eliminationRightHandAction_high (input : DivisionRow 8 lower) (mode : ℤ × ℤ) (low : |mode.1| < 3) :
    eliminationRightHandAction parameters L compact lower positive bounded state power input mode = 0 := by
  unfold eliminationRightHandAction regularRadialBulkAction
  apply completedBulkKernel_high
  · intro radius
    exact radialEliminationRightHandKernel_high_left parameters L compact state _
  · exact low

/-- An independently supplied high physical x satisfies the first row exactly when it equals the actual elimination. -/
theorem completedFirstRow_iff_eliminated (field : DivisionRow 1 lower) (input : DivisionRow 8 lower)
    (high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → field mode = 0) :
    retainedAAction parameters power lower positive bounded L compact state field =
      eliminationRightHandAction parameters L compact lower positive bounded state power input ↔
      field = eliminatedXAction parameters L compact lower positive bounded state power input := by
  rw [retainedCompletedEquation_iff parameters power lower positive bounded L compact state field _ high
    (eliminationRightHandAction_high parameters L compact lower positive bounded state power input),
    eliminatedXAction_eq_inverse, ContinuousLinearMap.comp_apply]

end Grad.AnnularPhysicalSolution
