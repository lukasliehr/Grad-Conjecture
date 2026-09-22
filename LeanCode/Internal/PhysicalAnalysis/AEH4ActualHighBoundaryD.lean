import AEH3ActualOuterRetainedTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularVariational Grad.AnnularUniformBoundary
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

def retainedBoundaryLiftMomentConstant
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) : ℝ :=
  Classical.choose
    (actualRetainedBoundaryLiftKernel_vanishingMoments parameters L compact moment)

theorem retainedBoundaryLiftMomentConstant_nonnegative
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    0 ≤ retainedBoundaryLiftMomentConstant parameters L compact moment :=
  (Classical.choose_spec
    (actualRetainedBoundaryLiftKernel_vanishingMoments parameters L compact moment)).1

theorem retainedBoundaryLiftMomentConstant_bound
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ)
    (state : BoundaryInverseState parameters L compact) :
    fullKernelMoment parameters moment (actualRetainedBoundaryLiftKernel state) ≤
      retainedBoundaryLiftMomentConstant parameters L compact moment *
        state.val.budget moment :=
  (Classical.choose_spec
    (actualRetainedBoundaryLiftKernel_vanishingMoments parameters L compact moment)).2 state

section Operator

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (angular cell : ℕ) (state : BoundaryInverseState parameters L compact)

/-- The actual current high boundary operator on literal `b_m⁻¹` energy:
`-T⁻¹ N` applied to the original retained tuple of the SAME outer trace. -/
def actualCurrentHighBoundaryD :
    annularEnergySpace lower L positive →L[ℂ]
      HighBoundaryPrimitive parameters angular cell :=
  (actualRetainedBoundaryTerm state angular cell).comp
    ((originalRetainedBoundaryLinear parameters L lengthPositive angular cell).comp
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell))

@[simp] theorem actualCurrentHighBoundaryD_apply
    (field : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field =
    actualRetainedBoundaryTerm state angular cell
      (originalRetainedBoundaryVector parameters L angular cell
        (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
          lengthPositive angular cell field)) := rfl

/-- Kernel-coordinate identity for the exact BCI22 operator. -/
theorem actualCurrentHighBoundaryD_kernel
    (field : annularEnergySpace lower L positive) :
    (actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field).val =
    fullNegativeKernelAction parameters angular cell
      (actualRetainedBoundaryLiftKernel state)
      (originalRetainedBoundaryVector parameters L angular cell
        (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
          lengthPositive angular cell field)) := by
  rw [actualCurrentHighBoundaryD_apply,
    actualRetainedBoundaryTerm_kernel]

def actualCurrentHighBoundaryDConstant : ℝ :=
  retainedBoundaryLiftMomentConstant parameters L compact (angular + cell + 1) *
    originalRetainedBoundaryConstant parameters angular cell *
      uniformOuterTraceConstant L

theorem actualCurrentHighBoundaryDConstant_nonnegative :
    0 ≤ actualCurrentHighBoundaryDConstant parameters L compact angular cell :=
  mul_nonneg
    (mul_nonneg
      (retainedBoundaryLiftMomentConstant_nonnegative parameters L compact _)
      (originalRetainedBoundaryConstant_nonnegative parameters angular cell))
    (uniformOuterTraceConstant_nonnegative L)

/-- At split tangential grade `(angular,cell)`, the physical boundary term
costs exactly `B_(angular+cell+8)` and is uniform in the inner radius. -/
theorem actualCurrentHighBoundaryD_bound
    (field : annularEnergySpace lower L positive) :
    ‖actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field‖ ≤
    actualCurrentHighBoundaryDConstant parameters L compact angular cell *
      state.val.budget (angular + cell + 1) * ‖field‖ := by
  let xi := actualCurrentHighOuterTrace parameters lower L positive lowerHalf
    lengthPositive angular cell field
  let retained := originalRetainedBoundaryVector parameters L angular cell xi
  have kernelIdentity := actualCurrentHighBoundaryD_kernel parameters L compact lower
    positive lowerHalf lengthPositive angular cell state field
  have action := fullNegativeKernelAction_bound parameters angular cell
    (actualRetainedBoundaryLiftKernel state) retained
  have moment := retainedBoundaryLiftMomentConstant_bound parameters L compact
    (angular + cell + 1) state
  have retainedBound := originalRetainedBoundaryLinear_bound parameters L lengthPositive
    angular cell xi
  have traceBound := actualCurrentHighOuterTrace_bound parameters lower L positive
    lowerHalf lengthPositive angular cell field
  change ‖(actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
    lengthPositive angular cell state field).val‖ ≤ _
  rw [kernelIdentity]
  calc
    ‖fullNegativeKernelAction parameters angular cell
        (actualRetainedBoundaryLiftKernel state) retained‖ ≤
      fullKernelMoment parameters (angular + cell + 1)
        (actualRetainedBoundaryLiftKernel state) * ‖retained‖ := action
    _ ≤ (retainedBoundaryLiftMomentConstant parameters L compact
          (angular + cell + 1) * state.val.budget (angular + cell + 1)) *
        (originalRetainedBoundaryConstant parameters angular cell * ‖xi‖) := by
      exact mul_le_mul moment retainedBound (norm_nonneg retained)
        (mul_nonneg
          (retainedBoundaryLiftMomentConstant_nonnegative parameters L compact _)
          (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho
            state.val.val.epsilon _))
    _ ≤ (retainedBoundaryLiftMomentConstant parameters L compact
          (angular + cell + 1) * state.val.budget (angular + cell + 1)) *
        (originalRetainedBoundaryConstant parameters angular cell *
          (uniformOuterTraceConstant L * ‖field‖)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg
          (retainedBoundaryLiftMomentConstant_nonnegative parameters L compact _)
          (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho
            state.val.val.epsilon _))
      exact mul_le_mul_of_nonneg_left traceBound
        (originalRetainedBoundaryConstant_nonnegative parameters angular cell)
    _ = actualCurrentHighBoundaryDConstant parameters L compact angular cell *
        state.val.budget (angular + cell + 1) * ‖field‖ := by
      unfold actualCurrentHighBoundaryDConstant
      ring

/-- BF11's base-grade estimate with the literal physical `B_8`. -/
theorem actualCurrentHighBoundaryD_B8
    (field : annularEnergySpace lower L positive) :
    ‖actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state field‖ ≤
    actualCurrentHighBoundaryDConstant parameters L compact 0 0 *
      physicalBudget parameters state.val.val.field state.val.val.rho
        state.val.val.epsilon 8 * ‖field‖ := by
  simpa only [zero_add, zero_add, Nat.reduceAdd] using
    actualCurrentHighBoundaryD_bound parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state field

end Operator

end Grad.AnnularCurrentBoundary
