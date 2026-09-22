import AHX8ActualCompletedRetainedInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)

theorem highBulkProjection_fixed {dimension : ℕ} (field : DivisionRow dimension lower)
    (high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → field mode = 0) :
    highBulkProjection parameters power lower positive bounded dimension field = field := by
  apply Subtype.ext
  funext mode
  apply Lp.ext
  filter_upwards [highBulkProjection_ae parameters power lower positive bounded field,
    Lp.coeFn_zero (ComplexEuclidean dimension) 2 (volume.restrict (Icc lower 1))] with x actual zeroValue
  rw [actual mode]
  by_cases highMode : 3 ≤ |mode.1|
  · simp only [highAngularMultiplier, if_pos highMode, one_smul]
  · rw [high mode (lt_of_not_ge highMode), zeroValue]
    simp only [Pi.zero_apply, smul_zero]

/-- Both original completed inverse identities give the exact unique retained
first-row solution on the literal high Fourier subspace. -/
theorem retainedCompletedEquation_iff (L compact : ℝ) (state : RetainedInverseState parameters L compact)
    (field data : DivisionRow 1 lower)
    (fieldHigh : ∀ mode : ℤ × ℤ, |mode.1| < 3 → field mode = 0)
    (dataHigh : ∀ mode : ℤ × ℤ, |mode.1| < 3 → data mode = 0) :
    retainedAAction parameters power lower positive bounded L compact state field = data ↔
      field = retainedInverseAction parameters L compact lower positive bounded state power data := by
  have left := congrArg (fun action : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower => action field)
    (retainedCompletedInverse_left parameters power lower positive bounded L compact state)
  have right := congrArg (fun action : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower => action data)
    (retainedCompletedInverse_right parameters power lower positive bounded L compact state)
  simp only [ContinuousLinearMap.comp_apply] at left right
  rw [highBulkProjection_fixed parameters power lower positive bounded field fieldHigh] at left
  rw [highBulkProjection_fixed parameters power lower positive bounded data dataHigh] at right
  constructor
  · intro equation
    rw [equation] at left
    exact left.symm
  · intro equation
    rw [equation]
    exact right

/-- Immediate original L2 consumer: the SAME accepted AHV inverse action
solves actual retained A, preserves high support, and retains its previously
proved radius-independent bound. -/
theorem actualRetainedL2Inverse_consumer (L compact : ℝ) (state : RetainedInverseState parameters L compact)
    (data : DivisionRow 1 lower) (dataHigh : ∀ mode : ℤ × ℤ, |mode.1| < 3 → data mode = 0) :
    retainedAAction parameters power lower positive bounded L compact state
      (retainedInverseAction parameters L compact lower positive bounded state power data) = data ∧
    (∀ mode : ℤ × ℤ, |mode.1| < 3 →
      retainedInverseAction parameters L compact lower positive bounded state power data mode = 0) ∧
    ‖retainedInverseAction parameters L compact lower positive bounded state power data‖ ≤
      retainedInverseConstant parameters L compact power * (1 + state.val.errorBudget power) * ‖data‖ := by
  have high := retainedInverseAction_high parameters power lower positive bounded L compact state data
  refine ⟨?_, high, retainedInverseAction_bound parameters L compact lower positive bounded state power data⟩
  exact (retainedCompletedEquation_iff parameters power lower positive bounded L compact state
    _ data high dataHigh).mpr rfl

end Grad.AnnularKernelL2
