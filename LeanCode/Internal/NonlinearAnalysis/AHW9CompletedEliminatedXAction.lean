import AHW8EliminatedKernelContinuity

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

/-- The actual eliminated x constant is chosen before
 the positive collar, physical state and input. -/
def eliminatedXConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialEliminatedXKernel_physicalMoments parameters L compact power)

theorem eliminatedXConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ eliminatedXConstant parameters L compact power :=
  (Classical.choose_spec (radialEliminatedXKernel_physicalMoments parameters L compact power)).1

def eliminatedXFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 8 1 :=
  radialEliminatedXKernel parameters L compact state (collarRadius lower positive bounded x)

theorem eliminatedXFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (eliminatedXFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (eliminatedXFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [eliminatedXFamily, Function.comp_def] using
        ((radialEliminatedXKernel_regular parameters L compact state).1 shift mode).comp
          (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem eliminatedXFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (eliminatedXFamily parameters L compact lower positive bounded state x) ≤
      eliminatedXConstant parameters L compact power * state.val.val.size power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialEliminatedXKernel_physicalMoments parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def eliminatedXAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (eliminatedXFamily parameters L compact lower positive bounded state)
    (eliminatedXFamily_measurable parameters L compact lower positive bounded state)
    (eliminatedXConstant parameters L compact power * state.val.val.size power)
    (eliminatedXFamily_moment parameters L compact lower positive bounded state power)

theorem eliminatedXAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ‖eliminatedXAction parameters L compact lower positive bounded state power field‖ ≤
      eliminatedXConstant parameters L compact power * state.val.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem eliminatedXAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (eliminatedXFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (eliminatedXAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The actual eliminated x error constant is chosen before
 the positive collar, physical state and input. -/
def eliminatedXErrorConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialEliminatedXKernel_referenceDifference parameters L compact power)

theorem eliminatedXErrorConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ eliminatedXErrorConstant parameters L compact power :=
  (Classical.choose_spec (radialEliminatedXKernel_referenceDifference parameters L compact power)).1

def eliminatedXErrorFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 8 1 :=
  fullKernelSub
    (radialEliminatedXKernel parameters L compact state (collarRadius lower positive bounded x))
    (circularEliminatedXKernel (radialKernelParameters parameters (collarRadius lower positive bounded x)) L)

theorem eliminatedXErrorFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (eliminatedXErrorFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (eliminatedXErrorFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [eliminatedXErrorFamily, Function.comp_def] using
        ((radialEliminatedXError_regular parameters L compact state).1 shift mode).comp
          (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem eliminatedXErrorFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (eliminatedXErrorFamily parameters L compact lower positive bounded state x) ≤
      eliminatedXErrorConstant parameters L compact power * state.val.errorBudget power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialEliminatedXKernel_referenceDifference parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def eliminatedXErrorAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (eliminatedXErrorFamily parameters L compact lower positive bounded state)
    (eliminatedXErrorFamily_measurable parameters L compact lower positive bounded state)
    (eliminatedXErrorConstant parameters L compact power * state.val.errorBudget power)
    (eliminatedXErrorFamily_moment parameters L compact lower positive bounded state power)

theorem eliminatedXErrorAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ‖eliminatedXErrorAction parameters L compact lower positive bounded state power field‖ ≤
      eliminatedXErrorConstant parameters L compact power * state.val.errorBudget power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem eliminatedXErrorAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (eliminatedXErrorFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (eliminatedXErrorAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside


/-- Both constants are chosen before the physical state and positive inner radius.
The error reference is the exact circular eliminated x, and the bulk carrier uses the original phase. -/
theorem eliminatedXCompleted_uniform (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    ∃ regularConstant errorConstant : ℝ, 0 ≤ regularConstant ∧ 0 ≤ errorConstant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : RetainedInverseState parameters L compact) (field : DivisionRow 8 lower),
      ‖eliminatedXAction parameters L compact lower positive bounded state power field‖ ≤
        regularConstant * (1 + state.val.errorBudget power) * ‖field‖ ∧
      ‖eliminatedXErrorAction parameters L compact lower positive bounded state power field‖ ≤
        errorConstant * state.val.errorBudget power * ‖field‖ := by
  refine ⟨eliminatedXConstant parameters L compact power, eliminatedXErrorConstant parameters L compact power,
    eliminatedXConstant_nonnegative parameters L compact power, eliminatedXErrorConstant_nonnegative parameters L compact power, ?_⟩
  intro lower positive bounded state field
  exact ⟨eliminatedXAction_bound parameters L compact lower positive bounded state power field,
    eliminatedXErrorAction_bound parameters L compact lower positive bounded state power field⟩

end Grad.AnnularKernelL2
