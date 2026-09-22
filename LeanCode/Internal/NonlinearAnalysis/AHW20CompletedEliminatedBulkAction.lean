import AHW19EliminatedBulkReferenceAndContinuity

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

/-- The actual eliminated (x,c,rV) constant is chosen before
 the positive collar, physical state and input. -/
def eliminatedBulkConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialEliminatedBulkKernel_physicalMoments parameters L compact power)

theorem eliminatedBulkConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ eliminatedBulkConstant parameters L compact power :=
  (Classical.choose_spec (radialEliminatedBulkKernel_physicalMoments parameters L compact power)).1

def eliminatedBulkFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 8 3 :=
  radialEliminatedBulkKernel parameters L compact state (collarRadius lower positive bounded x)

theorem eliminatedBulkFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (eliminatedBulkFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (eliminatedBulkFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [eliminatedBulkFamily, Function.comp_def] using
        ((radialEliminatedBulkKernel_regular parameters L compact state).1 shift mode).comp
          (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem eliminatedBulkFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (eliminatedBulkFamily parameters L compact lower positive bounded state x) ≤
      eliminatedBulkConstant parameters L compact power * state.val.val.size power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialEliminatedBulkKernel_physicalMoments parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def eliminatedBulkAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (eliminatedBulkFamily parameters L compact lower positive bounded state)
    (eliminatedBulkFamily_measurable parameters L compact lower positive bounded state)
    (eliminatedBulkConstant parameters L compact power * state.val.val.size power)
    (eliminatedBulkFamily_moment parameters L compact lower positive bounded state power)

theorem eliminatedBulkAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ‖eliminatedBulkAction parameters L compact lower positive bounded state power field‖ ≤
      eliminatedBulkConstant parameters L compact power * state.val.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem eliminatedBulkAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (eliminatedBulkFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (eliminatedBulkAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The actual eliminated (x,c,rV) error constant is chosen before
 the positive collar, physical state and input. -/
def eliminatedBulkErrorConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialEliminatedBulkKernel_referenceDifference parameters L compact power)

theorem eliminatedBulkErrorConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ eliminatedBulkErrorConstant parameters L compact power :=
  (Classical.choose_spec (radialEliminatedBulkKernel_referenceDifference parameters L compact power)).1

def eliminatedBulkErrorFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 8 3 :=
  fullKernelSub
    (radialEliminatedBulkKernel parameters L compact state (collarRadius lower positive bounded x))
    (circularEliminatedBulkKernel (radialKernelParameters parameters (collarRadius lower positive bounded x)) L)

theorem eliminatedBulkErrorFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (eliminatedBulkErrorFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (eliminatedBulkErrorFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [eliminatedBulkErrorFamily, Function.comp_def] using
        ((radialEliminatedBulkError_regular parameters L compact state).1 shift mode).comp
          (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem eliminatedBulkErrorFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (eliminatedBulkErrorFamily parameters L compact lower positive bounded state x) ≤
      eliminatedBulkErrorConstant parameters L compact power * state.val.errorBudget power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialEliminatedBulkKernel_referenceDifference parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def eliminatedBulkErrorAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (eliminatedBulkErrorFamily parameters L compact lower positive bounded state)
    (eliminatedBulkErrorFamily_measurable parameters L compact lower positive bounded state)
    (eliminatedBulkErrorConstant parameters L compact power * state.val.errorBudget power)
    (eliminatedBulkErrorFamily_moment parameters L compact lower positive bounded state power)

theorem eliminatedBulkErrorAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ‖eliminatedBulkErrorAction parameters L compact lower positive bounded state power field‖ ≤
      eliminatedBulkErrorConstant parameters L compact power * state.val.errorBudget power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem eliminatedBulkErrorAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 8 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (eliminatedBulkErrorFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (eliminatedBulkErrorAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside


/-- Both constants are chosen before the physical state and positive inner radius.
The error reference is the exact circular eliminated (x,c,rV), and the bulk carrier uses the original phase. -/
theorem eliminatedBulkCompleted_uniform (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    ∃ regularConstant errorConstant : ℝ, 0 ≤ regularConstant ∧ 0 ≤ errorConstant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : RetainedInverseState parameters L compact) (field : DivisionRow 8 lower),
      ‖eliminatedBulkAction parameters L compact lower positive bounded state power field‖ ≤
        regularConstant * (1 + state.val.errorBudget power) * ‖field‖ ∧
      ‖eliminatedBulkErrorAction parameters L compact lower positive bounded state power field‖ ≤
        errorConstant * state.val.errorBudget power * ‖field‖ := by
  refine ⟨eliminatedBulkConstant parameters L compact power, eliminatedBulkErrorConstant parameters L compact power,
    eliminatedBulkConstant_nonnegative parameters L compact power, eliminatedBulkErrorConstant_nonnegative parameters L compact power, ?_⟩
  intro lower positive bounded state field
  exact ⟨eliminatedBulkAction_bound parameters L compact lower positive bounded state power field,
    eliminatedBulkErrorAction_bound parameters L compact lower positive bounded state power field⟩

end Grad.AnnularKernelL2
