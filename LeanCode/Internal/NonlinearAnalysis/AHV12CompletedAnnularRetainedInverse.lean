import AHV11RetainedInverseRadiusContinuity

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

/-- The actual retained inverse constant is chosen before
 the positive collar, physical state and input. -/
def retainedInverseConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialRetainedHighInverse_physicalMoments parameters L compact power)

theorem retainedInverseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ retainedInverseConstant parameters L compact power :=
  (Classical.choose_spec (radialRetainedHighInverse_physicalMoments parameters L compact power)).1

def retainedInverseFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 1 1 :=
  radialRetainedHighInverse parameters L compact state (collarRadius lower positive bounded x)

theorem retainedInverseFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (retainedInverseFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (retainedInverseFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [retainedInverseFamily, Function.comp_def] using
        ((radialRetainedHighInverse_regular parameters L compact state).1 shift mode).comp
          (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem retainedInverseFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (retainedInverseFamily parameters L compact lower positive bounded state x) ≤
      retainedInverseConstant parameters L compact power * state.val.val.size power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialRetainedHighInverse_physicalMoments parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def retainedInverseAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (retainedInverseFamily parameters L compact lower positive bounded state)
    (retainedInverseFamily_measurable parameters L compact lower positive bounded state)
    (retainedInverseConstant parameters L compact power * state.val.val.size power)
    (retainedInverseFamily_moment parameters L compact lower positive bounded state power)

theorem retainedInverseAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 1 lower) :
    ‖retainedInverseAction parameters L compact lower positive bounded state power field‖ ≤
      retainedInverseConstant parameters L compact power * state.val.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem retainedInverseAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 1 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (retainedInverseFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (retainedInverseAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The actual retained inverse error constant is chosen before
 the positive collar, physical state and input. -/
def retainedInverseErrorConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialRetainedHighInverse_referenceMoments parameters L compact power)

theorem retainedInverseErrorConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ retainedInverseErrorConstant parameters L compact power :=
  (Classical.choose_spec (radialRetainedHighInverse_referenceMoments parameters L compact power)).1

def retainedInverseErrorFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 1 1 :=
  fullKernelAdd
    (radialRetainedHighInverse parameters L compact state (collarRadius lower positive bounded x))
    (retainedBInverseKernel (radialKernelParameters parameters (collarRadius lower positive bounded x)))

theorem retainedInverseErrorFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (retainedInverseErrorFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (retainedInverseErrorFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [retainedInverseErrorFamily, Function.comp_def] using
        ((radialRetainedInverseError_regular parameters L compact state).1 shift mode).comp
          (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem retainedInverseErrorFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (retainedInverseErrorFamily parameters L compact lower positive bounded state x) ≤
      retainedInverseErrorConstant parameters L compact power * state.val.errorBudget power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialRetainedHighInverse_referenceMoments parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def retainedInverseErrorAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (retainedInverseErrorFamily parameters L compact lower positive bounded state)
    (retainedInverseErrorFamily_measurable parameters L compact lower positive bounded state)
    (retainedInverseErrorConstant parameters L compact power * state.val.errorBudget power)
    (retainedInverseErrorFamily_moment parameters L compact lower positive bounded state power)

theorem retainedInverseErrorAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 1 lower) :
    ‖retainedInverseErrorAction parameters L compact lower positive bounded state power field‖ ≤
      retainedInverseErrorConstant parameters L compact power * state.val.errorBudget power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem retainedInverseErrorAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ) (field : DivisionRow 1 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (retainedInverseErrorFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (retainedInverseErrorAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside


/-- Both constants are chosen before the physical state and positive inner radius.
The error reference is the negative b_m inverse, and the bulk carrier uses the original phase. -/
theorem retainedCompletedInverse_uniform (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    ∃ regularConstant errorConstant : ℝ, 0 ≤ regularConstant ∧ 0 ≤ errorConstant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : RetainedInverseState parameters L compact) (field : DivisionRow 1 lower),
      ‖retainedInverseAction parameters L compact lower positive bounded state power field‖ ≤
        regularConstant * (1 + state.val.errorBudget power) * ‖field‖ ∧
      ‖retainedInverseErrorAction parameters L compact lower positive bounded state power field‖ ≤
        errorConstant * state.val.errorBudget power * ‖field‖ := by
  refine ⟨retainedInverseConstant parameters L compact power, retainedInverseErrorConstant parameters L compact power,
    retainedInverseConstant_nonnegative parameters L compact power, retainedInverseErrorConstant_nonnegative parameters L compact power, ?_⟩
  intro lower positive bounded state field
  exact ⟨retainedInverseAction_bound parameters L compact lower positive bounded state power field,
    retainedInverseErrorAction_bound parameters L compact lower positive bounded state power field⟩

end Grad.AnnularKernelL2
