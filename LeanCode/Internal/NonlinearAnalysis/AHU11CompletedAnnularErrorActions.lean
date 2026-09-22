import AHU10CircularKernelEntryContinuity

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

/-- The actual covariant error constant is chosen before
 the positive collar, physical state and input. -/
def normalizedCovariantErrorConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialNormalizedCovariantKernel_referenceDifference parameters L compact power)

theorem normalizedCovariantErrorConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ normalizedCovariantErrorConstant parameters L compact power :=
  (Classical.choose_spec (radialNormalizedCovariantKernel_referenceDifference parameters L compact power)).1

def normalizedCovariantErrorFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 7 3 :=
  fullKernelSub
    (radialNormalizedCovariantKernel parameters L compact state.val
      (collarRadius lower positive bounded x) state.property)
    (circularNormalizedCovariantKernel (radialKernelParameters parameters
      (collarRadius lower positive bounded x)) L)

theorem normalizedCovariantErrorFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (normalizedCovariantErrorFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (normalizedCovariantErrorFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [normalizedCovariantErrorFamily, fullKernelSub_entry, Function.comp_def, Pi.sub_apply] using
        (((radialNormalizedCovariantKernel_regular parameters L compact state).1 shift mode).sub
          (circularNormalizedCovariantKernel_entry_continuous parameters L shift mode)).comp
            (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem normalizedCovariantErrorFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (normalizedCovariantErrorFamily parameters L compact lower positive bounded state x) ≤
      normalizedCovariantErrorConstant parameters L compact power * state.errorBudget power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialNormalizedCovariantKernel_referenceDifference parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def normalizedCovariantErrorAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (normalizedCovariantErrorFamily parameters L compact lower positive bounded state)
    (normalizedCovariantErrorFamily_measurable parameters L compact lower positive bounded state)
    (normalizedCovariantErrorConstant parameters L compact power * state.errorBudget power)
    (normalizedCovariantErrorFamily_moment parameters L compact lower positive bounded state power)

theorem normalizedCovariantErrorAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ‖normalizedCovariantErrorAction parameters L compact lower positive bounded state power field‖ ≤
      normalizedCovariantErrorConstant parameters L compact power * state.errorBudget power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem normalizedCovariantErrorAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (normalizedCovariantErrorFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (normalizedCovariantErrorAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The actual rotated error constant is chosen before
 the positive collar, physical state and input. -/
def normalizedRotatedErrorConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact power)

theorem normalizedRotatedErrorConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ normalizedRotatedErrorConstant parameters L compact power :=
  (Classical.choose_spec (radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact power)).1

def normalizedRotatedErrorFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 7 3 :=
  fullKernelSub
    (radialNormalizedRotatedCovariantKernel parameters L compact state.val
      (collarRadius lower positive bounded x) state.property)
    (circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters
      (collarRadius lower positive bounded x)) L)

theorem normalizedRotatedErrorFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (normalizedRotatedErrorFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  by
    have continuous : Continuous (fun x =>
        (normalizedRotatedErrorFamily parameters L compact lower positive bounded state x).entry shift mode) := by
      simpa only [normalizedRotatedErrorFamily, fullKernelSub_entry, Function.comp_def, Pi.sub_apply] using
        (((radialNormalizedRotatedCovariantKernel_regular parameters L compact state).1 shift mode).sub
          (circularNormalizedRotatedCovariantKernel_entry_continuous parameters L shift mode)).comp
            (collarRadius_continuous lower positive bounded)
    exact continuous.aestronglyMeasurable

theorem normalizedRotatedErrorFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (normalizedRotatedErrorFamily parameters L compact lower positive bounded state x) ≤
      normalizedRotatedErrorConstant parameters L compact power * state.errorBudget power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialNormalizedRotatedCovariantKernel_referenceDifference parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def normalizedRotatedErrorAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (normalizedRotatedErrorFamily parameters L compact lower positive bounded state)
    (normalizedRotatedErrorFamily_measurable parameters L compact lower positive bounded state)
    (normalizedRotatedErrorConstant parameters L compact power * state.errorBudget power)
    (normalizedRotatedErrorFamily_moment parameters L compact lower positive bounded state power)

theorem normalizedRotatedErrorAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ‖normalizedRotatedErrorAction parameters L compact lower positive bounded state power field‖ ≤
      normalizedRotatedErrorConstant parameters L compact power * state.errorBudget power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem normalizedRotatedErrorAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (normalizedRotatedErrorFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (normalizedRotatedErrorAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The actual normalized errors act on the completed original annular L2 carrier,
with constant independent of the positive inner radius and linear in B_(power+7). -/
theorem normalizedCompletedErrors_uniform (parameters : PhaseParameters) (L compact : ℝ) :
    ∀ power, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : AnnularReconstructionState parameters L compact) (field : DivisionRow 7 lower),
      ‖normalizedCovariantErrorAction parameters L compact lower positive bounded state power field‖ +
        ‖normalizedRotatedErrorAction parameters L compact lower positive bounded state power field‖ ≤
      constant * (Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
        state.val.field state.val.rho state.val.epsilon (power + 7)) * ‖field‖ := by
  intro power
  refine ⟨normalizedCovariantErrorConstant parameters L compact power + normalizedRotatedErrorConstant parameters L compact power,
    add_nonneg (normalizedCovariantErrorConstant_nonnegative parameters L compact power)
      (normalizedRotatedErrorConstant_nonnegative parameters L compact power), ?_⟩
  intro lower positive bounded state field
  exact (add_le_add (normalizedCovariantErrorAction_bound parameters L compact lower positive bounded state power field)
    (normalizedRotatedErrorAction_bound parameters L compact lower positive bounded state power field)).trans_eq (by
      change _ + _ = (_ + _) * state.errorBudget power * ‖field‖
      ring)

end Grad.AnnularKernelL2
