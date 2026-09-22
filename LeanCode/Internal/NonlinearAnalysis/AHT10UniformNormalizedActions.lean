import AHT9ExactAnnularConsumer

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

/-- The normalized actual covariant kernel constant is chosen before
 the positive collar, physical state and input. -/
def normalizedCovariantConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialNormalizedCovariantKernel_physicalMoments parameters L compact power)

theorem normalizedCovariantConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ normalizedCovariantConstant parameters L compact power :=
  (Classical.choose_spec (radialNormalizedCovariantKernel_physicalMoments parameters L compact power)).1

def normalizedCovariantFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 7 3 :=
  radialNormalizedCovariantKernel parameters L compact state.val
    (collarRadius lower positive bounded x) state.property

theorem normalizedCovariantFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (normalizedCovariantFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  (((radialNormalizedCovariantKernel_regular parameters L compact state).1 shift mode).comp
    (collarRadius_continuous lower positive bounded)).aestronglyMeasurable

theorem normalizedCovariantFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (normalizedCovariantFamily parameters L compact lower positive bounded state x) ≤
      normalizedCovariantConstant parameters L compact power * state.val.size power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialNormalizedCovariantKernel_physicalMoments parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def normalizedCovariantAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (normalizedCovariantFamily parameters L compact lower positive bounded state)
    (normalizedCovariantFamily_measurable parameters L compact lower positive bounded state)
    (normalizedCovariantConstant parameters L compact power * state.val.size power)
    (normalizedCovariantFamily_moment parameters L compact lower positive bounded state power)

theorem normalizedCovariantAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ‖normalizedCovariantAction parameters L compact lower positive bounded state power field‖ ≤
      normalizedCovariantConstant parameters L compact power * state.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem normalizedCovariantAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (normalizedCovariantFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (normalizedCovariantAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The normalized actual rotated kernel constant is chosen before
 the positive collar, physical state and input. -/
def normalizedRotatedConstant (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) : ℝ :=
  Classical.choose (radialNormalizedRotatedCovariantKernel_physicalMoments parameters L compact power)

theorem normalizedRotatedConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    0 ≤ normalizedRotatedConstant parameters L compact power :=
  (Classical.choose_spec (radialNormalizedRotatedCovariantKernel_physicalMoments parameters L compact power)).1

def normalizedRotatedFamily (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (x : ℝ) :
    RadialKernel parameters (collarRadius lower positive bounded x) 7 3 :=
  radialNormalizedRotatedCovariantKernel parameters L compact state.val
    (collarRadius lower positive bounded x) state.property

theorem normalizedRotatedFamily_measurable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      (normalizedRotatedFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  (((radialNormalizedRotatedCovariantKernel_regular parameters L compact state).1 shift mode).comp
    (collarRadius_continuous lower positive bounded)).aestronglyMeasurable

theorem normalizedRotatedFamily_moment (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
        (normalizedRotatedFamily parameters L compact lower positive bounded state x) ≤
      normalizedRotatedConstant parameters L compact power * state.val.size power := by
  filter_upwards with x
  exact (Classical.choose_spec (radialNormalizedRotatedCovariantKernel_physicalMoments parameters L compact power)).2
    state (collarRadius lower positive bounded x)

def normalizedRotatedAction (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) :
    DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (normalizedRotatedFamily parameters L compact lower positive bounded state)
    (normalizedRotatedFamily_measurable parameters L compact lower positive bounded state)
    (normalizedRotatedConstant parameters L compact power * state.val.size power)
    (normalizedRotatedFamily_moment parameters L compact lower positive bounded state power)

theorem normalizedRotatedAction_bound (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ‖normalizedRotatedAction parameters L compact lower positive bounded state power field‖ ≤
      normalizedRotatedConstant parameters L compact power * state.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem normalizedRotatedAction_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (normalizedRotatedFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (normalizedRotatedAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- The genuine normalized original reconstruction acts on completed L2
with a constant independent of the inner radius. The inputs are the normalized
seven slots of AHP; the original-slot operator retains its separate 1/r factors. -/
theorem normalizedCompletedCovariants_uniform (parameters : PhaseParameters) (L compact : ℝ) :
    ∀ power, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : AnnularReconstructionState parameters L compact) (field : DivisionRow 7 lower),
      ‖normalizedCovariantAction parameters L compact lower positive bounded state power field‖ +
        ‖normalizedRotatedAction parameters L compact lower positive bounded state power field‖ ≤
      constant * (1 + Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
        state.val.field state.val.rho state.val.epsilon (power + 7)) * ‖field‖ := by
  intro power
  refine ⟨normalizedCovariantConstant parameters L compact power + normalizedRotatedConstant parameters L compact power,
    add_nonneg (normalizedCovariantConstant_nonnegative parameters L compact power)
      (normalizedRotatedConstant_nonnegative parameters L compact power), ?_⟩
  intro lower positive bounded state field
  exact (add_le_add (normalizedCovariantAction_bound parameters L compact lower positive bounded state power field)
    (normalizedRotatedAction_bound parameters L compact lower positive bounded state power field)).trans_eq (by
      change _ + _ = (_ + _) * state.val.size power * ‖field‖
      ring)

end Grad.AnnularKernelL2
