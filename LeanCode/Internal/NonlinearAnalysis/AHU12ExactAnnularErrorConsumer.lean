import AHU11CompletedAnnularErrorActions

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation

/-- Grade-one errors have exactly the physical B8 size, uniformly in the
positive collar. The completed fields use the original radial L2 measure and phase. -/
theorem actualAnnularReconstructionError_B8 (parameters : PhaseParameters) (L compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : AnnularReconstructionState parameters L compact) (field : DivisionRow 7 lower),
      ‖normalizedCovariantErrorAction parameters L compact lower positive bounded state 1 field‖ +
        ‖normalizedRotatedErrorAction parameters L compact lower positive bounded state 1 field‖ ≤
      constant * physicalBudget parameters state.val.field state.val.rho state.val.epsilon 8 * ‖field‖ :=
  normalizedCompletedErrors_uniform parameters L compact 1

theorem normalizedCovariantErrorFamily_entry_inside
    (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift mode : ℤ × ℤ) :
    (normalizedCovariantErrorFamily parameters L compact lower positive bounded state radius).entry shift mode =
      (radialNormalizedCovariantKernel parameters L compact state.val
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩ state.property).entry shift mode -
      (circularNormalizedCovariantKernel (radialKernelParameters parameters
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩) L).entry shift mode := by
  have same : collarRadius lower positive bounded radius =
      (⟨radius, (positive.trans_le inside.1).le, inside.2⟩ : RadialPoint) :=
    Subtype.ext (collarRadius_literal lower positive bounded radius inside)
  have entryEquality := congrArg (fun point : RadialPoint =>
    (fullKernelSub (radialNormalizedCovariantKernel parameters L compact state.val point state.property)
      (circularNormalizedCovariantKernel (radialKernelParameters parameters point) L)).entry shift mode) same
  simpa only [normalizedCovariantErrorFamily, fullKernelSub_entry] using entryEquality

theorem normalizedRotatedErrorFamily_entry_inside
    (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift mode : ℤ × ℤ) :
    (normalizedRotatedErrorFamily parameters L compact lower positive bounded state radius).entry shift mode =
      (radialNormalizedRotatedCovariantKernel parameters L compact state.val
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩ state.property).entry shift mode -
      (circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩) L).entry shift mode := by
  have same : collarRadius lower positive bounded radius =
      (⟨radius, (positive.trans_le inside.1).le, inside.2⟩ : RadialPoint) :=
    Subtype.ext (collarRadius_literal lower positive bounded radius inside)
  have entryEquality := congrArg (fun point : RadialPoint =>
    (fullKernelSub (radialNormalizedRotatedCovariantKernel parameters L compact state.val point state.property)
      (circularNormalizedRotatedCovariantKernel (radialKernelParameters parameters point) L)).entry shift mode) same
  simpa only [normalizedRotatedErrorFamily, fullKernelSub_entry] using entryEquality

/-- Exact consumer: both completed error fields have the literal actual-minus-circular
Fourier series on every physical radius almost everywhere. No independently chosen
error kernel is an input to this theorem. -/
theorem actualAnnularReconstructionError_physical
    (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact) (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      HasSum (fun shift =>
        ((radialNormalizedCovariantKernel parameters L compact state.val
            ⟨radius, (positive.trans_le inside.1).le, inside.2⟩ state.property).entry shift
              (twoFrequencyTranslation shift mode) -
          (circularNormalizedCovariantKernel
            (radialKernelParameters parameters ⟨radius, (positive.trans_le inside.1).le, inside.2⟩) L).entry shift
              (twoFrequencyTranslation shift mode))
          (originalRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (normalizedCovariantErrorAction parameters L compact lower positive bounded state power field) radius mode) ∧
      HasSum (fun shift =>
        ((radialNormalizedRotatedCovariantKernel parameters L compact state.val
            ⟨radius, (positive.trans_le inside.1).le, inside.2⟩ state.property).entry shift
              (twoFrequencyTranslation shift mode) -
          (circularNormalizedRotatedCovariantKernel
            (radialKernelParameters parameters ⟨radius, (positive.trans_le inside.1).le, inside.2⟩) L).entry shift
              (twoFrequencyTranslation shift mode))
          (originalRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (normalizedRotatedErrorAction parameters L compact lower positive bounded state power field) radius mode) := by
  filter_upwards [normalizedCovariantErrorAction_physical parameters L compact lower positive bounded state power field,
    normalizedRotatedErrorAction_physical parameters L compact lower positive bounded state power field]
    with radius first second
  intro inside mode
  constructor
  · simpa only [normalizedCovariantErrorFamily_entry_inside parameters L compact lower positive bounded state radius inside]
      using first mode
  · simpa only [normalizedRotatedErrorFamily_entry_inside parameters L compact lower positive bounded state radius inside]
      using second mode

end Grad.AnnularKernelL2
