import AHV13EvaluatedInverseOneHigh

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation

/-- B8 controls the inverse error on the original completed annular carrier. -/
theorem retainedCompletedInverseError_B8 (parameters : PhaseParameters) (L compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : RetainedInverseState parameters L compact) (field : DivisionRow 1 lower),
      ‖retainedInverseErrorAction parameters L compact lower positive bounded state 1 field‖ ≤
        constant * physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  exact ⟨retainedInverseErrorConstant parameters L compact 1,
    retainedInverseErrorConstant_nonnegative parameters L compact 1,
    fun lower positive bounded state field =>
      retainedInverseErrorAction_bound parameters L compact lower positive bounded state 1 field⟩

theorem retainedInverseFamily_entry_inside (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift mode : ℤ × ℤ) :
    (retainedInverseFamily parameters L compact lower positive bounded state radius).entry shift mode =
      (radialRetainedHighInverse parameters L compact state
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩).entry shift mode := by
  have same : collarRadius lower positive bounded radius =
      (⟨radius, (positive.trans_le inside.1).le, inside.2⟩ : RadialPoint) :=
    Subtype.ext (collarRadius_literal lower positive bounded radius inside)
  exact congrArg (fun point : RadialPoint =>
    (radialRetainedHighInverse parameters L compact state point).entry shift mode) same

theorem retainedInverseErrorFamily_entry_inside (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift mode : ℤ × ℤ) :
    (retainedInverseErrorFamily parameters L compact lower positive bounded state radius).entry shift mode =
      (radialRetainedHighInverse parameters L compact state
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩).entry shift mode +
      (retainedBInverseKernel (radialKernelParameters parameters
        ⟨radius, (positive.trans_le inside.1).le, inside.2⟩)).entry shift mode := by
  have same : collarRadius lower positive bounded radius =
      (⟨radius, (positive.trans_le inside.1).le, inside.2⟩ : RadialPoint) :=
    Subtype.ext (collarRadius_literal lower positive bounded radius inside)
  have equality := congrArg (fun point : RadialPoint =>
    (fullKernelAdd (radialRetainedHighInverse parameters L compact state point)
      (retainedBInverseKernel (radialKernelParameters parameters point))).entry shift mode) same
  simpa only [retainedInverseErrorFamily, fullKernelAdd_entry] using equality

/-- Exact original-radius and original-phase consumer of the same actual inverse.
The error is A^{-1}-(-B^{-1}), so the literal reference contribution is plus B^{-1}. -/
theorem actualAnnularRetainedInverse_physical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (power : ℕ) (field : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      HasSum (fun shift =>
        (radialRetainedHighInverse parameters L compact state
          ⟨radius, (positive.trans_le inside.1).le, inside.2⟩).entry shift (twoFrequencyTranslation shift mode)
            (originalRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (retainedInverseAction parameters L compact lower positive bounded state power field) radius mode) ∧
      HasSum (fun shift =>
        ((radialRetainedHighInverse parameters L compact state
          ⟨radius, (positive.trans_le inside.1).le, inside.2⟩).entry shift (twoFrequencyTranslation shift mode) +
        (retainedBInverseKernel (radialKernelParameters parameters
          ⟨radius, (positive.trans_le inside.1).le, inside.2⟩)).entry shift (twoFrequencyTranslation shift mode))
            (originalRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (retainedInverseErrorAction parameters L compact lower positive bounded state power field) radius mode) := by
  filter_upwards [retainedInverseAction_physical parameters L compact lower positive bounded state power field,
    retainedInverseErrorAction_physical parameters L compact lower positive bounded state power field]
    with radius actual error
  intro inside mode
  constructor
  · simpa only [retainedInverseFamily_entry_inside parameters L compact lower positive bounded state radius inside]
      using actual mode
  · simpa only [retainedInverseErrorFamily_entry_inside parameters L compact lower positive bounded state radius inside]
      using error mode

end Grad.AnnularKernelL2
