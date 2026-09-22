import AHT8OriginalCompletedCovariants

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact)

theorem originalCovariantFamily_entry_inside (x : ℝ) (inside : x ∈ Icc lower 1)
    (shift mode : ℤ × ℤ) :
    (originalCovariantFamily parameters L compact lower positive bounded state x).entry shift mode =
      (radialCovariantKernel parameters L compact state.val
        ⟨x, (positive.trans_le inside.1).le, inside.2⟩ state.property (positive.trans_le inside.1)).entry shift mode := by
  have same : positiveCollarRadius lower positive bounded x =
      (⟨⟨x, (positive.trans_le inside.1).le, inside.2⟩, positive.trans_le inside.1⟩ : PositiveRadialPoint) :=
    Subtype.ext (Subtype.ext (collarRadius_literal lower positive bounded x inside))
  have entryEquality := congrArg (fun point : PositiveRadialPoint =>
    (radialCovariantKernel parameters L compact state.val point.val state.property point.property).entry shift mode) same
  simpa only [originalCovariantFamily, positiveCollarRadius] using entryEquality

theorem originalRotatedFamily_entry_inside (x : ℝ) (inside : x ∈ Icc lower 1)
    (shift mode : ℤ × ℤ) :
    (originalRotatedFamily parameters L compact lower positive bounded state x).entry shift mode =
      (radialRotatedCovariantKernel parameters L compact state.val
        ⟨x, (positive.trans_le inside.1).le, inside.2⟩ state.property (positive.trans_le inside.1)).entry shift mode := by
  have same : positiveCollarRadius lower positive bounded x =
      (⟨⟨x, (positive.trans_le inside.1).le, inside.2⟩, positive.trans_le inside.1⟩ : PositiveRadialPoint) :=
    Subtype.ext (Subtype.ext (collarRadius_literal lower positive bounded x inside))
  have entryEquality := congrArg (fun point : PositiveRadialPoint =>
    (radialRotatedCovariantKernel parameters L compact state.val point.val state.property point.property).entry shift mode) same
  simpa only [originalRotatedFamily, positiveCollarRadius] using entryEquality

theorem actualCovariantAction_physical (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ (inside : x ∈ Icc lower 1) (mode : ℤ × ℤ),
      HasSum (fun shift =>
        (radialCovariantKernel parameters L compact state.val
          ⟨x, (positive.trans_le inside.1).le, inside.2⟩ state.property (positive.trans_le inside.1)).entry
          shift (twoFrequencyTranslation shift mode)
          (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (originalCovariantAction parameters L compact lower positive bounded state power field) x mode) := by
  filter_upwards [originalCovariantAction_physical parameters L compact lower positive bounded state power field]
    with x literal
  intro inside mode
  simpa only [originalCovariantFamily_entry_inside parameters L compact lower positive bounded state x inside] using literal mode

theorem actualRotatedAction_physical (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ (inside : x ∈ Icc lower 1) (mode : ℤ × ℤ),
      HasSum (fun shift =>
        (radialRotatedCovariantKernel parameters L compact state.val
          ⟨x, (positive.trans_le inside.1).le, inside.2⟩ state.property (positive.trans_le inside.1)).entry
          shift (twoFrequencyTranslation shift mode)
          (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (originalRotatedAction parameters L compact lower positive bounded state power field) x mode) := by
  filter_upwards [originalRotatedAction_physical parameters L compact lower positive bounded state power field]
    with x literal
  intro inside mode
  simpa only [originalRotatedFamily_entry_inside parameters L compact lower positive bounded state x inside] using literal mode

/-- The norm used by the actual completed operators is the literal
manuscript r dr norm, including original analytic phase and all Fourier modes. -/
theorem actualCovariantAction_original_norm (power : ℕ) (field : DivisionRow 7 lower) :
    ‖originalCovariantAction parameters L compact lower positive bounded state power field‖ ^ 2 =
      ∑' mode : ℤ × ℤ, ∫ x,
        x * (Real.exp (radialPhase parameters x mode.2) * annularFrequency mode.1 mode.2 ^ power) ^ 2 *
          ‖originalRowCoefficient parameters power lower
            (originalCovariantAction parameters L compact lower positive bounded state power field) x mode‖ ^ 2
        ∂volume.restrict (Icc lower 1) :=
  originalRow_norm_sq parameters power lower positive _

theorem actualRotatedAction_original_norm (power : ℕ) (field : DivisionRow 7 lower) :
    ‖originalRotatedAction parameters L compact lower positive bounded state power field‖ ^ 2 =
      ∑' mode : ℤ × ℤ, ∫ x,
        x * (Real.exp (radialPhase parameters x mode.2) * annularFrequency mode.1 mode.2 ^ power) ^ 2 *
          ‖originalRowCoefficient parameters power lower
            (originalRotatedAction parameters L compact lower positive bounded state power field) x mode‖ ^ 2
        ∂volume.restrict (Icc lower 1) :=
  originalRow_norm_sq parameters power lower positive _

end Grad.AnnularKernelL2
