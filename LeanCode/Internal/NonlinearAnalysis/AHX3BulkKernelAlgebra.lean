import AHX2BulkKernelComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

variable (parameters : PhaseParameters) (power : ℕ) (radius : RadialPoint)

theorem bulkKernelAction_sub {src tgt : ℕ} (first second : RadialKernel parameters radius src tgt) :
    bulkKernelAction parameters power radius (fullKernelSub first second) =
      bulkKernelAction parameters power radius first - bulkKernelAction parameters power radius second := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  change bulkKernelAction parameters power radius (fullKernelSub first second) field mode =
    bulkKernelAction parameters power radius first field mode - bulkKernelAction parameters power radius second field mode
  exact (bulkKernelAction_coordinate parameters power radius (fullKernelSub first second) field mode).unique
    (by simpa only [fullKernelSub_entry, sub_apply, smul_sub] using
      HasSum.sub (bulkKernelAction_coordinate parameters power radius first field mode) (bulkKernelAction_coordinate parameters power radius second field mode))

theorem bulkKernelAction_add {src tgt : ℕ} (first second : RadialKernel parameters radius src tgt) :
    bulkKernelAction parameters power radius (fullKernelAdd first second) =
      bulkKernelAction parameters power radius first + bulkKernelAction parameters power radius second := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  change bulkKernelAction parameters power radius (fullKernelAdd first second) field mode =
    bulkKernelAction parameters power radius first field mode + bulkKernelAction parameters power radius second field mode
  exact (bulkKernelAction_coordinate parameters power radius (fullKernelAdd first second) field mode).unique
    (by simpa only [fullKernelAdd_entry, add_apply, smul_add] using
      HasSum.add (bulkKernelAction_coordinate parameters power radius first field mode) (bulkKernelAction_coordinate parameters power radius second field mode))

theorem bulkKernelAction_diagonal {src tgt : ℕ}
    (diagonal : (ℤ × ℤ) → ComplexEuclidean src →L[ℂ] ComplexEuclidean tgt)
    (bound : ℝ) (bounded : ∀ mode, ‖diagonal mode‖ ≤ bound)
    (field : CellL2 src) (mode : ℤ × ℤ) :
    bulkKernelAction parameters power radius
      (modeDiagonalKernel (radialKernelParameters parameters radius) src tgt diagonal bound bounded) field mode =
      diagonal mode (field mode) := by
  rw [← (bulkKernelAction_coordinate parameters power radius
    (modeDiagonalKernel (radialKernelParameters parameters radius) src tgt diagonal bound bounded) field mode).tsum_eq]
  rw [tsum_eq_single (0, 0) (by
    intro shift nonzero
    simp only [modeDiagonalKernel_entry, if_neg nonzero, zero_apply, smul_zero])]
  rw [modeDiagonalKernel_entry, if_pos rfl, bulkWeightRatio_zero]
  simp only [Complex.ofReal_one, one_smul, twoFrequencyTranslation_apply, sub_zero]

theorem bulkKernelAction_identity (dimension : ℕ) :
    bulkKernelAction parameters power radius (fullIdentityKernel (radialKernelParameters parameters radius) dimension) =
      ContinuousLinearMap.id ℂ (CellL2 dimension) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  change bulkKernelAction parameters power radius
    (fullIdentityKernel (radialKernelParameters parameters radius) dimension) field mode = field mode
  rw [← (bulkKernelAction_coordinate parameters power radius
    (fullIdentityKernel (radialKernelParameters parameters radius) dimension) field mode).tsum_eq]
  rw [tsum_eq_single (0, 0) (by
    intro shift nonzero
    rw [fullIdentityKernel_entry_ne_zero _ _ _ _ nonzero]
    simp only [zero_apply, smul_zero])]
  rw [fullIdentityKernel_entry_zero, bulkWeightRatio_zero]
  simp only [Complex.ofReal_one, one_smul, twoFrequencyTranslation_apply, sub_zero, ContinuousLinearMap.id_apply]

end Grad.AnnularKernelL2
