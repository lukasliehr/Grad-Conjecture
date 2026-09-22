import AKZ4LiteralMatrixFourierCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.BoundaryKernelAction Grad.AnnularRestriction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

/-- The existing completed radial action applied to the actual original
matrix family. The input/output power uses the same conjugation. -/
def originalMatrixBulkAction : DivisionRow input lower →L[ℂ] DivisionRow output lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (originalMatrixRadialKernel parameters family coherent) (originalMatrixRadialKernel_regular parameters family coherent)

theorem originalMatrixBulkAction_bound (field : DivisionRow input lower) :
    ‖originalMatrixBulkAction parameters family coherent power lower positive bounded field‖ ≤
      physicalMatrixKernelConstant parameters input output power * ‖family (power + 1)‖ * ‖field‖ := by
  have moments : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded radius)) power
        (originalMatrixRadialKernel parameters family coherent (collarRadius lower positive bounded radius)) ≤
        physicalMatrixKernelConstant parameters input output power * ‖family (power + 1)‖ :=
    Eventually.of_forall (fun radius => originalMatrixRadialKernel_bound parameters family coherent (collarRadius lower positive bounded radius) power)
  have same := regularRadialBulkAction_eq_completed parameters power lower positive bounded
    (originalMatrixRadialKernel parameters family coherent) (originalMatrixRadialKernel_regular parameters family coherent)
    (regularRadialBulk_measurable parameters lower positive bounded _ (originalMatrixRadialKernel_regular parameters family coherent))
    (physicalMatrixKernelConstant parameters input output power * ‖family (power + 1)‖) moments
  change ‖regularRadialBulkAction parameters power lower positive bounded _ _ field‖ ≤ _
  rw [same]
  exact completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem originalMatrixBulkAction_physical (field : DivisionRow input lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (originalMatrixRadialKernel parameters family coherent (collarRadius lower positive bounded radius)).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower (originalMatrixBulkAction parameters family coherent power lower positive bounded field) radius mode) := by
  unfold originalMatrixBulkAction regularRadialBulkAction
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  exact collarRadius_literal lower positive bounded radius inside

theorem originalMatrixBulkAction_restriction (upper : ℝ) (upperPositive : 0 < upper) (upperBounded : upper ≤ 1)
    (included : lower ≤ upper) (field : DivisionRow input lower) :
    originalBulkRestriction output lower upper included
      (originalMatrixBulkAction parameters family coherent power lower positive bounded field) =
      originalMatrixBulkAction parameters family coherent power upper upperPositive upperBounded
        (originalBulkRestriction input lower upper included field) :=
  originalBulkRestriction_regularRadialBulkAction parameters power lower upper included positive upperPositive upperBounded
    (originalMatrixRadialKernel parameters family coherent) (originalMatrixRadialKernel_regular parameters family coherent) field

end Grad.ActualPhysicalField
