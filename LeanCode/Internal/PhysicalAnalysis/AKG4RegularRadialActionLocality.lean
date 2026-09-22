import AKG3SameFullPhysicalCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularKernelL2 Grad.AnnularKernelContinuity
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

/-- Exact coefficient realization of the already accepted regular completed
radial action, at every unchanged inserted kernel grade. -/
theorem restrictionRegularAction_ae {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (field : DivisionRow source lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift =>
        (bulkWeightRatio parameters power (collarRadius lower positive bounded radius).val shift mode : ℂ) •
        (kernel (collarRadius lower positive bounded radius)).entry shift (twoFrequencyTranslation shift mode)
          (field (twoFrequencyTranslation shift mode) radius))
        (regularRadialBulkAction parameters power lower positive bounded kernel regular field mode radius) :=
  completedBulkKernel_ae parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded) _
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters power kernel regular)
    (regularRadialBulk_moment parameters power lower positive bounded kernel regular) field

/-- The continuous radius extensions agree on the smaller actual collar. -/
theorem restrictionCollarRadius (lower upper : ℝ) (included : lower ≤ upper)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (bounded : upper ≤ 1)
    (radius : ℝ) (inside : radius ∈ Icc upper 1) :
    collarRadius upper upperPositive bounded radius =
      collarRadius lower lowerPositive (included.trans bounded) radius := by
  apply Subtype.ext
  exact (collarRadius_literal upper upperPositive bounded radius inside).trans
    (collarRadius_literal lower lowerPositive (included.trans bounded) radius
      ⟨included.trans inside.1,inside.2⟩).symm

/-- Genuine endpoint locality of the completed regular kernel action.
The kernel, original radial phase, full convolution and analytic width are
identical; only the actual L2 collar measure is restricted. -/
theorem originalBulkRestriction_regularRadialBulkAction {source target : ℕ}
    (parameters : PhaseParameters) (power : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (bounded : upper ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (field : DivisionRow source lower) :
    originalBulkRestriction target lower upper included
      (regularRadialBulkAction parameters power lower lowerPositive (included.trans bounded) kernel regular field) =
    regularRadialBulkAction parameters power upper upperPositive bounded kernel regular
      (originalBulkRestriction source lower upper included field) := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae target lower upper included
      (regularRadialBulkAction parameters power lower lowerPositive (included.trans bounded) kernel regular field),
    (restrictionRegularAction_ae parameters power lower lowerPositive (included.trans bounded) kernel regular field).filter_mono
      (ae_mono (collarMeasure_le lower upper included)),
    restrictionRegularAction_ae parameters power upper upperPositive bounded kernel regular
      (originalBulkRestriction source lower upper included field),
    originalBulkRestriction_ae source lower upper included field,
    ae_restrict_mem measurableSet_Icc] with radius restricted sourceLaw targetLaw actual inside
  rw [restricted mode]
  have sameRadius := restrictionCollarRadius lower upper included lowerPositive upperPositive bounded radius inside
  have sameEntry := congrArg (fun point : RadialPoint => (kernel point).entry) sameRadius
  have same := targetLaw mode
  simp only [sameRadius,sameEntry,actual] at same
  exact (sourceLaw mode).unique same

end Grad.AnnularRestriction
