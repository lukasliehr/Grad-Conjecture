import AHX1BulkWeightCocycle

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

private abbrev Shift := ℤ × ℤ

/-- The actual original-phase L2 action respects the already-constructed
full input-mode-dependent kernel composition. -/
theorem bulkKernelAction_comp {input middle output : ℕ}
    (parameters : PhaseParameters) (power : ℕ) (radius : RadialPoint)
    (outer : RadialKernel parameters radius middle output)
    (inner : RadialKernel parameters radius input middle) :
    bulkKernelAction parameters power radius (fullKernelComposition outer inner) =
      (bulkKernelAction parameters power radius outer).comp
        (bulkKernelAction parameters power radius inner) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  have pairSummable := bulkActionPairTerm_summable parameters power radius outer inner field mode
  have sheared : Summable (fun pair : Shift × Shift =>
      bulkActionPairTerm parameters power radius outer inner field mode
        (twoFrequencyConvolutionEquiv pair)) :=
    twoFrequencyConvolutionEquiv.summable_iff.mpr pairSummable
  have leftTerm (total : Shift) :
      (bulkWeightRatio parameters power radius.val total mode : ℂ) •
        (fullKernelComposition outer inner).entry total (twoFrequencyTranslation total mode)
          (field (twoFrequencyTranslation total mode)) =
        ∑' middleShift : Shift, bulkActionPairTerm parameters power radius outer inner field mode
          (total - middleShift, middleShift) := by
    rw [fullKernelComposition_entry]
    let evaluate : (ComplexEuclidean input →L[ℂ] ComplexEuclidean output) →L[ℂ]
        ComplexEuclidean output :=
      (bulkWeightRatio parameters power radius.val total mode : ℂ) •
        ContinuousLinearMap.apply ℂ (ComplexEuclidean output) (field (twoFrequencyTranslation total mode))
    change evaluate (∑' middleShift : Shift, fullKernelCompositionTerm outer inner total middleShift
      (twoFrequencyTranslation total mode)) = _
    rw [evaluate.map_tsum (fullKernelCompositionTerm_summable outer inner total
      (twoFrequencyTranslation total mode))]
    apply tsum_congr
    intro middleShift
    rw [bulkActionPairTerm_literal]
    have totalEq : total - middleShift + middleShift = total := sub_add_cancel _ _
    have outerInput : twoFrequencyTranslation total mode + middleShift =
        twoFrequencyTranslation (total - middleShift) mode := by
      ext <;> simp only [twoFrequencyTranslation_apply] <;> dsimp <;> ring
    rw [totalEq]
    change (bulkWeightRatio parameters power radius.val total mode : ℂ) •
      outer.entry (total - middleShift) (twoFrequencyTranslation total mode + middleShift)
        (inner.entry middleShift (twoFrequencyTranslation total mode)
          (field (twoFrequencyTranslation total mode))) = _
    rw [outerInput]
  have rightTerm (outerShift : Shift) :
      (bulkWeightRatio parameters power radius.val outerShift mode : ℂ) •
        outer.entry outerShift (twoFrequencyTranslation outerShift mode)
          (bulkKernelAction parameters power radius inner field (twoFrequencyTranslation outerShift mode)) =
        ∑' innerShift : Shift, bulkActionPairTerm parameters power radius outer inner field mode
          (outerShift, innerShift) := by
    have innerSum := bulkKernelAction_hasSum parameters power radius inner field
    have mapped := (bulkShiftAction parameters power radius outer outerShift).hasSum innerSum
    have coordinate := (lp.evalCLM ℂ (fun _ : Shift => ComplexEuclidean output) 2 mode).hasSum mapped
    exact coordinate.tsum_eq.symm
  have leftSum := bulkKernelAction_coordinate parameters power radius (fullKernelComposition outer inner) field mode
  have rightSum := bulkKernelAction_coordinate parameters power radius outer
    (bulkKernelAction parameters power radius inner field) mode
  change bulkKernelAction parameters power radius (fullKernelComposition outer inner) field mode =
    bulkKernelAction parameters power radius outer (bulkKernelAction parameters power radius inner field) mode
  calc
    _ = ∑' total : Shift, (bulkWeightRatio parameters power radius.val total mode : ℂ) •
        (fullKernelComposition outer inner).entry total (twoFrequencyTranslation total mode)
          (field (twoFrequencyTranslation total mode)) := leftSum.tsum_eq.symm
    _ = ∑' total : Shift, ∑' middleShift : Shift,
        bulkActionPairTerm parameters power radius outer inner field mode
          (total - middleShift, middleShift) := tsum_congr leftTerm
    _ = ∑' pair : Shift × Shift, bulkActionPairTerm parameters power radius outer inner field mode
        (twoFrequencyConvolutionEquiv pair) := sheared.tsum_prod.symm
    _ = ∑' pair : Shift × Shift, bulkActionPairTerm parameters power radius outer inner field mode pair :=
      twoFrequencyConvolutionEquiv.tsum_eq _
    _ = ∑' outerShift : Shift, ∑' innerShift : Shift,
        bulkActionPairTerm parameters power radius outer inner field mode (outerShift, innerShift) :=
      pairSummable.tsum_prod
    _ = ∑' outerShift : Shift, (bulkWeightRatio parameters power radius.val outerShift mode : ℂ) •
        outer.entry outerShift (twoFrequencyTranslation outerShift mode)
          (bulkKernelAction parameters power radius inner field (twoFrequencyTranslation outerShift mode)) :=
      tsum_congr (fun outerShift => (rightTerm outerShift).symm)
    _ = _ := rightSum.tsum_eq

end Grad.AnnularKernelL2
