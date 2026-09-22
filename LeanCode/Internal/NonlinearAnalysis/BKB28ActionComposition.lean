import BKB27ActionAlgebra

noncomputable section

set_option maxHeartbeats 1800000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

private abbrev KernelShift := ℤ × ℤ

theorem fullNegativeKernelAction_comp
    {inputDimension middleDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension) :
    fullNegativeKernelAction parameters angular cell
        (fullKernelComposition outer inner) =
      (fullNegativeKernelAction parameters angular cell outer).comp
        (fullNegativeKernelAction parameters angular cell inner) := by
  apply ContinuousLinearMap.ext
  intro field
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  have pairSummable :=
    fullKernelActionPairTerm_summable parameters angular cell outer inner field mode
  have shearedPairSummable : Summable (fun pair : KernelShift × KernelShift =>
      fullKernelActionPairTerm angular cell outer inner field mode
        (twoFrequencyConvolutionEquiv pair)) :=
    twoFrequencyConvolutionEquiv.summable_iff.mpr pairSummable
  have leftTerm (total : KernelShift) :
      (fullKernelComposition outer inner).entry total
          (twoFrequencyTranslation total mode)
          (negativeTraceCoefficient parameters angular cell field
            (twoFrequencyTranslation total mode)) =
        ∑' middle : KernelShift,
          fullKernelActionPairTerm angular cell outer inner field mode
            (total - middle, middle) := by
    rw [fullKernelComposition_entry]
    let evaluate :
        (ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension) →L[ℂ]
          ComplexEuclidean outputDimension :=
      ContinuousLinearMap.apply ℂ (ComplexEuclidean outputDimension)
        (negativeTraceCoefficient parameters angular cell field
          (twoFrequencyTranslation total mode))
    change evaluate (∑' middle : KernelShift,
        fullKernelCompositionTerm outer inner total middle
          (twoFrequencyTranslation total mode)) = _
    rw [evaluate.map_tsum
      (fullKernelCompositionTerm_summable outer inner total
        (twoFrequencyTranslation total mode))]
    apply tsum_congr
    intro middle
    unfold evaluate fullKernelCompositionTerm fullKernelActionPairTerm
    have outerInput :
        twoFrequencyTranslation total mode + middle =
          twoFrequencyTranslation (total - middle) mode := by
      ext <;> simp only [twoFrequencyTranslation_apply] <;> dsimp <;> ring
    have innerInput :
        twoFrequencyTranslation total mode =
          twoFrequencyTranslation middle
            (twoFrequencyTranslation (total - middle) mode) := by
      ext <;> simp only [twoFrequencyTranslation_apply] <;> dsimp <;> ring
    rw [outerInput, innerInput]
    rfl
  have rightTerm (outerShift : KernelShift) :
      outer.entry outerShift (twoFrequencyTranslation outerShift mode)
          (negativeTraceCoefficient parameters angular cell
            (fullNegativeKernelAction parameters angular cell inner field)
            (twoFrequencyTranslation outerShift mode)) =
        ∑' innerShift : KernelShift,
          fullKernelActionPairTerm angular cell outer inner field mode
            (outerShift, innerShift) := by
    have innerSum := fullNegativeKernelAction_coefficient_hasSum
      parameters angular cell inner field
        (twoFrequencyTranslation outerShift mode)
    have mapped :=
      (outer.entry outerShift
        (twoFrequencyTranslation outerShift mode)).hasSum innerSum
    exact mapped.tsum_eq.symm
  have leftSum := fullNegativeKernelAction_coefficient_hasSum
    parameters angular cell (fullKernelComposition outer inner) field mode
  have rightSum := fullNegativeKernelAction_coefficient_hasSum
    parameters angular cell outer
      (fullNegativeKernelAction parameters angular cell inner field) mode
  calc
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (fullKernelComposition outer inner) field) mode =
        ∑' total : KernelShift,
          (fullKernelComposition outer inner).entry total
            (twoFrequencyTranslation total mode)
            (negativeTraceCoefficient parameters angular cell field
              (twoFrequencyTranslation total mode)) := leftSum.tsum_eq.symm
    _ = ∑' total : KernelShift, ∑' middle : KernelShift,
          fullKernelActionPairTerm angular cell outer inner field mode
            (total - middle, middle) := by
      apply tsum_congr
      exact leftTerm
    _ = ∑' pair : KernelShift × KernelShift,
          fullKernelActionPairTerm angular cell outer inner field mode
            (twoFrequencyConvolutionEquiv pair) :=
      shearedPairSummable.tsum_prod.symm
    _ = ∑' pair : KernelShift × KernelShift,
          fullKernelActionPairTerm angular cell outer inner field mode pair :=
      twoFrequencyConvolutionEquiv.tsum_eq
        (fullKernelActionPairTerm angular cell outer inner field mode)
    _ = ∑' outerShift : KernelShift, ∑' innerShift : KernelShift,
          fullKernelActionPairTerm angular cell outer inner field mode
            (outerShift, innerShift) := pairSummable.tsum_prod
    _ = ∑' outerShift : KernelShift,
          outer.entry outerShift (twoFrequencyTranslation outerShift mode)
            (negativeTraceCoefficient parameters angular cell
              (fullNegativeKernelAction parameters angular cell inner field)
              (twoFrequencyTranslation outerShift mode)) := by
      apply tsum_congr
      intro outerShift
      exact (rightTerm outerShift).symm
    _ = negativeTraceCoefficient parameters angular cell
          (fullNegativeKernelAction parameters angular cell outer
            (fullNegativeKernelAction parameters angular cell inner field)) mode :=
      rightSum.tsum_eq

end Grad.BoundaryKernelAction
