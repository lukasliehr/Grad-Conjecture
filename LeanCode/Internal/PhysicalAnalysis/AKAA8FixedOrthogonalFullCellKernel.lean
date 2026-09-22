import AKAA4ActualFullCellKernel
import ANS6ShiftPrimitive

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Algebra
open Grad.GenericCarriers

/-- A fixed orthogonal kernel on every integer cell. Coefficients depend
 only on the integration parameter, so spatial differentiation acts by the
 actual orthogonal covector action and introduces no coefficient derivative. -/
def startupFixedKernelData {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient)
    (integrable : Integrable coefficient measure) :
    Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension openUnitDisk where
  domainMeasurable := openUnitDisk_isOpen.measurableSet
  orthogonal := orthogonal
  invariant := invariant
  actionMeasurable := measurable
  coefficient := fun output input pair => if output = input then coefficient pair.1 else 0
  weight := fun output input parameter => if output = input then ‖coefficient parameter‖ else 0
  coefficientMeasurable := fun output input => by
    by_cases same : output = input
    · simp only [same, if_true]
      exact (coefficientMeasurable.comp measurable_fst).aestronglyMeasurable
    · simp only [same, if_false]
      exact aestronglyMeasurable_const
  weightMeasurable := fun _ _ => by
    split_ifs
    · exact coefficientMeasurable.norm
    · exact measurable_const
  weightNonnegative := fun _ _ _ => by split_ifs <;> positivity
  weightIntegrable := fun _ _ => by
    split_ifs
    · exact integrable.norm
    · exact integrable_zero _ _ _
  domination := fun output input => by
    filter_upwards with pair
    by_cases same : output = input <;> simp only [same, if_true, if_false, norm_zero, le_refl]
  rowBound := ∫ parameter, ‖coefficient parameter‖ ∂measure
  columnBound := ∫ parameter, ‖coefficient parameter‖ ∂measure
  rowNonnegative := integral_nonneg (fun _ => norm_nonneg _)
  columnNonnegative := integral_nonneg (fun _ => norm_nonneg _)
  rowsSummable := fun output => by
    have eq (input : ℤ) : (∫ parameter, (if output = input then ‖coefficient parameter‖ else 0) ∂measure) =
        if output = input then (∫ parameter, ‖coefficient parameter‖ ∂measure) else 0 := by
      split_ifs <;> simp only [integral_zero]
    simp_rw [eq]
    simpa only [eq_comm] using (hasSum_ite_eq output
      (∫ parameter, ‖coefficient parameter‖ ∂measure)).summable
  columnsSummable := fun input => by
    have eq (output : ℤ) : (∫ parameter, (if output = input then ‖coefficient parameter‖ else 0) ∂measure) =
        if output = input then (∫ parameter, ‖coefficient parameter‖ ∂measure) else 0 := by
      split_ifs <;> simp only [integral_zero]
    simp_rw [eq]
    exact (hasSum_ite_eq input (∫ parameter, ‖coefficient parameter‖ ∂measure)).summable
  rows := fun output => by
    have eq (input : ℤ) : (∫ parameter, (if output = input then ‖coefficient parameter‖ else 0) ∂measure) =
        if output = input then (∫ parameter, ‖coefficient parameter‖ ∂measure) else 0 := by
      split_ifs <;> simp only [integral_zero]
    simp_rw [eq]
    simp
  columns := fun input => by
    have eq (output : ℤ) : (∫ parameter, (if output = input then ‖coefficient parameter‖ else 0) ∂measure) =
        if output = input then (∫ parameter, ‖coefficient parameter‖ ∂measure) else 0 := by
      split_ifs <;> simp only [integral_zero]
    simp_rw [eq]
    simp

end Grad.GaugeCoefficients.Physical.RadialLedger
