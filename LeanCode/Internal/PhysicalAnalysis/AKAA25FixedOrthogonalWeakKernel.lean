import AKAA24ActualMatrixFirstGraphBound

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure Classical
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel

theorem startupParameterDerivative {Parameter : Type*} {inputDimension outputDimension : ℕ}
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (index : ℕ × ℕ) (pair : Parameter × Grad.PDEBootstrap.Spatial) :
    Grad.RepresentedKernel.coefficientDerivative index (fun pair => coefficient pair.1) pair =
      if index = (0, 0) then coefficient pair.1 else 0 := by
  by_cases zero : index = (0, 0)
  · subst index
    rfl
  · have nonzero : index.1 + index.2 ≠ 0 := by
      intro equality
      apply zero
      exact Prod.ext (by omega) (by omega)
    rw [if_neg zero]
    change iteratedFDeriv ℝ (index.1 + index.2) (fun _ : Grad.PDEBootstrap.Spatial => coefficient pair.1) pair.2 _ = 0
    rw [iteratedFDeriv_const_of_ne nonzero]
    rfl

/-- Genuine RKWD data for every actual fixed angular/reflection pullback.
 No coefficient derivative is manufactured: all positive spatial orders
 vanish, while the orthogonal covectors remain in the weak allocation. -/
def startupFixedRawData {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient) (integrable : Integrable coefficient measure) :
    RawKernelData measure inputDimension outputDimension openUnitDisk := by
  let data := startupFixedKernelData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable
  have derivative (index : ℕ × ℕ) (output input : ℤ) :
      Grad.RepresentedKernel.coefficientDerivative index (data.coefficient output input) =
      (fun pair => if index = (0, 0) then data.coefficient output input pair else 0) := by
    funext pair
    exact startupParameterDerivative (fun parameter => if output = input then coefficient parameter else 0) index pair
  exact {
    domainOpen := openUnitDisk_isOpen
    orthogonal := orthogonal
    invariant := invariant
    actionMeasurable := measurable
    coefficient := data.coefficient
    coefficientSmooth := fun output input parameter => by
      change ContDiffOn ℝ ∞ (fun _ : Grad.PDEBootstrap.Spatial =>
        if output = input then coefficient parameter else 0) openUnitDisk
      exact contDiffOn_const
    derivativeMeasurable := fun index output input => by
      rw [derivative]
      by_cases zero : index = (0, 0)
      · simp only [if_pos zero]
        exact data.coefficientMeasurable output input
      · simp only [if_neg zero]
        exact aestronglyMeasurable_const
    envelope := fun _ _ _ => 1
    envelopeOneLe := fun _ _ => Filter.Eventually.of_forall (fun _ => le_rfl)
    majorant := fun _ _ => data.weight
    majorantMeasurable := fun _ _ => data.weightMeasurable
    majorantNonnegative := fun _ _ => data.weightNonnegative
    majorantIntegrable := fun _ _ => data.weightIntegrable
    domination := fun index moment output input => by
      filter_upwards [] with pair
      rw [congrFun (derivative index output input) pair]
      by_cases zero : index = (0, 0)
      · rw [if_pos zero]
        by_cases same : output = input
        · subst input
          simp [data, startupFixedKernelData, Grad.CellWeights.cellWeight]
        · simp only [data, startupFixedKernelData, if_neg same, norm_zero, zero_mul, le_refl]
      · rw [if_neg zero, norm_zero, zero_mul, zero_mul]
        exact data.weightNonnegative output input pair.1
    rowBound := fun _ _ => data.rowBound
    columnBound := fun _ _ => data.columnBound
    rowNonnegative := fun _ _ => data.rowNonnegative
    columnNonnegative := fun _ _ => data.columnNonnegative
    rowsSummable := fun _ _ => data.rowsSummable
    columnsSummable := fun _ _ => data.columnsSummable
    rows := fun _ _ => data.rows
    columns := fun _ _ => data.columns }

theorem startupFixedRawData_operator {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {inputDimension outputDimension : ℕ}
    (orthogonal : Parameter → Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (measurable : Measurable (fun pair : Parameter × Grad.PDEBootstrap.Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue inputDimension outputDimension)
    (coefficientMeasurable : Measurable coefficient) (integrable : Integrable coefficient measure) :
    operator (startupFixedRawData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable) (0, 0) 0 =
      Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable) := by
  apply startupKernel_congr
    (l2Data (startupFixedRawData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable) (0, 0) 0)
    (startupFixedKernelData measure orthogonal invariant measurable coefficient coefficientMeasurable integrable) rfl
  intro output input
  filter_upwards [] with pair
  change Grad.CellWeights.derivativeFactor 0 (output - input) •
    (if output = input then coefficient pair.1 else 0) = _
  rw [Grad.CellWeights.derivativeFactor, pow_zero, one_smul]
  rfl

end Grad.CartesianStartup
