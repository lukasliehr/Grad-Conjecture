import RK1Data

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel

variable {Parameter : Type*} [MeasurableSpace Parameter]
  {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
  (data : RawKernelData measure inputDimension outputDimension domain)

theorem derivative_domination (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ) :
    ∀ᵐ pair ∂measure.prod (volume.restrict domain),
      ‖coefficientDerivative multiindex (data.coefficient output input) pair‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment ≤
          data.majorant multiindex moment output input pair.1 := by
  filter_upwards [data.domination multiindex moment output input,
    data.envelopeOneLe output input] with pair dominated envelope
  exact (le_mul_of_one_le_right
    (mul_nonneg (norm_nonneg _) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _))
    envelope).trans dominated

theorem momentCoefficient_measurable (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ) :
    AEStronglyMeasurable (momentCoefficient data multiindex moment output input)
      (measure.prod (volume.restrict domain)) :=
  (data.derivativeMeasurable multiindex output input).const_smul
    (Grad.CellWeights.derivativeFactor moment (output - input))

theorem momentCoefficient_domination (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ) :
    ∀ᵐ pair ∂measure.prod (volume.restrict domain),
      ‖momentCoefficient data multiindex moment output input pair‖ ≤
        data.majorant multiindex moment output input pair.1 := by
  filter_upwards [derivative_domination data multiindex moment output input] with pair dominated
  calc
    ‖momentCoefficient data multiindex moment output input pair‖ =
        ‖Grad.CellWeights.derivativeFactor moment (output - input)‖ *
          ‖coefficientDerivative multiindex (data.coefficient output input) pair‖ := norm_smul _ _
    _ ≤ Grad.CellWeights.cellWeight (output - input) ^ moment *
          ‖coefficientDerivative multiindex (data.coefficient output input) pair‖ :=
      mul_le_mul_of_nonneg_right
        (Grad.CellBinomial.derivativeFactor_le_positive moment moment le_rfl (output - input))
        (norm_nonneg _)
    _ = ‖coefficientDerivative multiindex (data.coefficient output input) pair‖ *
          Grad.CellWeights.cellWeight (output - input) ^ moment := mul_comm _ _
    _ ≤ data.majorant multiindex moment output input pair.1 := dominated

def l2Data (multiindex : ℕ × ℕ) (moment : ℕ) :
    Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain where
  domainMeasurable := data.domainOpen.measurableSet
  orthogonal := data.orthogonal
  invariant := data.invariant
  actionMeasurable := data.actionMeasurable
  coefficient := momentCoefficient data multiindex moment
  weight := data.majorant multiindex moment
  coefficientMeasurable := momentCoefficient_measurable data multiindex moment
  weightMeasurable := data.majorantMeasurable multiindex moment
  weightNonnegative := data.majorantNonnegative multiindex moment
  weightIntegrable := data.majorantIntegrable multiindex moment
  domination := momentCoefficient_domination data multiindex moment
  rowBound := data.rowBound multiindex moment
  columnBound := data.columnBound multiindex moment
  rowNonnegative := data.rowNonnegative multiindex moment
  columnNonnegative := data.columnNonnegative multiindex moment
  rowsSummable := data.rowsSummable multiindex moment
  columnsSummable := data.columnsSummable multiindex moment
  rows := data.rows multiindex moment
  columns := data.columns multiindex moment

theorem l2Data_coefficient (multiindex : ℕ × ℕ) (moment : ℕ) (output input : ℤ)
    (pair : Parameter × Spatial) :
    (l2Data data multiindex moment).coefficient output input pair =
      Grad.CellWeights.derivativeFactor moment (output - input) •
        coefficientDerivative multiindex (data.coefficient output input) pair := rfl

theorem l2Data_zero_coefficient :
    (l2Data data (0, 0) 0).coefficient = data.coefficient := by
  funext output input
  exact momentCoefficient_zero data output input

end Grad.RepresentedKernel
