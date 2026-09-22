import CM1Summability

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators

namespace Grad.RepresentedKernel.Composition.Moments

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
  (inner : RawKernelData innerMeasure inputDimension middleDimension domain)
  (outerIndex innerIndex : ℕ × ℕ)

def parameterMajorant (moment : ℕ) (output input : ℤ) (parameter : ℤ × (Outer × Inner)) : ℝ :=
  ∑ allocation ∈ Finset.range (moment + 1), (moment.choose allocation : ℝ) *
    Countable.countWeight (l2Data outer outerIndex allocation)
      (l2Data inner innerIndex (moment - allocation)) output input parameter

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem parameterMajorant_literal (moment : ℕ) (output input : ℤ) (parameter : ℤ × (Outer × Inner)) :
    parameterMajorant outer inner outerIndex innerIndex moment output input parameter =
      ∑ allocation ∈ Finset.range (moment + 1), (moment.choose allocation : ℝ) *
        (outer.majorant outerIndex allocation output parameter.1 parameter.2.1 *
          inner.majorant innerIndex (moment - allocation) parameter.1 input parameter.2.2) := rfl

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem parameterMajorant_nonnegative (moment : ℕ) (output input : ℤ) (parameter : ℤ × (Outer × Inner)) :
    0 ≤ parameterMajorant outer inner outerIndex innerIndex moment output input parameter :=
  Finset.sum_nonneg (fun allocation _membership => mul_nonneg (Nat.cast_nonneg _)
    (Countable.countWeight_nonnegative (l2Data outer outerIndex allocation)
      (l2Data inner innerIndex (moment - allocation)) output input parameter))

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem parameterMajorant_measurable (moment : ℕ) (output input : ℤ) :
    Measurable (parameterMajorant outer inner outerIndex innerIndex moment output input) :=
  Finset.measurable_sum _ (fun allocation _membership => measurable_const.mul
    (Countable.countWeight_measurable (l2Data outer outerIndex allocation)
      (l2Data inner innerIndex (moment - allocation)) output input))

theorem parameterMajorant_integrable (moment : ℕ) (output input : ℤ) :
    Integrable (parameterMajorant outer inner outerIndex innerIndex moment output input)
      ((Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) :=
  integrable_finsetSum _ (fun allocation _membership =>
    (Countable.countWeight_integrable (l2Data outer outerIndex allocation)
      (l2Data inner innerIndex (moment - allocation)) output input).const_mul _)

theorem parameterMajorant_integral (moment : ℕ) (output input : ℤ) :
    (∫ parameter, parameterMajorant outer inner outerIndex innerIndex moment output input parameter
      ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) =
      allocatedWeight moment
        (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data outer outerIndex allocation))
        (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data inner innerIndex allocation)) output input := by
  unfold parameterMajorant
  rw [integral_finsetSum _ (fun allocation _membership =>
    (Countable.countWeight_integrable (l2Data outer outerIndex allocation)
      (l2Data inner innerIndex (moment - allocation)) output input).const_mul _)]
  simp only [integral_const_mul, Countable.countWeight_integral, allocatedWeight,
    Countable.combinedWeight, Countable.middleWeight]

theorem parameterMajorant_rows (moment : ℕ) (output : ℤ) :
    Summable (fun input : ℤ => ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ∧
    (∑' input : ℤ, ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ≤
      allocatedBound moment (outer.rowBound outerIndex) (inner.rowBound innerIndex) := by
  simp only [parameterMajorant_integral]
  exact allocated_rows moment
    (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data outer outerIndex allocation))
    (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data inner innerIndex allocation))
    (outer.rowBound outerIndex) (inner.rowBound innerIndex)
    (fun allocation => Grad.FullCellKernel.integratedWeight_nonneg (l2Data outer outerIndex allocation))
    (fun allocation => Grad.FullCellKernel.integratedWeight_nonneg (l2Data inner innerIndex allocation))
    (outer.rowsSummable outerIndex) (inner.rowsSummable innerIndex)
    (outer.rows outerIndex) (inner.rows innerIndex) (inner.rowNonnegative innerIndex) output

theorem parameterMajorant_columns (moment : ℕ) (input : ℤ) :
    Summable (fun output : ℤ => ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ∧
    (∑' output : ℤ, ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ≤
      allocatedBound moment (outer.columnBound outerIndex) (inner.columnBound innerIndex) := by
  simp only [parameterMajorant_integral]
  exact allocated_columns moment
    (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data outer outerIndex allocation))
    (fun allocation => Grad.FullCellKernel.integratedWeight (l2Data inner innerIndex allocation))
    (outer.columnBound outerIndex) (inner.columnBound innerIndex)
    (fun allocation => Grad.FullCellKernel.integratedWeight_nonneg (l2Data outer outerIndex allocation))
    (fun allocation => Grad.FullCellKernel.integratedWeight_nonneg (l2Data inner innerIndex allocation))
    (outer.columnsSummable outerIndex) (inner.columnsSummable innerIndex)
    (outer.columns outerIndex) (inner.columns innerIndex) (outer.columnNonnegative outerIndex) input

end Grad.RepresentedKernel.Composition.Moments
