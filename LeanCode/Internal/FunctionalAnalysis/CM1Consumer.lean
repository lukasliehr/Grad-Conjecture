import CM1Domination
import AW1Consumers

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

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem zeroMoment_consumer (output input : ℤ) (parameter : ℤ × (Outer × Inner)) :
    parameterMajorant outer inner outerIndex innerIndex 0 output input parameter =
      outer.majorant outerIndex 0 output parameter.1 parameter.2.1 *
        inner.majorant innerIndex 0 parameter.1 input parameter.2.2 := by
  simp [parameterMajorant_literal]

theorem originalWidth_consumer (sigma gamma scale : ℝ)
    (outerEnvelope : outer.envelope = Grad.AnalyticWeights.envelope sigma gamma scale)
    (innerEnvelope : inner.envelope = Grad.AnalyticWeights.envelope sigma gamma scale)
    (widthNonnegative : ∀ point ∈ domain, 0 ≤ Grad.AnalyticWeights.rate sigma gamma (scale * ‖point‖))
    (moment : ℕ) (output input : ℤ) :
    Measurable (parameterMajorant outer inner outerIndex innerIndex moment output input) ∧
    (∀ parameter, 0 ≤ parameterMajorant outer inner outerIndex innerIndex moment output input parameter) ∧
    Integrable (parameterMajorant outer inner outerIndex innerIndex moment output input)
      ((Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ∧
    (∀ᵐ pair ∂((Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)).prod (volume.restrict domain),
      ‖derivativePairCoefficient outer inner outerIndex innerIndex output input pair‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment *
          Grad.AnalyticWeights.envelope sigma gamma scale output input pair.2 ≤
            parameterMajorant outer inner outerIndex innerIndex moment output input pair.1) :=
  ⟨parameterMajorant_measurable outer inner outerIndex innerIndex moment output input,
    parameterMajorant_nonnegative outer inner outerIndex innerIndex moment output input,
    parameterMajorant_integrable outer inner outerIndex innerIndex moment output input,
    countable_derivative_pair_domination outer inner outerIndex innerIndex
      (fun radius => Grad.AnalyticWeights.rate sigma gamma (scale * radius))
      outerEnvelope innerEnvelope widthNonnegative moment output input⟩

theorem rowColumn_consumer (moment : ℕ) :
    (∀ output, Summable (fun input : ℤ => ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure))) ∧
    (∀ input, Summable (fun output : ℤ => ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure))) ∧
    (∀ output, (∑' input : ℤ, ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ≤
      allocatedBound moment (outer.rowBound outerIndex) (inner.rowBound innerIndex)) ∧
    (∀ input, (∑' output : ℤ, ∫ parameter,
      parameterMajorant outer inner outerIndex innerIndex moment output input parameter
        ∂(Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) ≤
      allocatedBound moment (outer.columnBound outerIndex) (inner.columnBound innerIndex)) :=
  ⟨fun output => (parameterMajorant_rows outer inner outerIndex innerIndex moment output).1,
    fun input => (parameterMajorant_columns outer inner outerIndex innerIndex moment input).1,
    fun output => (parameterMajorant_rows outer inner outerIndex innerIndex moment output).2,
    fun input => (parameterMajorant_columns outer inner outerIndex innerIndex moment input).2⟩

end Grad.RepresentedKernel.Composition.Moments
