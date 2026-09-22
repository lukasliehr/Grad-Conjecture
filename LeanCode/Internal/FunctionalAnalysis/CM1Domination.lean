import CM1Majorants

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

def derivativePairCoefficient (output input : ℤ) (pair : (ℤ × (Outer × Inner)) × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  (coefficientDerivative outerIndex (outer.coefficient output pair.1.1) (pair.1.2.1, pair.2)).comp
    (coefficientDerivative innerIndex (inner.coefficient pair.1.1 input)
      (pair.1.2.2, outer.orthogonal pair.1.2.1 pair.2))

theorem fixed_derivative_pair_domination (width : ℝ → ℝ)
    (outerEnvelope : outer.envelope = radialEnvelope width)
    (innerEnvelope : inner.envelope = radialEnvelope width)
    (widthNonnegative : ∀ point ∈ domain, 0 ≤ width ‖point‖)
    (moment : ℕ) (output middle input : ℤ) :
    ∀ᵐ pair ∂(outerMeasure.prod innerMeasure).prod (volume.restrict domain),
      ‖derivativePairCoefficient outer inner outerIndex innerIndex output input ((middle, pair.1), pair.2)‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment * radialEnvelope width output input pair.2 ≤
          parameterMajorant outer inner outerIndex innerIndex moment output input (middle, pair.1) := by
  have outerAlmost := (outer_projection_quasi outerMeasure innerMeasure domain).ae
    (ae_all_iff.mpr (fun allocation : ℕ => outer.domination outerIndex allocation output middle))
  have innerAlmost := (shifted_inner_projection_quasi (l2Data outer (0, 0) 0)).ae
    (ae_all_iff.mpr (fun allocation : ℕ => inner.domination innerIndex allocation middle input))
  have pointMembership : ∀ᵐ pair ∂(outerMeasure.prod innerMeasure).prod (volume.restrict domain),
      pair.2 ∈ domain :=
    MeasureTheory.Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem outer.domainOpen.measurableSet)
  filter_upwards [outerAlmost, innerAlmost, pointMembership] with pair outerValues innerValues membership
  simp only [outerEnvelope] at outerValues
  simp only [innerEnvelope] at innerValues
  have estimate := allocated_envelope_comp_bound
    (coefficientDerivative outerIndex (outer.coefficient output middle) (pair.1.1, pair.2))
    (coefficientDerivative innerIndex (inner.coefficient middle input) (pair.1.2, outer.orthogonal pair.1.1 pair.2))
    width output middle input (outer.orthogonal pair.1.1) pair.2 (widthNonnegative pair.2 membership)
    moment (fun allocation => outer.majorant outerIndex allocation output middle pair.1.1)
      (fun allocation => inner.majorant innerIndex allocation middle input pair.1.2)
      (fun allocation _bound => outerValues allocation) (fun allocation _bound => innerValues allocation)
  simpa only [derivativePairCoefficient, parameterMajorant_literal, mul_assoc] using estimate

theorem countable_derivative_pair_domination (width : ℝ → ℝ)
    (outerEnvelope : outer.envelope = radialEnvelope width)
    (innerEnvelope : inner.envelope = radialEnvelope width)
    (widthNonnegative : ∀ point ∈ domain, 0 ≤ width ‖point‖)
    (moment : ℕ) (output input : ℤ) :
    ∀ᵐ pair ∂((Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)).prod (volume.restrict domain),
      ‖derivativePairCoefficient outer inner outerIndex innerIndex output input pair‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment * radialEnvelope width output input pair.2 ≤
          parameterMajorant outer inner outerIndex innerIndex moment output input pair.1 := by
  have family := Countable.count_family_ae ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
    (fun middle pair =>
      ‖derivativePairCoefficient outer inner outerIndex innerIndex output input ((middle, pair.1), pair.2)‖ *
        Grad.CellWeights.cellWeight (output - input) ^ moment * radialEnvelope width output input pair.2 ≤
          parameterMajorant outer inner outerIndex innerIndex moment output input (middle, pair.1))
    (fun middle => fixed_derivative_pair_domination outer inner outerIndex innerIndex width outerEnvelope
      innerEnvelope widthNonnegative moment output middle input)
  exact (measurePreserving_prodAssoc (Measure.count : Measure ℤ) (outerMeasure.prod innerMeasure)
    (volume.restrict domain)).quasiMeasurePreserving.ae family

end Grad.RepresentedKernel.Composition.Moments
