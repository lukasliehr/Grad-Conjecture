import CK2Weights

noncomputable section

open MeasureTheory MeasureTheory.Measure Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology

namespace Grad.RepresentedKernel.Composition.Countable

theorem count_family_ae {Space : Type*} [MeasurableSpace Space] (measure : Measure Space)
    [SigmaFinite measure] (predicate : ℤ → Space → Prop) (almost : ∀ index, ∀ᵐ point ∂measure, predicate index point) :
    ∀ᵐ pair ∂(Measure.count : Measure ℤ).prod measure, predicate pair.1 pair.2 := by
  filter_upwards [quasiMeasurePreserving_snd.ae (ae_all_iff.mpr almost)] with pair allIndices
  exact allIndices pair.1

theorem count_family_aestronglyMeasurable {Space Value : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup Value] (measure : Measure Space) [SigmaFinite measure]
    (family : ℤ → Space → Value) (measurability : ∀ index, AEStronglyMeasurable (family index) measure) :
    AEStronglyMeasurable (fun pair : ℤ × Space => family pair.1 pair.2) (Measure.count.prod measure) := by
  let representative : ℤ → Space → Value := fun index => (measurability index).mk (family index)
  have measurableRepresentative : StronglyMeasurable (Function.uncurry representative) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun _ => continuous_of_discreteTopology) (fun index => (measurability index).stronglyMeasurable_mk)
  exact ⟨Function.uncurry representative, measurableRepresentative,
    count_family_ae measure (fun index point => family index point = representative index point)
      (fun index => (measurability index).ae_eq_mk)⟩

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

def countCoefficient (output input : ℤ) (pair : (ℤ × (Outer × Inner)) × Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  pairCoefficient outer inner output pair.1.1 input (pair.1.2, pair.2)

def countWeight (output input : ℤ) (parameter : ℤ × (Outer × Inner)) : ℝ :=
  pairWeight outer inner output parameter.1 input parameter.2

def countOrthogonal (parameter : ℤ × (Outer × Inner)) : Spatial ≃ₗᵢ[ℝ] Spatial :=
  pairOrthogonal outer inner parameter.2

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem countOrthogonal_invariant (parameter : ℤ × (Outer × Inner)) :
    Grad.KernelPullback.Domain.Invariant domain (countOrthogonal outer inner parameter) :=
  pairOrthogonal_invariant outer inner parameter.2

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem count_action_measurable :
    Measurable (fun pair : (ℤ × (Outer × Inner)) × Spatial => countOrthogonal outer inner pair.1 pair.2) :=
  (pair_action_measurable outer inner).comp (measurable_fst.snd.prodMk measurable_snd)

theorem countCoefficient_measurable (output input : ℤ) :
    AEStronglyMeasurable (countCoefficient outer inner output input)
      ((Measure.count.prod (outerMeasure.prod innerMeasure)).prod (volume.restrict domain)) :=
  (count_family_aestronglyMeasurable ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
    (fun middle => pairCoefficient outer inner output middle input)
    (fun middle => pairCoefficient_measurable outer inner output middle input)).comp_quasiMeasurePreserving
      (measurePreserving_prodAssoc (Measure.count : Measure ℤ) (outerMeasure.prod innerMeasure)
        (volume.restrict domain)).quasiMeasurePreserving

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem countWeight_measurable (output input : ℤ) : Measurable (countWeight outer inner output input) :=
  measurable_from_prod_countable_right (fun middle => pairWeight_measurable outer inner output middle input)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem countWeight_nonnegative (output input : ℤ) (parameter : ℤ × (Outer × Inner)) :
    0 ≤ countWeight outer inner output input parameter :=
  pairWeight_nonnegative outer inner output parameter.1 input parameter.2

theorem pairWeight_norm_integral (output middle input : ℤ) :
    (∫ parameter, ‖pairWeight outer inner output middle input parameter‖ ∂outerMeasure.prod innerMeasure) =
      middleWeight outer inner output input middle := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (pairWeight_nonnegative outer inner output middle input _)]
  exact pairWeight_integral outer inner output middle input

theorem countWeight_integrable (output input : ℤ) :
    Integrable (countWeight outer inner output input) (Measure.count.prod (outerMeasure.prod innerMeasure)) := by
  apply (integrable_prod_iff (countWeight_measurable outer inner output input).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun middle => pairWeight_integrable outer inner output middle input), ?_⟩
  change Integrable (fun middle : ℤ => ∫ parameter,
    ‖pairWeight outer inner output middle input parameter‖ ∂outerMeasure.prod innerMeasure) Measure.count
  simp_rw [pairWeight_norm_integral]
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg (middleWeight_nonnegative outer inner output input _)] using
    middleWeight_summable outer inner output input

theorem countWeight_integral (output input : ℤ) :
    (∫ parameter, countWeight outer inner output input parameter
      ∂Measure.count.prod (outerMeasure.prod innerMeasure)) = combinedWeight outer inner output input := by
  rw [integral_prod _ (countWeight_integrable outer inner output input),
    integral_countable (countWeight_integrable outer inner output input).integral_prod_left]
  change (∑' middle : ℤ, (Measure.count : Measure ℤ).real {middle} •
    ∫ parameter, pairWeight outer inner output middle input parameter ∂outerMeasure.prod innerMeasure) = _
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    pairWeight_integral, combinedWeight, middleWeight, Grad.FullCellKernel.integratedWeight]

theorem countCoefficient_domination (output input : ℤ) :
    ∀ᵐ pair ∂(Measure.count.prod (outerMeasure.prod innerMeasure)).prod (volume.restrict domain),
      ‖countCoefficient outer inner output input pair‖ ≤ countWeight outer inner output input pair.1 :=
  (measurePreserving_prodAssoc (Measure.count : Measure ℤ) (outerMeasure.prod innerMeasure)
    (volume.restrict domain)).quasiMeasurePreserving.ae
      (count_family_ae ((outerMeasure.prod innerMeasure).prod (volume.restrict domain))
        (fun middle pair => ‖pairCoefficient outer inner output middle input pair‖ ≤
          pairWeight outer inner output middle input pair.1)
        (fun middle => pairCoefficient_domination outer inner output middle input))

def composedData : Grad.FullCellKernel.L2KernelData
    ((Measure.count : Measure ℤ).prod (outerMeasure.prod innerMeasure)) inputDimension outputDimension domain where
  domainMeasurable := outer.domainMeasurable
  orthogonal := countOrthogonal outer inner
  invariant := countOrthogonal_invariant outer inner
  actionMeasurable := count_action_measurable outer inner
  coefficient := countCoefficient outer inner
  weight := countWeight outer inner
  coefficientMeasurable := countCoefficient_measurable outer inner
  weightMeasurable := countWeight_measurable outer inner
  weightNonnegative := countWeight_nonnegative outer inner
  weightIntegrable := countWeight_integrable outer inner
  domination := countCoefficient_domination outer inner
  rowBound := outer.rowBound * inner.rowBound
  columnBound := outer.columnBound * inner.columnBound
  rowNonnegative := mul_nonneg outer.rowNonnegative inner.rowNonnegative
  columnNonnegative := mul_nonneg outer.columnNonnegative inner.columnNonnegative
  rowsSummable := fun output => by
    simpa only [countWeight_integral] using (rowProducts_summable outer inner output).2.1
  columnsSummable := fun input => by
    simpa only [countWeight_integral] using (columnProducts_summable outer inner input).1
  rows := fun output => by
    simpa only [countWeight_integral] using (rowProducts_summable outer inner output).2.2
  columns := fun input => by
    simpa only [countWeight_integral] using (columnProducts_summable outer inner input).2

end Grad.RepresentedKernel.Composition.Countable
