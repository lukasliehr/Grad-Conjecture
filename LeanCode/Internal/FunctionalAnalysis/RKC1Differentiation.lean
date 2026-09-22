import RKC1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel.Composition.Spatial

theorem allocations : AllocationGoal := by
  intro multiindex selected target
  have outerCount := count_total selected.card (subword (canonicalWord multiindex) selected)
  have innerCount := count_total (selectedᶜ).card target
  have complementary := Finset.card_add_card_compl selected
  simp only [Fintype.card_fin] at complementary
  change (outerIndex multiindex selected).1 + (outerIndex multiindex selected).2 = selected.card at outerCount
  change (wordIndex target).1 + (wordIndex target).2 = (selectedᶜ).card at innerCount
  constructor
  · omega
  · intro moment allocation bounded
    omega

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : RawKernelData outerMeasure middleDimension outputDimension domain)
  (inner : RawKernelData innerMeasure inputDimension middleDimension domain)

theorem orthogonal_entry_measurable (direction coordinate : Fin 2) :
    Measurable (fun parameter => outer.orthogonal parameter (spatialDirection direction) coordinate) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) coordinate).measurable.comp
    (outer.actionMeasurable.comp (measurable_id.prodMk measurable_const))

theorem orthogonal_entry_bound (parameter : Outer) (direction coordinate : Fin 2) :
    |outer.orthogonal parameter (spatialDirection direction) coordinate| ≤ 1 := by
  calc
    _ ≤ ‖outer.orthogonal parameter (spatialDirection direction)‖ :=
      PiLp.norm_apply_le _ _
    _ = ‖spatialDirection direction‖ := (outer.orthogonal parameter).norm_map _
    _ = 1 := by simp [spatialDirection, PiLp.norm_single]

theorem chainFactors : ChainFactorGoal outer := by
  intro rank word target
  simp only [chainFactor_eq]
  constructor
  · exact Finset.measurable_prod _ (fun position _ => orthogonal_entry_measurable outer _ _)
  · intro parameter
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun position _ => orthogonal_entry_bound outer parameter _ _)

theorem derivatives : DerivativeGoal outer inner := by
  constructor
  · intro output input parameter
    exact (rawData Outer Inner outerMeasure innerMeasure inputDimension middleDimension outputDimension
      domain outer inner output input parameter).1
  · intro multiindex output input pair inside
    change wordDerivative _ (canonicalWord multiindex)
      (composedCoefficient outer.orthogonal outer.coefficient inner.coefficient output input pair.1) pair.2 = _
    rw [raw_expanded outer inner output pair.1.1 input pair.1.2.1 pair.1.2.2
      _ (canonicalWord multiindex) pair.2 inside]
    apply Finset.sum_congr rfl
    intro selected _
    apply Finset.sum_congr rfl
    intro target _
    rw [coefficient_word_canonical outer.domainOpen _ _ (outer.coefficientSmooth _ _ _) _ _ _ inside,
      coefficient_word_canonical inner.domainOpen _ _ (inner.coefficientSmooth _ _ _) _ _ _
        ((outer.invariant pair.1.2.1 pair.2).mpr inside)]
    rfl

variable [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]

set_option maxHeartbeats 800000 in
theorem derivativePair_measurable (outerIndex innerIndex : ℕ × ℕ) (output input : ℤ) :
    AEStronglyMeasurable (Moments.derivativePairCoefficient outer inner outerIndex innerIndex output input)
      ((parameterMeasure outerMeasure innerMeasure).prod (volume.restrict domain)) := by
  have each (middle : ℤ) : AEStronglyMeasurable
      (fun pair : (Outer × Inner) × Spatial =>
        Moments.derivativePairCoefficient outer inner outerIndex innerIndex output input ((middle, pair.1), pair.2))
      ((outerMeasure.prod innerMeasure).prod (volume.restrict domain)) :=
    (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
      (((outer.derivativeMeasurable outerIndex output middle).comp_quasiMeasurePreserving
        (outer_projection_quasi outerMeasure innerMeasure domain)).prodMk
        ((inner.derivativeMeasurable innerIndex middle input).comp_quasiMeasurePreserving
          (shifted_inner_projection_quasi (l2Data outer (0, 0) 0))))
  exact (Countable.count_family_aestronglyMeasurable
    ((outerMeasure.prod innerMeasure).prod (volume.restrict domain)) _ each).comp_quasiMeasurePreserving
      (measurePreserving_prodAssoc (Measure.count : Measure ℤ) (outerMeasure.prod innerMeasure)
        (volume.restrict domain)).quasiMeasurePreserving

theorem derivativeTerm_measurable (multiindex : ℕ × ℕ)
    (selected : Finset (Fin (multiindex.1 + multiindex.2))) (target : Word (selectedᶜ).card)
    (output input : ℤ) :
    AEStronglyMeasurable (derivativeTerm outer inner multiindex selected target output input)
      ((parameterMeasure outerMeasure innerMeasure).prod (volume.restrict domain)) :=
  (((chainFactors outer _ _ target).1.comp measurable_fst.snd.fst).aestronglyMeasurable).smul
    (derivativePair_measurable outer inner _ _ output input)

theorem derivatives_measurable : DerivativeMeasurableGoal outer inner := by
  intro multiindex output input
  have finiteSum : AEStronglyMeasurable
      (fun pair => ∑ selected : Finset (Fin (multiindex.1 + multiindex.2)),
        ∑ target : Word (selectedᶜ).card, derivativeTerm outer inner multiindex selected target output input pair)
      ((parameterMeasure outerMeasure innerMeasure).prod (volume.restrict domain)) := by
    simpa only [Finset.sum_fn] using
      Finset.aestronglyMeasurable_sum Finset.univ (fun selected _ =>
        Finset.aestronglyMeasurable_sum Finset.univ (fun target _ =>
          derivativeTerm_measurable outer inner multiindex selected target output input))
  apply finiteSum.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem outer.domainOpen.measurableSet)] with pair inside
  exact ((derivatives outer inner).2 multiindex output input pair inside).symm

end Grad.RepresentedKernel.Composition.Spatial
