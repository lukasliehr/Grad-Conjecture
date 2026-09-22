import RKWD1Interface
import RKC1Differentiation
import SM1Calculus

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

universe parameterUniverse valueUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

theorem chainProducts : ChainProductGoal.{parameterUniverse} := by
  intro Parameter _ measure inputDimension outputDimension rank domain data word selected target
  exact Grad.RepresentedKernel.Composition.Spatial.chainFactors data
    (selectedᶜ).card (subword word selectedᶜ) target

theorem allocationIndices : AllocationIndexGoal := by
  intro rank word selected
  exact Grad.RepresentedKernel.SpatialProduct.count_total selected.card (subword word selected)

theorem listDerivative_append {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (first second : List (Fin 2)) (function : Spatial → Value) :
    Grad.RepresentedKernel.SpatialProduct.listDerivative (first ++ second) function =
      Grad.RepresentedKernel.SpatialProduct.listDerivative first
        (Grad.RepresentedKernel.SpatialProduct.listDerivative second function) := by
  simp only [Grad.RepresentedKernel.SpatialProduct.listDerivative, List.foldr_append]

theorem coefficientDerivative_smooth {Parameter : Type parameterUniverse}
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (openDomain : IsOpen domain)
    (coefficient : Parameter × Spatial →
      PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (smooth : ∀ parameter, ContDiffOn ℝ ∞ (fun point => coefficient (parameter, point)) domain)
    (multiindex : ℕ × ℕ) (parameter : Parameter) :
    ContDiffOn ℝ ∞ (fun point => coefficientDerivative multiindex coefficient (parameter, point)) domain := by
  let word := Grad.WeakTesting.Commutation.canonicalWord multiindex.1 multiindex.2
  have listSmooth := Grad.RepresentedKernel.SpatialProduct.listDerivative_smooth openDomain
    (List.ofFn word) (smooth parameter)
  apply listSmooth.congr
  intro point inside
  exact (Grad.RepresentedKernel.SpatialProduct.listDerivative_ofFn openDomain _ word
    (smooth parameter) inside).symm

theorem coefficientDerivative_comp {Parameter : Type parameterUniverse}
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (openDomain : IsOpen domain)
    (coefficient : Parameter × Spatial →
      PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (smooth : ∀ parameter, ContDiffOn ℝ ∞ (fun point => coefficient (parameter, point)) domain)
    (first second : ℕ × ℕ) (pair : Parameter × Spatial) (inside : pair.2 ∈ domain) :
    coefficientDerivative first
        (fun pair => coefficientDerivative second coefficient (pair.1, pair.2)) pair =
      coefficientDerivative (indexAdd first second) coefficient pair := by
  let firstWord := Grad.WeakTesting.Commutation.canonicalWord first.1 first.2
  let secondWord := Grad.WeakTesting.Commutation.canonicalWord second.1 second.2
  let totalWord := Grad.WeakTesting.Commutation.canonicalWord
    (first.1 + second.1) (first.2 + second.2)
  let function := fun point => coefficient (pair.1, point)
  have functionSmooth : ContDiffOn ℝ ∞ function domain := smooth pair.1
  have secondSmooth : ContDiffOn ℝ ∞
      (Grad.RepresentedKernel.SpatialProduct.wordDerivative (second.1 + second.2)
        secondWord function) domain := by
    have listSmooth := Grad.RepresentedKernel.SpatialProduct.listDerivative_smooth openDomain
      (List.ofFn secondWord) functionSmooth
    exact listSmooth.congr (fun point membership =>
      (Grad.RepresentedKernel.SpatialProduct.listDerivative_ofFn openDomain _ secondWord
        functionSmooth membership).symm)
  change Grad.RepresentedKernel.SpatialProduct.wordDerivative (first.1 + first.2) firstWord
      (Grad.RepresentedKernel.SpatialProduct.wordDerivative (second.1 + second.2)
        secondWord function) pair.2 =
    Grad.RepresentedKernel.SpatialProduct.wordDerivative
      ((first.1 + second.1) + (first.2 + second.2)) totalWord function pair.2
  have secondLocal :
      Grad.RepresentedKernel.SpatialProduct.wordDerivative (second.1 + second.2)
        secondWord function =ᶠ[𝓝 pair.2]
      Grad.RepresentedKernel.SpatialProduct.listDerivative (List.ofFn secondWord) function :=
    Filter.eventually_of_mem (openDomain.mem_nhds inside) (fun point membership =>
      (Grad.RepresentedKernel.SpatialProduct.listDerivative_ofFn openDomain _ secondWord
        functionSmooth membership).symm)
  have replacement := congrArg
    (fun derivative : ContinuousMultilinearMap ℝ
        (fun _ : Fin (first.1 + first.2) => Spatial)
        (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) =>
      derivative (fun position => spatialDirection (firstWord position)))
    ((secondLocal.iteratedFDeriv ℝ (first.1 + first.2)).self_of_nhds)
  change Grad.RepresentedKernel.SpatialProduct.wordDerivative (first.1 + first.2) firstWord
      (Grad.RepresentedKernel.SpatialProduct.wordDerivative (second.1 + second.2)
        secondWord function) pair.2 =
    Grad.RepresentedKernel.SpatialProduct.wordDerivative (first.1 + first.2) firstWord
      (Grad.RepresentedKernel.SpatialProduct.listDerivative (List.ofFn secondWord) function) pair.2
    at replacement
  rw [replacement]
  rw [← Grad.RepresentedKernel.SpatialProduct.listDerivative_ofFn openDomain _ firstWord
      (Grad.RepresentedKernel.SpatialProduct.listDerivative_smooth openDomain
        (List.ofFn secondWord) functionSmooth) inside]
  rw [← listDerivative_append]
  rw [← Grad.RepresentedKernel.SpatialProduct.listDerivative_ofFn openDomain _ totalWord
      functionSmooth inside]
  apply Grad.RepresentedKernel.SpatialProduct.listDerivative_perm openDomain _ functionSmooth inside
  rw [Grad.WeightedJets.SpatialMultiplier.canonical_list,
    Grad.WeightedJets.SpatialMultiplier.canonical_list,
    Grad.WeightedJets.SpatialMultiplier.canonical_list]
  apply List.perm_iff_count.mpr
  intro direction
  simp only [List.count_append, List.count_replicate]
  split_ifs <;> omega

variable {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
  {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
  (data : RawKernelData measure inputDimension outputDimension domain)

theorem allocatedCoefficient_smooth {rank : ℕ} (word : Word rank)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card) (output input : ℤ)
    (parameter : Parameter) :
    ContDiffOn ℝ ∞
      (fun point => allocatedCoefficient data word selected target output input (parameter, point)) domain := by
  exact (coefficientDerivative_smooth data.domainOpen (data.coefficient output input)
    (data.coefficientSmooth output input) (selectedIndex word selected) parameter).const_smul
      (chainProduct data word selected target parameter : ℂ)

theorem allocatedCoefficient_derivative {rank : ℕ} (word : Word rank)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card)
    (multiindex : ℕ × ℕ) (output input : ℤ) (pair : Parameter × Spatial)
    (inside : pair.2 ∈ domain) :
    coefficientDerivative multiindex (allocatedCoefficient data word selected target output input) pair =
      (chainProduct data word selected target pair.1 : ℂ) •
        coefficientDerivative (indexAdd multiindex (selectedIndex word selected))
          (data.coefficient output input) pair := by
  let derivative := fun point => coefficientDerivative (selectedIndex word selected)
    (data.coefficient output input) (pair.1, point)
  have derivativeSmooth : ContDiffAt ℝ ∞ derivative pair.2 :=
    (coefficientDerivative_smooth data.domainOpen (data.coefficient output input)
      (data.coefficientSmooth output input) (selectedIndex word selected) pair.1).contDiffAt
        (data.domainOpen.mem_nhds inside)
  change iteratedFDeriv ℝ (multiindex.1 + multiindex.2)
      (fun point => (chainProduct data word selected target pair.1 : ℂ) • derivative point) pair.2 _ = _
  rw [iteratedFDeriv_const_smul_apply'
    (derivativeSmooth.of_le (by exact_mod_cast le_top))]
  simp only [smul_apply]
  congr 1
  exact coefficientDerivative_comp data.domainOpen (data.coefficient output input)
    (data.coefficientSmooth output input) multiindex (selectedIndex word selected) pair inside

theorem allocatedCoefficient_measurable {rank : ℕ} (word : Word rank)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card)
    (multiindex : ℕ × ℕ) (output input : ℤ) :
    AEStronglyMeasurable
      (coefficientDerivative multiindex (allocatedCoefficient data word selected target output input))
      (measure.prod (volume.restrict domain)) := by
  have productMeasurable : AEStronglyMeasurable (fun pair : Parameter × Spatial =>
      (chainProduct data word selected target pair.1 : ℂ) •
        coefficientDerivative (indexAdd multiindex (selectedIndex word selected))
          (data.coefficient output input) pair)
      (measure.prod (volume.restrict domain)) :=
    by
      have chainMeasurable : Measurable (fun pair : Parameter × Spatial =>
          (chainProduct data word selected target pair.1 : ℂ)) :=
        by
          have rawMeasurable :=
            (chainProducts Parameter measure inputDimension outputDimension rank domain data word selected target).1
          exact Complex.continuous_ofReal.measurable.comp (rawMeasurable.comp measurable_fst)
      exact chainMeasurable.aestronglyMeasurable.smul
        (data.derivativeMeasurable (indexAdd multiindex (selectedIndex word selected)) output input)
  apply productMeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem data.domainOpen.measurableSet)] with pair inside
  exact (allocatedCoefficient_derivative data word selected target multiindex output input pair inside).symm

def allocatedData {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank))
    (target : Word (selectedᶜ).card) :
    RawKernelData measure inputDimension outputDimension domain where
  domainOpen := data.domainOpen
  orthogonal := data.orthogonal
  invariant := data.invariant
  actionMeasurable := data.actionMeasurable
  coefficient := allocatedCoefficient data word selected target
  coefficientSmooth := allocatedCoefficient_smooth data word selected target
  derivativeMeasurable := allocatedCoefficient_measurable data word selected target
  envelope := data.envelope
  envelopeOneLe := data.envelopeOneLe
  majorant := allocatedMajorant data word selected
  majorantMeasurable := fun multiindex =>
    data.majorantMeasurable (indexAdd multiindex (selectedIndex word selected))
  majorantNonnegative := fun multiindex =>
    data.majorantNonnegative (indexAdd multiindex (selectedIndex word selected))
  majorantIntegrable := fun multiindex =>
    data.majorantIntegrable (indexAdd multiindex (selectedIndex word selected))
  domination := fun multiindex moment output input => by
    filter_upwards [data.domination (indexAdd multiindex (selectedIndex word selected)) moment output input,
      data.envelopeOneLe output input,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem data.domainOpen.measurableSet)]
      with pair dominated envelope inside
    rw [allocatedCoefficient_derivative data word selected target multiindex output input pair inside,
      norm_smul, Complex.norm_real]
    calc
      |chainProduct data word selected target pair.1| *
          ‖coefficientDerivative (indexAdd multiindex (selectedIndex word selected))
            (data.coefficient output input) pair‖ *
          Grad.CellWeights.cellWeight (output - input) ^ moment * data.envelope output input pair.2 =
        |chainProduct data word selected target pair.1| *
          (‖coefficientDerivative (indexAdd multiindex (selectedIndex word selected))
            (data.coefficient output input) pair‖ *
          Grad.CellWeights.cellWeight (output - input) ^ moment * data.envelope output input pair.2) := by ring
      _ ≤ 1 * (‖coefficientDerivative (indexAdd multiindex (selectedIndex word selected))
            (data.coefficient output input) pair‖ *
          Grad.CellWeights.cellWeight (output - input) ^ moment * data.envelope output input pair.2) := by
        apply mul_le_mul_of_nonneg_right
          ((chainProducts Parameter measure inputDimension outputDimension rank domain data word selected target).2 pair.1)
        exact mul_nonneg (mul_nonneg (norm_nonneg _)
          (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _))
            (zero_le_one.trans envelope)
      _ ≤ data.majorant (indexAdd multiindex (selectedIndex word selected)) moment output input pair.1 := by
        simpa only [one_mul] using dominated
  rowBound := allocatedRowBound data word selected
  columnBound := allocatedColumnBound data word selected
  rowNonnegative := fun multiindex =>
    data.rowNonnegative (indexAdd multiindex (selectedIndex word selected))
  columnNonnegative := fun multiindex =>
    data.columnNonnegative (indexAdd multiindex (selectedIndex word selected))
  rowsSummable := fun multiindex =>
    data.rowsSummable (indexAdd multiindex (selectedIndex word selected))
  columnsSummable := fun multiindex =>
    data.columnsSummable (indexAdd multiindex (selectedIndex word selected))
  rows := fun multiindex => data.rows (indexAdd multiindex (selectedIndex word selected))
  columns := fun multiindex => data.columns (indexAdd multiindex (selectedIndex word selected))

theorem allocatedData_specification {rank : ℕ} (word : Word rank)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card) :
    AllocationSpecification data word selected target (allocatedData data word selected target) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem allocationData : AllocationDataGoal.{parameterUniverse} := by
  intro Parameter _ measure inputDimension outputDimension rank domain data word selected target
  exact ⟨allocatedData data word selected target,
    allocatedData_specification data word selected target⟩

theorem allocationCLM : AllocationCLMGoal.{parameterUniverse} := by
  intro Parameter _ measure _ inputDimension outputDimension rank domain data word family specification
    selected target multiindex moment
  have bound := operator_norm_le (family selected target) multiindex moment
  rw [(specification selected target).2.2.2.2.1,
    (specification selected target).2.2.2.2.2] at bound
  exact bound

end Grad.RepresentedKernel.WeakDerivatives
