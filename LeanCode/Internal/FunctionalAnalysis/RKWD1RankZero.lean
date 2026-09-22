import RKWD1Interface
import OJConsumer

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open Grad.SpatialDilation (disk)
open scoped BigOperators ContDiff Topology

universe parameterUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

theorem selectedIndex_zero (word : Word 0) (selected : Finset (Fin 0)) :
    selectedIndex word selected = (0, 0) := by
  have selectedCard : selected.card = 0 := by
    rw [show selected = ∅ from Subsingleton.elim _ _]
    rfl
  have total := Grad.RepresentedKernel.SpatialProduct.count_total selected.card (subword word selected)
  apply Prod.ext <;> dsimp [selectedIndex] <;> omega

theorem chainProduct_zero {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word 0) (selected : Finset (Fin 0)) (target : Word (selectedᶜ).card)
    (parameter : Parameter) : chainProduct data word selected target parameter = 1 := by
  have complementCard : selectedᶜ.card = 0 := by
    rw [show selectedᶜ = ∅ from Subsingleton.elim _ _]
    rfl
  rw [chainProduct, Grad.RepresentedKernel.SpatialProduct.chainFactor_eq]
  apply Fintype.prod_eq_one
  intro position
  exact Fin.elim0 (Fin.cast complementCard position)

theorem allocatedCoefficient_zero {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word 0) (selected : Finset (Fin 0)) (target : Word (selectedᶜ).card) :
    allocatedCoefficient data word selected target = data.coefficient := by
  funext output input pair
  rw [allocatedCoefficient, selectedIndex_zero word selected,
    chainProduct_zero data word selected target pair.1]
  simp only [Complex.ofReal_one, one_smul, Grad.RepresentedKernel.coefficientDerivative_zero]

theorem allocatedMajorant_zero {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word 0) (selected : Finset (Fin 0)) :
    allocatedMajorant data word selected = data.majorant := by
  funext multiindex
  change data.majorant (indexAdd multiindex (selectedIndex word selected)) = data.majorant multiindex
  rw [selectedIndex_zero word selected]
  rfl

theorem allocatedRowBound_zero {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word 0) (selected : Finset (Fin 0)) :
    allocatedRowBound data word selected = data.rowBound := by
  funext multiindex
  change data.rowBound (indexAdd multiindex (selectedIndex word selected)) = data.rowBound multiindex
  rw [selectedIndex_zero word selected]
  rfl

theorem allocatedColumnBound_zero {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (word : Word 0) (selected : Finset (Fin 0)) :
    allocatedColumnBound data word selected = data.columnBound := by
  funext multiindex
  change data.columnBound (indexAdd multiindex (selectedIndex word selected)) = data.columnBound multiindex
  rw [selectedIndex_zero word selected]
  rfl

theorem allocationSpecification_zero_eq {Parameter : Type parameterUniverse}
    [MeasurableSpace Parameter] {measure : Measure Parameter}
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data allocated : RawKernelData measure inputDimension outputDimension domain)
    (word : Word 0) (selected : Finset (Fin 0)) (target : Word (selectedᶜ).card)
    (specification : AllocationSpecification data word selected target allocated) :
    allocated = data := by
  rcases specification with ⟨orthogonal, coefficient, envelope, majorant, rowBound, columnBound⟩
  rw [allocatedCoefficient_zero data word selected target] at coefficient
  rw [allocatedMajorant_zero data word selected] at majorant
  rw [allocatedRowBound_zero data word selected] at rowBound
  rw [allocatedColumnBound_zero data word selected] at columnBound
  cases data
  cases allocated
  simp_all only

set_option linter.style.haveILetI false in
theorem rankZero : RankZeroGoal.{parameterUniverse} := by
  intro Parameter _ measure _ inputDimension outputDimension order weight radius data word family specification jet
  have complementCard : (default : Finset (Fin 0))ᶜ.card = 0 := by
    rw [show (default : Finset (Fin 0))ᶜ = ∅ from Subsingleton.elim _ _]
    rfl
  let uniqueTarget : Unique (Word (default : Finset (Fin 0))ᶜ.card) := {
    default := fun position => Fin.elim0 (Fin.cast complementCard position)
    uniq target := by
      funext position
      exact Fin.elim0 (Fin.cast complementCard position)
    }
  letI := uniqueTarget
  rw [derivativeCandidate]
  simp_rw [fun selected target => allocationSpecification_zero_eq data
    (family selected target) word selected target (specification selected target)]
  rw [Fintype.sum_unique]
  rw [Fintype.sum_unique]
  exact congrArg (operator data (0, 0) 0)
    (Grad.WeightedJets.Ordered.orderedDerivative_zero inputDimension order (disk radius)
      (fun _ => weight) jet default)

end Grad.RepresentedKernel.WeakDerivatives
