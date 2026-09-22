import AKAA19FirstOrderAllocation

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel
open Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered

theorem startupFirst_candidate {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order weight : ℕ}
    (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (reference : Parameter) (identity : ∀ parameter, data.orthogonal parameter = LinearIsometryEquiv.refl ℝ _)
    (direction : Fin 2) (bound : 1 ≤ order)
    (field : Grad.WeightedJets.GraphGrade inputDimension order weight openUnitDisk) :
    (∑ selected : Finset (Fin 1), ∑ target : Word selectedᶜ.card,
      operator (allocatedData data (startupFirstWord direction) selected target) (0, 0) 0
        (inputDerivative inputDimension order 1 weight openUnitDisk bound field selected target)) =
      operator data (0, 0) 0
        (orderedDerivative inputDimension order 1 openUnitDisk (fun _ => weight) bound field (startupFirstWord direction)) +
      operator data (startupFirstIndex direction) 0
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field) := by
  have constant : ∀ parameter, data.orthogonal parameter = data.orthogonal reference :=
    fun parameter => (identity parameter).trans (identity reference).symm
  simp_rw [startupAllocated_operator data reference constant]
  change (∑ selected : Finset (Fin 1), ∑ target : Word selectedᶜ.card,
    (chainProduct data (startupFirstWord direction) selected target reference : ℂ) •
      operator data (selectedIndex (startupFirstWord direction) selected) 0
        (inputDerivative inputDimension order 1 weight openUnitDisk bound field selected target)) = _
  have enumeration : (Finset.univ : Finset (Finset (Fin 1))) = {∅, Finset.univ} := by decide
  rw [enumeration, Finset.sum_pair (by decide : (∅ : Finset (Fin 1)) ≠ Finset.univ)]
  congr 1
  · simp_rw [startupFirst_chain_empty data direction _ reference (identity reference), startupFirst_selected_empty]
    rw [Fintype.sum_eq_single (fun _ => direction)]
    · rw [if_pos rfl, Complex.ofReal_one, one_smul]
      rfl
    · intro target different
      rw [if_neg different, Complex.ofReal_zero, zero_smul]
  · simp_rw [startupFirst_chain_univ, Complex.ofReal_one, one_smul, startupFirst_selected_univ]
    have empty : ((Finset.univ : Finset (Fin 1))ᶜ).card = 0 := by decide
    let uniqueTarget : Unique (Word ((Finset.univ : Finset (Fin 1))ᶜ).card) := {
      default := fun position => Fin.elim0 (Fin.cast empty position)
      uniq target := by funext position; exact Fin.elim0 (Fin.cast empty position) }
    let _ := uniqueTarget
    rw [Fintype.sum_unique]
    change operator data (startupFirstIndex direction) 0
      (orderedDerivative inputDimension order 0 openUnitDisk (fun _ => weight) (Nat.zero_le order) field default) = _
    rw [orderedDerivative_zero]

theorem startupSingleEntry_firstWeak {inputDimension outputDimension order weight : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell : ℤ)
    (direction : Fin 2) (bound : 1 ≤ order)
    (field : Grad.WeightedJets.GraphGrade inputDimension order weight openUnitDisk) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension openUnitDisk 1 (startupFirstWord direction)
      (operator (startupSingleEntryData jet outputCell inputCell) (0, 0) 0
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field))
      (operator (startupSingleEntryData jet outputCell inputCell) (0, 0) 0
        (orderedDerivative inputDimension order 1 openUnitDisk (fun _ => weight) bound field (startupFirstWord direction)) +
      operator (startupSingleEntryData jet outputCell inputCell) (startupFirstIndex direction) 0
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field)) := by
  have weak := startupSingleEntry_weak jet outputCell inputCell (startupFirstWord direction) bound field
  rw [startupFirst_candidate (startupSingleEntryData jet outputCell inputCell) (0 : ℝ) (fun _ => rfl)] at weak
  exact weak

end Grad.CartesianStartup
