import AKAA25FixedOrthogonalWeakKernel

noncomputable section

set_option maxHeartbeats 1700000

open MeasureTheory Classical
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel
open Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct

variable {Parameter : Type*} [MeasurableSpace Parameter] {measure : Measure Parameter}
  [SigmaFinite measure] {inputDimension outputDimension : ℕ}

def startupRawFirstCandidate
    (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (direction : Fin 2) (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    FieldL2 outputDimension openUnitDisk :=
  ∑ selected : Finset (Fin 1), ∑ target : Word selectedᶜ.card,
    operator (allocatedData data (startupFirstWord direction) selected target) (0, 0) 0
      (inputDerivative inputDimension 1 1 0 openUnitDisk le_rfl field selected target)

theorem startupRawFirst_weak
    (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (direction : Fin 2) (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension openUnitDisk 1 (startupFirstWord direction)
      (operator data (0, 0) 0 (base inputDimension 1 openUnitDisk (fun _ => 0) field))
      (startupRawFirstCandidate data direction field) := by
  have consumer :
      ∀ (data : RawKernelData measure inputDimension outputDimension (Grad.SpatialDilation.disk 1))
        (word : Word 1) (bound : 1 ≤ 1)
        (family : AllocatedFamily measure inputDimension outputDimension (Grad.SpatialDilation.disk 1) 1),
        FamilySpecification data word family →
        ∀ field : GraphGrade inputDimension 1 0 (Grad.SpatialDilation.disk 1),
        Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension (Grad.SpatialDilation.disk 1) 1 word
          (operator data (0, 0) 0 (base inputDimension 1 (Grad.SpatialDilation.disk 1) (fun _ => 0) field))
          (∑ selected : Finset (Fin 1), ∑ target : Word selectedᶜ.card,
            operator (family selected target) (0, 0) 0
              (inputDerivative inputDimension 1 1 0 (Grad.SpatialDilation.disk 1) bound field selected target)) :=
    weakGraphConsumer Parameter measure inputDimension outputDimension 1 1 0 1 (by norm_num)
  rw [show Grad.SpatialDilation.disk 1 = openUnitDisk from openUnitDisk_eq_ball.symm] at consumer
  exact consumer data (startupFirstWord direction) le_rfl
    (fun selected target => allocatedData data (startupFirstWord direction) selected target)
    (fun selected target => allocatedData_specification data (startupFirstWord direction) selected target) field

theorem startupFirstAllocationInput_bound (field : GraphGrade inputDimension 1 0 openUnitDisk)
    (selected : Finset (Fin 1)) (target : Word selectedᶜ.card) :
    ‖inputDerivative inputDimension 1 1 0 openUnitDisk le_rfl field selected target‖ ≤ ‖field‖ := by
  have rankBound : selectedᶜ.card ≤ 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ selectedᶜ
  have factorial : Nat.factorial selectedᶜ.card = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp rankBound with zero | one
    · rw [zero, Nat.factorial_zero]
    · rw [one, Nat.factorial_one]
  have total := orderedDerivative_norm_le inputDimension 1 selectedᶜ.card openUnitDisk (fun _ => 0) rankBound field
  rw [factorial, Nat.cast_one, Real.sqrt_one, one_mul] at total
  exact (PiLp.norm_apply_le _ target).trans total

def startupRawFirstDerivativeBudget
    (data : RawKernelData measure inputDimension outputDimension openUnitDisk) (direction : Fin 2) : ℝ :=
  ∑ selected : Finset (Fin 1), ∑ _target : Word selectedᶜ.card,
    Real.sqrt (data.rowBound (selectedIndex (startupFirstWord direction) selected) 0 *
      data.columnBound (selectedIndex (startupFirstWord direction) selected) 0)

theorem startupRawFirstCandidate_bound
    (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (direction : Fin 2) (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    ‖startupRawFirstCandidate data direction field‖ ≤ startupRawFirstDerivativeBudget data direction * ‖field‖ := by
  unfold startupRawFirstCandidate startupRawFirstDerivativeBudget
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro selected _
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro target _
  have bound := operator_norm_apply (allocatedData data (startupFirstWord direction) selected target) (0, 0) 0
    (inputDerivative inputDimension 1 1 0 openUnitDisk le_rfl field selected target)
  have row : (allocatedData data (startupFirstWord direction) selected target).rowBound (0, 0) 0 =
      data.rowBound (selectedIndex (startupFirstWord direction) selected) 0 := by
    change data.rowBound (indexAdd (0, 0) (selectedIndex (startupFirstWord direction) selected)) 0 = _
    simp only [indexAdd, Nat.zero_add]
  have column : (allocatedData data (startupFirstWord direction) selected target).columnBound (0, 0) 0 =
      data.columnBound (selectedIndex (startupFirstWord direction) selected) 0 := by
    change data.columnBound (indexAdd (0, 0) (selectedIndex (startupFirstWord direction) selected)) 0 = _
    simp only [indexAdd, Nat.zero_add]
  rw [row, column] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (startupFirstAllocationInput_bound field selected target) (Real.sqrt_nonneg _))

def startupRawFirstGraph (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (field : GraphGrade inputDimension 1 0 openUnitDisk) : GraphGrade outputDimension 1 0 openUnitDisk :=
  startupFirstGraph (operator data (0, 0) 0 (base inputDimension 1 openUnitDisk (fun _ => 0) field))
    (fun direction => startupRawFirstCandidate data direction field)
    (fun direction => startupRawFirst_weak data direction field)

theorem startupRawFirstGraph_base (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    base outputDimension 1 openUnitDisk (fun _ => 0) (startupRawFirstGraph data field) =
      operator data (0, 0) 0 (base inputDimension 1 openUnitDisk (fun _ => 0) field) :=
  startupFirstGraph_base _ _ _

def startupRawFirstBudget (data : RawKernelData measure inputDimension outputDimension openUnitDisk) : ℝ :=
  Real.sqrt (data.rowBound (0, 0) 0 * data.columnBound (0, 0) 0) +
    startupRawFirstDerivativeBudget data 0 + startupRawFirstDerivativeBudget data 1

theorem startupRawFirstGraph_bound (data : RawKernelData measure inputDimension outputDimension openUnitDisk)
    (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    ‖startupRawFirstGraph data field‖ ≤ startupRawFirstBudget data * ‖field‖ := by
  have zeroth := (operator_norm_apply data (0, 0) 0
    (base inputDimension 1 openUnitDisk (fun _ => 0) field)).trans
    (mul_le_mul_of_nonneg_left (base_norm_le inputDimension 1 openUnitDisk (fun _ => 0) field) (Real.sqrt_nonneg _))
  exact (startupFirstGraph_norm_bound _ _ _).trans
    ((add_le_add (add_le_add zeroth (startupRawFirstCandidate_bound data 0 field))
      (startupRawFirstCandidate_bound data 1 field)).trans_eq (by
        unfold startupRawFirstBudget
        ring))

/-- First-graph realization of the same represented kernel; the complete
 orthogonal covector allocation is retained in its actual weak derivatives. -/
def startupRawFirstGraphCLM (data : RawKernelData measure inputDimension outputDimension openUnitDisk) :
    GraphGrade inputDimension 1 0 openUnitDisk →L[ℂ] GraphGrade outputDimension 1 0 openUnitDisk := by
  let mapping : GraphGrade inputDimension 1 0 openUnitDisk →ₗ[ℂ] GraphGrade outputDimension 1 0 openUnitDisk := {
    toFun := startupRawFirstGraph data
    map_add' := by
      intro first second
      apply base_injective outputDimension 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
      rw [map_add, startupRawFirstGraph_base, startupRawFirstGraph_base, startupRawFirstGraph_base, map_add, map_add]
    map_smul' := by
      intro scalar field
      apply base_injective outputDimension 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
      rw [map_smul, startupRawFirstGraph_base, startupRawFirstGraph_base, map_smul, map_smul]
      rfl }
  exact mapping.mkContinuous (startupRawFirstBudget data) (startupRawFirstGraph_bound data)

end Grad.CartesianStartup
