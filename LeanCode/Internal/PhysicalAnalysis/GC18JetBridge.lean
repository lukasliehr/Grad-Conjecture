import GC18BoundsConsumer
import DivisionConsumer
import TangentialPolar

noncomputable section

set_option maxHeartbeats 1400000

open Set
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.RepresentedKernel.SpatialProduct

def operatorJetColumnValue {input output : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) : C(ClosedDisk, PhysicalValue output) :=
  ⟨fun point => field.value point column,
    (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).continuous.comp field.value.continuous⟩

theorem closedDiskLift_operatorJetColumnValue {input output : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) : closedDiskLift (operatorJetColumnValue field column) =
      (ContinuousLinearMap.apply ℂ (PhysicalValue output) column) ∘ closedDiskLift field.value := by
  funext point
  by_cases inside : point ∈ closedUnitDisk
  · simp [closedDiskLift, inside]
    rfl
  · simp [closedDiskLift, inside]

theorem operatorJetColumnValue_smooth {input output : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) : ContDiffOn ℝ ∞ (closedDiskLift (operatorJetColumnValue field column)) openUnitDisk := by
  rw [closedDiskLift_operatorJetColumnValue]
  exact ((ContinuousLinearMap.apply ℂ (PhysicalValue output) column).restrictScalars ℝ).contDiff.comp_contDiffOn field.smoothInterior

def operatorJetColumnDerivative {input output rank : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) (word : CartesianWord rank) : C(ClosedDisk, PhysicalValue output) :=
  ⟨fun point => smoothOperatorDerivative field (orthogonalTargetIndex word) point column,
    (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).continuous.comp
      (smoothOperatorDerivative field (orthogonalTargetIndex word)).continuous⟩

theorem operatorJetColumnDerivative_spec {input output rank : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) (word : CartesianWord rank) :
    IsCartesianExtension (operatorJetColumnValue field column) rank word (operatorJetColumnDerivative field column word) := by
  intro point inside
  have smooth := field.smoothInterior.contDiffAt (openUnitDisk_isOpen.mem_nhds inside)
  rw [cartesianDerivative, closedDiskLift_operatorJetColumnValue]
  change operatorJetColumnDerivative field column word point =
    iteratedFDeriv ℝ rank (((ContinuousLinearMap.apply ℂ (PhysicalValue output) column).restrictScalars ℝ) ∘
      closedDiskLift field.value) point.val (fun position => spatialBasis (word position))
  rw [((ContinuousLinearMap.apply ℂ (PhysicalValue output) column).restrictScalars ℝ).iteratedFDeriv_comp_left
    smooth (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))]
  change smoothOperatorDerivative field (orthogonalTargetIndex word) point column =
    wordDerivative rank word (closedDiskLift field.value) point.val column
  exact congrArg (fun operator : OperatorValue input output => operator column)
    (wordDerivative_eq_smoothOperatorDerivative field word point.val inside).symm

/-- A genuine closed jet extracted from a smooth coefficient generator.
This bridge will transfer O11 to the C² coefficient graph by bounded closure. -/
def operatorJetColumn {input output : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) : ClosedJet output where
  value := operatorJetColumnValue field column
  smoothInterior := operatorJetColumnValue_smooth field column
  derivativeExists _rank word := ⟨operatorJetColumnDerivative field column word,
    operatorJetColumnDerivative_spec field column word⟩

theorem operatorJetColumn_derivative {input output rank : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) (word : CartesianWord rank) :
    closedDerivative (operatorJetColumn field column) rank word = operatorJetColumnDerivative field column word :=
  (cartesianExtension_unique (operatorJetColumn field column) rank word
    (operatorJetColumnDerivative field column word) (operatorJetColumnDerivative_spec field column word)).symm

end Grad.GaugeCoefficients.Physical.RadialLedger
