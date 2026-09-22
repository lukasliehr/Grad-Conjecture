import GQC11APActualDifferentials

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

abbrev APFamily (L sigma gamma ell : ℝ) (dimension : ℕ) :=
  ∀ grade : ℕ, apGrade L sigma gamma ell dimension grade

def APFamilyCoherent {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) : Prop :=
  ∀ (low high : ℕ) (ordered : low ≤ high), apLowering L sigma gamma ell ordered (family high) = family low

def apFamilyClosedDerivative {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (cell : ℤ) (index : CartesianMultiIndex) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  apWeightedMultiDerivative L sigma gamma ell index le_rfl cell (family (cartesianOrder index + 2))

theorem apFamilyClosedDerivative_eq {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family)
    (cell : ℤ) (index : CartesianMultiIndex) (large : cartesianOrder index + 2 ≤ grade) :
    apFamilyClosedDerivative family cell index = apWeightedMultiDerivative L sigma gamma ell index large cell (family grade) := by
  unfold apFamilyClosedDerivative
  rw [← coherent (cartesianOrder index + 2) grade large, apWeightedMultiDerivative_lowering]

theorem apFamilyClosedDerivative_compatible {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family) (cell : ℤ) :
    ClosedTowerCompatible (apFamilyClosedDerivative family cell) := by
  intro index point inside
  rw [apFamilyClosedDerivative_eq family coherent cell index (grade := cartesianOrder index + 3) (by omega),
    apFamilyClosedDerivative_eq family coherent cell (1 + index.1, index.2)
      (grade := cartesianOrder index + 3) (by unfold cartesianOrder; omega),
    apFamilyClosedDerivative_eq family coherent cell (index.1, 1 + index.2)
      (grade := cartesianOrder index + 3) (by unfold cartesianOrder; omega)]
  exact apWeightedMultiDerivative_hasFDerivAt L sigma gamma ell index le_rfl cell
    (family (cartesianOrder index + 3)) point inside

theorem closedTower_wordDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (family : CartesianMultiIndex → C(ClosedDisk, Value)) (compatible : ClosedTowerCompatible family)
    (order : ℕ) (word : CartesianWord order) (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) :
    cartesianDerivative order word (closedDiskLift (family (0, 0))) point.val = family (cartesianWordIndex word) point := by
  have actual := closedTower_listDerivative family compatible (List.ofFn word) (0, 0) inside
  rw [Grad.GaugeCoefficients.Radial.operatorCartesianListDerivative_ofFn openUnitDisk_isOpen order word
    (closedTower_contDiffOn family compatible (0, 0)) inside] at actual
  change _ = closedDiskLift (family (0 + (List.ofFn word).count 0, 0 + (List.ofFn word).count 1)) point.val at actual
  rw [Nat.zero_add, Nat.zero_add, closedLift_value _ point.val inside] at actual
  exact actual

/-- A genuine closed jet reconstructed from the compatible differential tower. -/
def closedTowerJet {dimension : ℕ} (family : CartesianMultiIndex → C(ClosedDisk, ComplexEuclidean dimension))
    (compatible : ClosedTowerCompatible family) : ClosedJet dimension where
  value := family (0, 0)
  smoothInterior := closedTower_contDiffOn family compatible (0, 0)
  derivativeExists order word := ⟨family (cartesianWordIndex word), fun point inside =>
    (closedTower_wordDerivative family compatible order word point inside).symm⟩

theorem closedTowerJet_multiDerivative {dimension : ℕ}
    (family : CartesianMultiIndex → C(ClosedDisk, ComplexEuclidean dimension))
    (compatible : ClosedTowerCompatible family) (index : CartesianMultiIndex) :
    closedMultiDerivative (closedTowerJet family compatible) index = family index := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  rw [closedMultiDerivative, closedDerivative_spec _ _ _ point inside]
  exact closedTower_multiDerivative family compatible index point inside

def apFamilyWeightedJet {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family) (cell : ℤ) : ClosedJet dimension :=
  closedTowerJet (apFamilyClosedDerivative family cell) (apFamilyClosedDerivative_compatible family coherent cell)

theorem apFamilyWeightedJet_derivative {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family)
    (cell : ℤ) (index : CartesianMultiIndex) :
    closedMultiDerivative (apFamilyWeightedJet family coherent cell) index = apFamilyClosedDerivative family cell index :=
  closedTowerJet_multiDerivative _ _ index

end Grad.GaugeCoefficients.Physical.Compensated
