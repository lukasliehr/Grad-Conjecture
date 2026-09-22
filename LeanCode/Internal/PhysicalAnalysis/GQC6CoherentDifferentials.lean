import GQC5ActualFirstDerivative

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Radial hiding zeroDerivativeIndexAt
open Grad.GaugeCoefficients.Neumann.Regularity

def familyClosedDerivative {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (cell : ℤ) (index : CartesianMultiIndex) :
    C(ClosedDisk, OperatorValue input output) :=
  coefficientDerivative (family (cartesianOrder index)) cell (multiIndexAtOrder index)

theorem shiftedCoordinate_eq_family {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (fixed : CartesianMultiIndex) (index : DerivativeIndex 1) :
    coefficientDerivative (derivativeFamily fixed family 1) cell index =
      familyClosedDerivative family cell (shiftedOperatorIndex (derivativeMultiIndex index) fixed) := by
  apply ContinuousMap.ext
  intro point
  change coefficientDerivative (coefficientDerivativeShift L sigma gamma ell 1 input output fixed
    (family (1 + cartesianOrder fixed))) cell index point = _
  rw [coefficientDerivativeShift_derivative]
  exact coherent _ _ (raisedDerivativeIndex fixed index)
    (multiIndexAtOrder (shiftedOperatorIndex (derivativeMultiIndex index) fixed)) rfl cell point

/-- Every stored derivative of one coherent all-grade family has the
genuine next Cartesian derivative on the original disk. -/
theorem familyClosedDerivative_hasFDerivAt {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (index : CartesianMultiIndex) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift (familyClosedDerivative family cell index))
      (planarDerivative
        (closedDiskLift (familyClosedDerivative family cell (1 + index.1, index.2)) point)
        (closedDiskLift (familyClosedDerivative family cell (index.1, 1 + index.2)) point)) point := by
  have actual := coefficientHasFirstDerivative admissible (derivativeFamily index family 1) cell point inside
  have zeroCoordinate : coefficientDerivative (derivativeFamily index family 1) cell (zeroDerivativeIndexAt 1) =
      familyClosedDerivative family cell index := by
    simpa [shiftedOperatorIndex, derivativeMultiIndex, zeroDerivativeIndexAt] using
      shiftedCoordinate_eq_family family coherent cell index (zeroDerivativeIndexAt 1)
  have firstCoordinate : coefficientDerivative (derivativeFamily index family 1) cell (firstCoordinateIndex 0) =
      familyClosedDerivative family cell (1 + index.1, index.2) := by
    simpa [shiftedOperatorIndex, derivativeMultiIndex, firstCoordinateIndex] using
      shiftedCoordinate_eq_family family coherent cell index (firstCoordinateIndex 0)
  have secondCoordinate : coefficientDerivative (derivativeFamily index family 1) cell (firstCoordinateIndex 1) =
      familyClosedDerivative family cell (index.1, 1 + index.2) := by
    simpa [shiftedOperatorIndex, derivativeMultiIndex, firstCoordinateIndex] using
      shiftedCoordinate_eq_family family coherent cell index (firstCoordinateIndex 1)
  rw [zeroCoordinate, closedLift_value _ point inside] at actual
  change HasFDerivAt _ (planarDerivative
    (coefficientDerivative (derivativeFamily index family 1) cell (firstCoordinateIndex 0) _)
    (coefficientDerivative (derivativeFamily index family 1) cell (firstCoordinateIndex 1) _)) point at actual
  rw [firstCoordinate, secondCoordinate] at actual
  rw [closedLift_value _ point inside, closedLift_value _ point inside]
  exact actual

end Grad.GaugeCoefficients.Physical.Compensated
