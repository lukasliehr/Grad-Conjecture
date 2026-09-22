import GQC7ClosedSmoothTower

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Neumann.Regularity

theorem familyClosedDerivative_compatible {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) (cell : ℤ) :
    ClosedTowerCompatible (familyClosedDerivative family cell) :=
  familyClosedDerivative_hasFDerivAt admissible family coherent cell

/-- Actual smooth closed operator jet reconstructed from the unchanged
coherent coefficient completion. All derivative claims are proved. -/
def actualCoefficientJet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) (cell : ℤ) :
    SmoothOperatorJet input output where
  value := familyClosedDerivative family cell (0, 0)
  smoothInterior := closedTower_contDiffOn (familyClosedDerivative family cell)
    (familyClosedDerivative_compatible admissible family coherent cell) (0, 0)
  derivativeExists index := ⟨familyClosedDerivative family cell index, fun point inside =>
    (closedTower_multiDerivative (familyClosedDerivative family cell)
      (familyClosedDerivative_compatible admissible family coherent cell) index point inside).symm⟩

theorem actualCoefficientJet_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (index : CartesianMultiIndex) :
    smoothOperatorDerivative (actualCoefficientJet admissible family coherent cell) index =
      familyClosedDerivative family cell index := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  change (Classical.choose ((actualCoefficientJet admissible family coherent cell).derivativeExists index)) point = _
  rw [Classical.choose_spec ((actualCoefficientJet admissible family coherent cell).derivativeExists index) point inside]
  exact closedTower_multiDerivative (familyClosedDerivative family cell)
    (familyClosedDerivative_compatible admissible family coherent cell) index point inside

theorem actualCoefficientJet_coherent {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    smoothOperatorDerivative (actualCoefficientJet admissible family coherent cell)
      (derivativeMultiIndex index) point = coefficientDerivative (family grade) cell index point := by
  rw [actualCoefficientJet_derivative]
  exact (coherent_derivative_raw family coherent cell index point).symm

end Grad.GaugeCoefficients.Physical.Compensated
