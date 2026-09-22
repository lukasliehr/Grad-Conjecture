import GQE8CompletedPreservation

noncomputable section
set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

def referenceRowFamily (L sigma gamma ell : ℝ) : CoefficientFamily L sigma gamma ell 3 1 :=
  fixedJetFamily L sigma gamma ell radialRowJet

theorem referenceRowFamily_matrix (L sigma gamma ell : ℝ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (referenceRowFamily L sigma gamma ell) grade angle point = circleTraceCovector point := by
  change operatorMatrix (coefficientPhysicalValue (fixedJetFamily L sigma gamma ell radialRowJet grade) angle point) = _
  rw [fixedJetFamily_physicalValue]
  ext row column
  fin_cases row
  change radialRowJet.value point (operatorBasis column) 0 = circleTraceCovector point 0 column
  rw [radialRowJet_value]
  fin_cases column <;> simp [operatorBasis, circleTraceCovector]

def normalRowFamily {L sigma gamma ell : ℝ} (data : LedgerData L sigma gamma ell) :
    CoefficientFamily L sigma gamma ell 3 1 :=
  fun grade => referenceRowFamily L sigma gamma ell grade + data.traceDeviation grade

theorem normalRowFamily_coherent {L sigma gamma ell : ℝ}
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) : FamilyCoherent (normalRowFamily data) :=
  (fixedJetFamily_coherent L sigma gamma ell radialRowJet).add coherent.2.2.2.2.2.1

/-- Literal AO24. The inverse seed, physical planar inclusion and inverse
transpose of the actual frame remain in their prescribed order. -/
theorem actualNormalRow_matrix {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (normalRowFamily ledger.val) grade angle point =
      (spatialColumn point).transpose * familyMatrix ledger.val.seedInverse grade angle point *
        planarPhysicalInclusion.transpose * (familyMatrix ledger.val.frameInverse grade angle point).transpose := by
  have literal := ledger.property.2.2.2.2.2.2.1 grade angle point
  have addition := familyMatrix_add admissible (referenceRowFamily L parameters.sigma0 parameters.gamma ell)
    ledger.val.traceDeviation (fixedJetFamily_coherent L parameters.sigma0 parameters.gamma ell radialRowJet)
    ledger.property.1.2.2.2.2.2.1 grade angle point
  exact addition.trans ((congrArg₂ (fun first second : Matrix (Fin 1) (Fin 3) ℂ => first + second)
    (referenceRowFamily_matrix L parameters.sigma0 parameters.gamma ell grade angle point) literal).trans (by abel))

theorem normalRowFamily_sub_reference {L sigma gamma ell : ℝ}
    (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    normalRowFamily data grade - referenceRowFamily L sigma gamma ell grade = data.traceDeviation grade :=
  add_sub_cancel_left _ _

end Grad.GaugeCoefficients.Physical.Compensated
