import GC18CartesianContinuity

noncomputable section

set_option maxHeartbeats 1500000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

def operatorEntryCLM {input output : ℕ} (row : Fin output) (column : Fin input) :
    OperatorValue input output →L[ℂ] ℂ :=
  (PiLp.proj 2 (fun _ : Fin output => ℂ) row).comp
    (ContinuousLinearMap.apply ℂ (PhysicalValue output) (operatorBasis column))

theorem familyMatrix_angularMean {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (row : Fin output) (column : Fin input) :
    closedAngularMean (fun other => familyMatrix family grade angle other row column) point =
      familyMatrix (angularFamily family) grade angle point row column := by
  unfold familyMatrix
  rw [angularFamily_physicalValue admissible family coherent]
  exact (closedAngularMean_clm ((operatorEntryCLM row column).restrictScalars ℝ)
    (fun other => coefficientPhysicalValue (family grade) angle other)
    (coefficientPhysicalValue_continuous admissible family coherent grade angle) point).symm

theorem tangentColumn_basis {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (tangentColumnFamily L sigma gamma ell grade) angle point (operatorBasis 0) = storedTangent point := by
  apply PiLp.ext
  intro row
  change familyMatrix (tangentColumnFamily L sigma gamma ell) grade angle point row 0 = _
  rw [tangentColumn_matrix admissible]
  fin_cases row <;> simp [storedTangent, Matrix.sub_apply]

theorem scalarColumn_basis {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (scalarColumnFamily L sigma gamma ell grade) angle point (operatorBasis 0) = storedScalar := by
  apply PiLp.ext
  intro row
  change familyMatrix (scalarColumnFamily L sigma gamma ell) grade angle point row 0 = _
  rw [scalarColumn_matrix admissible]
  fin_cases row <;> simp [storedScalar]

theorem tangentRow_action {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : PhysicalValue 3) :
    (coefficientPhysicalValue (tangentRowFamily L sigma gamma ell grade) angle point value) 0 = storedTangentDot point value := by
  rw [operatorMatrix_action]
  change (∑ column : Fin 3, familyMatrix (tangentRowFamily L sigma gamma ell) grade angle point 0 column * value column) = _
  rw [tangentRow_matrix admissible]
  simp [storedTangentDot, Matrix.sub_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem scalarRow_action {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : PhysicalValue 3) :
    (coefficientPhysicalValue (scalarRowFamily L sigma gamma ell grade) angle point value) 0 = value 2 := by
  rw [operatorMatrix_action]
  change (∑ column : Fin 3, familyMatrix (scalarRowFamily L sigma gamma ell) grade angle point 0 column * value column) = _
  rw [scalarRow_matrix admissible]
  simp [Matrix.single_apply]

theorem sandwichFamily_entry_action {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (row : CoefficientFamily L sigma gamma ell 3 1)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (column : CoefficientFamily L sigma gamma ell 1 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge) (columnCoherent : FamilyCoherent column)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (sandwichFamily admissible row gauge column) grade angle point 0 0 =
      (coefficientPhysicalValue (row grade) angle point
        (coefficientPhysicalValue (gauge grade) angle point
          (coefficientPhysicalValue (column grade) angle point (operatorBasis 0)))) 0 := by
  unfold familyMatrix sandwichFamily composeFamily
  rw [family_physicalValue_comp admissible row _ rowCoherent (gaugeCoherent.comp admissible columnCoherent),
    family_physicalValue_comp admissible gauge column gaugeCoherent columnCoherent]
  rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
