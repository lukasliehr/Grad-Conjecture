import GC18CrossNormalization

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Frame

theorem angularFamily_physical_congr {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (first second : CoefficientFamily L sigma gamma ell input output)
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second)
    (grade : ℕ) (angle : ℝ)
    (same : ∀ point, coefficientPhysicalValue (first grade) angle point =
      coefficientPhysicalValue (second grade) angle point) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily first grade) angle point =
      coefficientPhysicalValue (angularFamily second grade) angle point := by
  rw [angularFamily_physicalValue admissible first firstCoherent,
    angularFamily_physicalValue admissible second secondCoherent]
  simp_rw [same]

theorem angularSandwich_full_decomposition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (row : CoefficientFamily L sigma gamma ell 3 1)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (column : CoefficientFamily L sigma gamma ell 1 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge) (columnCoherent : FamilyCoherent column)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily
      (sandwichFamily admissible row (fullGaugeFamily gauge) column) grade) angle point =
      coefficientPhysicalValue (angularFamily (composeFamily admissible row column) grade) angle point +
        coefficientPhysicalValue (angularFamily (sandwichFamily admissible row gauge column) grade) angle point := by
  have firstCoherent := sandwichFamily_coherent admissible row (fullGaugeFamily gauge) column
    rowCoherent (fullGaugeFamily_coherent gauge gaugeCoherent) columnCoherent
  have sandwichCoherent := sandwichFamily_coherent admissible row gauge column rowCoherent gaugeCoherent columnCoherent
  have productCoherent : FamilyCoherent (composeFamily admissible row column) := rowCoherent.comp admissible columnCoherent
  have identity := angularFamily_physical_congr admissible
    (sandwichFamily admissible row (fullGaugeFamily gauge) column)
    (fun grade => composeFamily admissible row column grade + sandwichFamily admissible row gauge column grade)
    firstCoherent (productCoherent.add sandwichCoherent) grade angle (fun other => by
      rw [sandwichFull_physicalValue admissible row gauge column rowCoherent gaugeCoherent columnCoherent,
        family_physicalValue_add admissible _ _ productCoherent sandwichCoherent]) point
  rw [angularFamily_add, family_physicalValue_add admissible _ _
    (angularFamily_coherent _ productCoherent) (angularFamily_coherent _ sandwichCoherent)] at identity
  exact identity

theorem scalarSquare_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (composeFamily admissible (scalarRowFamily L sigma gamma ell)
      (scalarColumnFamily L sigma gamma ell) grade) angle point = ContinuousLinearMap.id ℂ (PhysicalValue 1) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_one]
  change familyMatrix (composeFamily admissible _ _) grade angle point = 1
  rw [familyMatrix_comp admissible _ _ (scalarRow_coherent L sigma gamma ell) (scalarColumn_coherent L sigma gamma ell),
    scalarRow_matrix admissible, scalarColumn_matrix admissible]
  ext row column
  fin_cases row
  fin_cases column
  simp [Matrix.mul_apply, Matrix.single_apply]

theorem angularScalarSquare_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily (composeFamily admissible (scalarRowFamily L sigma gamma ell)
      (scalarColumnFamily L sigma gamma ell)) grade) angle point = ContinuousLinearMap.id ℂ (PhysicalValue 1) := by
  rw [angularFamily_physicalValue admissible
    (composeFamily admissible (scalarRowFamily L sigma gamma ell) (scalarColumnFamily L sigma gamma ell))
    ((scalarRow_coherent L sigma gamma ell).comp admissible (scalarColumn_coherent L sigma gamma ell))]
  simp_rw [scalarSquare_physicalValue admissible]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const, sub_zero, one_smul]

/-- Literal δ=Π(e3ᵀ C e3), with the circle term proved rather than assumed. -/
theorem deltaCoefficient_full_formula {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (deltaCoefficient admissible gauge grade) angle point =
      coefficientPhysicalValue (angularFamily
        (sandwichFamily admissible (scalarRowFamily L sigma gamma ell) (fullGaugeFamily gauge)
          (scalarColumnFamily L sigma gamma ell)) grade) angle point := by
  rw [angularSandwich_full_decomposition admissible _ gauge _
    (scalarRow_coherent L sigma gamma ell) coherent (scalarColumn_coherent L sigma gamma ell),
    angularScalarSquare_physicalValue admissible]
  unfold deltaCoefficient
  rw [family_physicalValue_add admissible (identityFamily L sigma gamma ell 1) (deltaDeviation admissible gauge)
    (identityFamily_coherent L sigma gamma ell 1) (deltaDeviation_coherent admissible gauge coherent),
    identityFamily, identityFamily_physicalValue]
  rfl

/-- The full coefficient C is precisely the accepted physical gauge matrix
of the actual frame and seed, in its original stored coordinates. -/
theorem actualFullGauge_matrix {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fullGaugeFamily ledger.val.gaugeDeviation) grade angle point =
      physicalGaugeMatrix (physicalSeedMatrix rho alpha delta parameter angle)
        (operatorMatrix (fourierEvaluation (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) angle point))
        (operatorMatrix (coefficientPhysicalValue (ledger.val.frameInverse grade) angle point)).transpose point := by
  unfold familyMatrix
  rw [fullGaugeFamily_physicalValue admissible _ ledger.property.1.2.2.2.1,
    operatorMatrix_add, operatorMatrix_one, ledger.property.2.2.2.2.1 grade angle point]
  abel

end Grad.GaugeCoefficients.Physical.RadialLedger
