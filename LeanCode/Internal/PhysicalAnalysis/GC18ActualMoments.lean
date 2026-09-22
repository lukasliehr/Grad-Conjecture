import GC18MomentOperators

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem fullGauge_mu_moment {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    closedAngularMean (fun other => storedTangentDot other
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other (storedTangent other))) point =
      radiusScalar point * familyMatrix (muCoefficient admissible gauge) grade angle point 0 0 := by
  let numerator := sandwichFamily admissible (tangentRowFamily L sigma gamma ell)
    (fullGaugeFamily gauge) (tangentColumnFamily L sigma gamma ell)
  have numeratorCoherent : FamilyCoherent numerator := sandwichFamily_coherent admissible _ _ _
    (tangentRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) (tangentColumn_coherent L sigma gamma ell)
  have integrand : (fun other => storedTangentDot other
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other (storedTangent other))) =
      fun other => familyMatrix numerator grade angle other 0 0 := by
    funext other
    rw [sandwichFamily_entry_action admissible _ _ _ (tangentRow_coherent L sigma gamma ell)
      (fullGaugeFamily_coherent gauge coherent) (tangentColumn_coherent L sigma gamma ell),
      tangentColumn_basis admissible, tangentRow_action admissible]
  rw [integrand, familyMatrix_angularMean admissible numerator numeratorCoherent]
  have identity := radialSandwich_physical_left admissible (fullGaugeFamily gauge) (tangentColumnFamily L sigma gamma ell)
    (fullGaugeFamily_coherent gauge coherent) (tangentColumn_coherent L sigma gamma ell) grade angle point
  rw [← muCoefficient_full_formula admissible gauge coherent] at identity
  have scalar := congrArg (fun mapping : OperatorValue 1 1 => operatorMatrix mapping 0 0) identity
  simpa only [familyMatrix, numerator, operatorMatrix_smul, Matrix.smul_apply, smul_eq_mul, radiusScalar] using scalar

theorem fullGauge_eta_moment {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    closedAngularMean (fun other => storedTangentDot other
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other storedScalar)) point =
      radiusScalar point * familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0 := by
  let numerator := sandwichFamily admissible (tangentRowFamily L sigma gamma ell)
    (fullGaugeFamily gauge) (scalarColumnFamily L sigma gamma ell)
  have numeratorCoherent : FamilyCoherent numerator := sandwichFamily_coherent admissible _ _ _
    (tangentRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) (scalarColumn_coherent L sigma gamma ell)
  have integrand : (fun other => storedTangentDot other
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other storedScalar)) =
      fun other => familyMatrix numerator grade angle other 0 0 := by
    funext other
    rw [sandwichFamily_entry_action admissible _ _ _ (tangentRow_coherent L sigma gamma ell)
      (fullGaugeFamily_coherent gauge coherent) (scalarColumn_coherent L sigma gamma ell),
      scalarColumn_basis admissible, tangentRow_action admissible]
  rw [integrand, familyMatrix_angularMean admissible numerator numeratorCoherent]
  have identity := radialSandwich_physical_left admissible (fullGaugeFamily gauge) (scalarColumnFamily L sigma gamma ell)
    (fullGaugeFamily_coherent gauge coherent) (scalarColumn_coherent L sigma gamma ell) grade angle point
  rw [← etaCoefficient_full_formula admissible gauge coherent] at identity
  have scalar := congrArg (fun mapping : OperatorValue 1 1 => operatorMatrix mapping 0 0) identity
  simpa only [familyMatrix, numerator, operatorMatrix_smul, Matrix.smul_apply, smul_eq_mul, radiusScalar] using scalar

theorem fullGauge_nu_moment {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    closedAngularMean (fun other =>
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other (storedTangent other)) 2) point =
      radiusScalar point * familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0 := by
  let numerator := sandwichFamily admissible (scalarRowFamily L sigma gamma ell)
    (fullGaugeFamily gauge) (tangentColumnFamily L sigma gamma ell)
  have numeratorCoherent : FamilyCoherent numerator := sandwichFamily_coherent admissible _ _ _
    (scalarRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) (tangentColumn_coherent L sigma gamma ell)
  have integrand : (fun other =>
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other (storedTangent other)) 2) =
      fun other => familyMatrix numerator grade angle other 0 0 := by
    funext other
    rw [sandwichFamily_entry_action admissible _ _ _ (scalarRow_coherent L sigma gamma ell)
      (fullGaugeFamily_coherent gauge coherent) (tangentColumn_coherent L sigma gamma ell),
      tangentColumn_basis admissible, scalarRow_action admissible]
  rw [integrand, familyMatrix_angularMean admissible numerator numeratorCoherent]
  have identity := radialSandwich_physical_right admissible (scalarRowFamily L sigma gamma ell) (fullGaugeFamily gauge)
    (scalarRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) grade angle point
  rw [← nuCoefficient_full_formula admissible gauge coherent] at identity
  have scalar := congrArg (fun mapping : OperatorValue 1 1 => operatorMatrix mapping 0 0) identity
  simpa only [familyMatrix, numerator, operatorMatrix_smul, Matrix.smul_apply, smul_eq_mul, radiusScalar] using scalar

theorem fullGauge_delta_moment {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    closedAngularMean (fun other => (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other storedScalar) 2) point =
      familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0 := by
  let numerator := sandwichFamily admissible (scalarRowFamily L sigma gamma ell)
    (fullGaugeFamily gauge) (scalarColumnFamily L sigma gamma ell)
  have numeratorCoherent : FamilyCoherent numerator := sandwichFamily_coherent admissible _ _ _
    (scalarRow_coherent L sigma gamma ell) (fullGaugeFamily_coherent gauge coherent) (scalarColumn_coherent L sigma gamma ell)
  have integrand : (fun other => (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other storedScalar) 2) =
      fun other => familyMatrix numerator grade angle other 0 0 := by
    funext other
    rw [sandwichFamily_entry_action admissible _ _ _ (scalarRow_coherent L sigma gamma ell)
      (fullGaugeFamily_coherent gauge coherent) (scalarColumn_coherent L sigma gamma ell),
      scalarColumn_basis admissible, scalarRow_action admissible]
  rw [integrand, familyMatrix_angularMean admissible numerator numeratorCoherent]
  exact congrArg (fun mapping : OperatorValue 1 1 => operatorMatrix mapping 0 0)
    (deltaCoefficient_full_formula admissible gauge coherent grade angle point).symm

end Grad.GaugeCoefficients.Physical.RadialLedger
