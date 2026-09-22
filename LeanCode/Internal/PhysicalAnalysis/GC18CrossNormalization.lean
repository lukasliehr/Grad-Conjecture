import GC18FullNumerators
import GC18ExtensionValue

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem zeroFamily_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (input output grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (zeroFamily L sigma gamma ell input output grade) angle point = 0 := by
  apply operatorMatrix_injective
  exact familyMatrix_zero admissible input output grade angle point

theorem radialDivisionFamily_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (input output : ℕ) :
    radialDivisionFamily admissible (zeroFamily L sigma gamma ell input output) = zeroFamily L sigma gamma ell input output := by
  funext grade
  simp only [radialDivisionFamily, radialFamily, laplacianFamily, angularFamily, zeroFamily, map_zero]

theorem radialDivisionFamily_physical_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ)
    (zero : ∀ point, coefficientPhysicalValue (family grade) angle point = 0) (point : ClosedDisk) :
    coefficientPhysicalValue (radialDivisionFamily admissible family grade) angle point = 0 := by
  have identity := radialDivisionFamily_physical_congr admissible family (zeroFamily L sigma gamma ell input output)
    coherent (zeroFamily_coherent L sigma gamma ell input output) grade angle
    (fun other => (zero other).trans (zeroFamily_physicalValue admissible input output grade angle other).symm) point
  rw [radialDivisionFamily_zero, zeroFamily_physicalValue admissible] at identity
  exact identity

theorem scalarRow_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (scalarRowFamily L sigma gamma ell) grade angle point = (Matrix.single 0 2 1 : Matrix (Fin 1) (Fin 3) ℂ) := by
  unfold scalarRowFamily familyMatrix
  rw [constantFamily_physicalValue admissible, operatorMatrix_matrixUnit]

theorem scalarColumn_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (scalarColumnFamily L sigma gamma ell) grade angle point = (Matrix.single 2 0 1 : Matrix (Fin 3) (Fin 1) ℂ) := by
  unfold scalarColumnFamily familyMatrix
  rw [constantFamily_physicalValue admissible, operatorMatrix_matrixUnit]

theorem tangentScalar_physical_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (composeFamily admissible (tangentRowFamily L sigma gamma ell)
      (scalarColumnFamily L sigma gamma ell) grade) angle point = 0 := by
  apply operatorMatrix_injective
  change familyMatrix (composeFamily admissible _ _) grade angle point = 0
  rw [familyMatrix_comp admissible _ _ (tangentRow_coherent L sigma gamma ell) (scalarColumn_coherent L sigma gamma ell),
    tangentRow_matrix admissible, scalarColumn_matrix admissible]
  ext row column
  fin_cases row
  fin_cases column
  simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.single_apply]

theorem scalarTangent_physical_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (composeFamily admissible (scalarRowFamily L sigma gamma ell)
      (tangentColumnFamily L sigma gamma ell) grade) angle point = 0 := by
  apply operatorMatrix_injective
  change familyMatrix (composeFamily admissible _ _) grade angle point = 0
  rw [familyMatrix_comp admissible _ _ (scalarRow_coherent L sigma gamma ell) (tangentColumn_coherent L sigma gamma ell),
    scalarRow_matrix admissible, tangentColumn_matrix admissible]
  ext row column
  fin_cases row
  fin_cases column
  simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.single_apply]

theorem etaCoefficient_full_formula {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (etaCoefficient admissible gauge grade) angle point =
      coefficientPhysicalValue (radialDivisionFamily admissible
        (sandwichFamily admissible (tangentRowFamily L sigma gamma ell) (fullGaugeFamily gauge)
          (scalarColumnFamily L sigma gamma ell)) grade) angle point := by
  rw [radialSandwich_full_decomposition admissible _ gauge _
    (tangentRow_coherent L sigma gamma ell) coherent (scalarColumn_coherent L sigma gamma ell),
    radialDivisionFamily_physical_zero admissible
      (composeFamily admissible (tangentRowFamily L sigma gamma ell) (scalarColumnFamily L sigma gamma ell))
      ((tangentRow_coherent L sigma gamma ell).comp admissible (scalarColumn_coherent L sigma gamma ell))
      grade angle (tangentScalar_physical_zero admissible grade angle), zero_add]
  rfl

theorem nuCoefficient_full_formula {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (nuCoefficient admissible gauge grade) angle point =
      coefficientPhysicalValue (radialDivisionFamily admissible
        (sandwichFamily admissible (scalarRowFamily L sigma gamma ell) (fullGaugeFamily gauge)
          (tangentColumnFamily L sigma gamma ell)) grade) angle point := by
  rw [radialSandwich_full_decomposition admissible _ gauge _
    (scalarRow_coherent L sigma gamma ell) coherent (tangentColumn_coherent L sigma gamma ell),
    radialDivisionFamily_physical_zero admissible
      (composeFamily admissible (scalarRowFamily L sigma gamma ell) (tangentColumnFamily L sigma gamma ell))
      ((scalarRow_coherent L sigma gamma ell).comp admissible (tangentColumn_coherent L sigma gamma ell))
      grade angle (scalarTangent_physical_zero admissible grade angle), zero_add]
  rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
