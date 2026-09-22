import GC18Interface

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem tangentColumn_coherent (L sigma gamma ell : ℝ) :
    FamilyCoherent (tangentColumnFamily L sigma gamma ell) :=
  (fixedJetFamily_coherent L sigma gamma ell _).sub (fixedJetFamily_coherent L sigma gamma ell _)

theorem tangentRow_coherent (L sigma gamma ell : ℝ) :
    FamilyCoherent (tangentRowFamily L sigma gamma ell) :=
  (fixedJetFamily_coherent L sigma gamma ell _).sub (fixedJetFamily_coherent L sigma gamma ell _)

theorem scalarColumn_coherent (L sigma gamma ell : ℝ) :
    FamilyCoherent (scalarColumnFamily L sigma gamma ell) := constantFamily_coherent L sigma gamma ell _

theorem scalarRow_coherent (L sigma gamma ell : ℝ) :
    FamilyCoherent (scalarRowFamily L sigma gamma ell) := constantFamily_coherent L sigma gamma ell _

theorem sandwichFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row : CoefficientFamily L sigma gamma ell 3 1) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (column : CoefficientFamily L sigma gamma ell 1 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge)
    (columnCoherent : FamilyCoherent column) : FamilyCoherent (sandwichFamily admissible row gauge column) :=
  rowCoherent.comp admissible (gaugeCoherent.comp admissible columnCoherent)

theorem muDeviation_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (muDeviation admissible gauge) :=
  radialDivisionFamily_coherent admissible _ (sandwichFamily_coherent admissible _ _ _
    (tangentRow_coherent L sigma gamma ell) coherent (tangentColumn_coherent L sigma gamma ell))

theorem etaCoefficient_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (etaCoefficient admissible gauge) :=
  radialDivisionFamily_coherent admissible _ (sandwichFamily_coherent admissible _ _ _
    (tangentRow_coherent L sigma gamma ell) coherent (scalarColumn_coherent L sigma gamma ell))

theorem nuCoefficient_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (nuCoefficient admissible gauge) :=
  radialDivisionFamily_coherent admissible _ (sandwichFamily_coherent admissible _ _ _
    (scalarRow_coherent L sigma gamma ell) coherent (tangentColumn_coherent L sigma gamma ell))

theorem deltaDeviation_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (deltaDeviation admissible gauge) :=
  angularFamily_coherent _ (sandwichFamily_coherent admissible _ _ _
    (scalarRow_coherent L sigma gamma ell) coherent (scalarColumn_coherent L sigma gamma ell))

def tangentColumnConstant (grade : ℕ) : ℝ :=
  fixedJetConstant (coordinateOperatorJet 0 (matrixUnit (input := 1) (output := 3) 1 0)) grade +
    fixedJetConstant (coordinateOperatorJet 1 (matrixUnit (input := 1) (output := 3) 0 0)) grade

def tangentRowConstant (grade : ℕ) : ℝ :=
  fixedJetConstant (coordinateOperatorJet 0 (matrixUnit (input := 3) (output := 1) 0 1)) grade +
    fixedJetConstant (coordinateOperatorJet 1 (matrixUnit (input := 3) (output := 1) 0 0)) grade

def scalarColumnConstant : ℕ → ℝ := fixedFamilyConstant (matrixUnit (input := 1) (output := 3) 2 0)
def scalarRowConstant : ℕ → ℝ := fixedFamilyConstant (matrixUnit (input := 3) (output := 1) 0 2)

theorem tangentColumnConstant_nonnegative (grade : ℕ) : 0 ≤ tangentColumnConstant grade :=
  add_nonneg (fixedJetConstant_nonnegative _ _) (fixedJetConstant_nonnegative _ _)
theorem tangentRowConstant_nonnegative (grade : ℕ) : 0 ≤ tangentRowConstant grade :=
  add_nonneg (fixedJetConstant_nonnegative _ _) (fixedJetConstant_nonnegative _ _)
theorem scalarColumnConstant_nonnegative (grade : ℕ) : 0 ≤ scalarColumnConstant grade :=
  fixedFamilyConstant_nonnegative _ _
theorem scalarRowConstant_nonnegative (grade : ℕ) : 0 ≤ scalarRowConstant grade :=
  fixedFamilyConstant_nonnegative _ _

theorem tangentColumn_bound (L sigma gamma ell : ℝ) (grade : ℕ) :
    ‖tangentColumnFamily L sigma gamma ell grade‖ ≤ tangentColumnConstant grade :=
  (norm_sub_le _ _).trans (add_le_add (fixedJetFamily_norm_le L sigma gamma ell _ grade)
    (fixedJetFamily_norm_le L sigma gamma ell _ grade))

theorem tangentRow_bound (L sigma gamma ell : ℝ) (grade : ℕ) :
    ‖tangentRowFamily L sigma gamma ell grade‖ ≤ tangentRowConstant grade :=
  (norm_sub_le _ _).trans (add_le_add (fixedJetFamily_norm_le L sigma gamma ell _ grade)
    (fixedJetFamily_norm_le L sigma gamma ell _ grade))

theorem scalarColumn_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    ‖scalarColumnFamily L sigma gamma ell grade‖ ≤ scalarColumnConstant grade :=
  constantFamily_norm_le admissible _ grade
theorem scalarRow_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    ‖scalarRowFamily L sigma gamma ell grade‖ ≤ scalarRowConstant grade :=
  constantFamily_norm_le admissible _ grade

def sandwichConstant (row column : ℕ → ℝ) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * row grade * gradeProductConstant grade * column grade

theorem sandwichConstant_nonnegative {row column : ℕ → ℝ}
    (rowNonnegative : ∀ grade, 0 ≤ row grade) (columnNonnegative : ∀ grade, 0 ≤ column grade)
    (grade : ℕ) : 0 ≤ sandwichConstant row column grade := by
  unfold sandwichConstant
  positivity [gradeProductConstant_nonnegative grade, rowNonnegative grade, columnNonnegative grade]

theorem sandwichFamily_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row : CoefficientFamily L sigma gamma ell 3 1) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (column : CoefficientFamily L sigma gamma ell 1 3) (rowConstant columnConstant : ℕ → ℝ)
    (rowNonnegative : ∀ grade, 0 ≤ rowConstant grade) (_columnNonnegative : ∀ grade, 0 ≤ columnConstant grade)
    (rowBound : ∀ grade, ‖row grade‖ ≤ rowConstant grade)
    (columnBound : ∀ grade, ‖column grade‖ ≤ columnConstant grade) (grade : ℕ) :
    ‖sandwichFamily admissible row gauge column grade‖ ≤
      sandwichConstant rowConstant columnConstant grade * ‖gauge grade‖ := by
  have productNonnegative := gradeProductConstant_nonnegative grade
  have inner := (coefficientComposition_norm_le admissible grade (gauge grade) (column grade)).trans
    (mul_le_mul_of_nonneg_left (columnBound grade) (mul_nonneg productNonnegative (norm_nonneg _)))
  have outer := (coefficientComposition_norm_le admissible grade (row grade)
    (composeFamily admissible gauge column grade)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (rowBound grade) productNonnegative) inner
      (norm_nonneg _) (mul_nonneg productNonnegative (rowNonnegative grade)))
  exact outer.trans_eq (by unfold sandwichConstant; ring)

def numeratorConstant (row column gauge : ℕ → ℝ) (grade : ℕ) : ℝ :=
  radialDivisionConstant grade * sandwichConstant row column (grade + 2) * gauge (grade + 2)

theorem numeratorConstant_nonnegative {row column gauge : ℕ → ℝ}
    (rowNonnegative : ∀ grade, 0 ≤ row grade) (columnNonnegative : ∀ grade, 0 ≤ column grade)
    (gaugeNonnegative : ∀ grade, 0 ≤ gauge grade) (grade : ℕ) :
    0 ≤ numeratorConstant row column gauge grade :=
  mul_nonneg (mul_nonneg (radialDivisionConstant_nonnegative grade)
    (sandwichConstant_nonnegative rowNonnegative columnNonnegative (grade + 2))) (gaugeNonnegative (grade + 2))

theorem radialNumerator_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (row : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 1)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (column : CoefficientFamily L parameters.sigma0 parameters.gamma ell 1 3)
    (rowConstant columnConstant gaugeConstant : ℕ → ℝ)
    (rowNonnegative : ∀ grade, 0 ≤ rowConstant grade) (columnNonnegative : ∀ grade, 0 ≤ columnConstant grade)
    (rowBound : ∀ grade, ‖row grade‖ ≤ rowConstant grade)
    (columnBound : ∀ grade, ‖column grade‖ ≤ columnConstant grade)
    (gaugeBound : ∀ grade, ‖gauge grade‖ ≤ gaugeConstant grade * physicalBudget parameters field rho epsilon (grade + 4))
    (grade : ℕ) :
    ‖radialDivisionFamily admissible (sandwichFamily admissible row gauge column) grade‖ ≤
      numeratorConstant rowConstant columnConstant gaugeConstant grade * physicalBudget parameters field rho epsilon (grade + 6) := by
  apply (radialDivisionFamily_bound admissible _ grade).trans
  have sandwich := sandwichFamily_bound admissible row gauge column rowConstant columnConstant
    rowNonnegative columnNonnegative rowBound columnBound (grade + 2)
  have bound := mul_le_mul_of_nonneg_left (sandwich.trans
    (mul_le_mul_of_nonneg_left (gaugeBound (grade + 2))
      (sandwichConstant_nonnegative rowNonnegative columnNonnegative (grade + 2))))
    (radialDivisionConstant_nonnegative grade)
  simpa only [numeratorConstant, Nat.add_assoc, mul_assoc] using bound

end Grad.GaugeCoefficients.Physical.RadialLedger
