import GQC55CoefficientGradeBound

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem radial_sandwich_coefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (row : CoefficientFamily L sigma gamma ell 3 1) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (column : CoefficientFamily L sigma gamma ell 1 3) (rowC columnC : ℕ → ℝ)
    (rowNonnegative : ∀ q, 0 ≤ rowC q) (columnNonnegative : ∀ q, 0 ≤ columnC q)
    (rowBound : ∀ q, ‖row q‖ ≤ rowC q) (columnBound : ∀ q, ‖column q‖ ≤ columnC q) (grade : ℕ) :
    ‖radialDivisionFamily admissible (sandwichFamily admissible row gauge column) grade‖ ≤
      numeratorConstant rowC columnC (fun _ => 1) grade * ‖gauge (grade + 2)‖ := by
  have bound := (radialDivisionFamily_bound admissible (sandwichFamily admissible row gauge column) grade).trans
    (mul_le_mul_of_nonneg_left
      (sandwichFamily_bound admissible row gauge column rowC columnC rowNonnegative columnNonnegative rowBound columnBound (grade + 2))
      (radialDivisionConstant_nonnegative grade))
  exact bound.trans_eq (by unfold numeratorConstant; ring)

theorem muDeviation_coefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    ‖muDeviation admissible gauge grade‖ ≤ muConstant (fun _ => 1) grade * ‖gauge (grade + 2)‖ :=
  radial_sandwich_coefficient_bound admissible _ gauge _ tangentRowConstant tangentColumnConstant
    tangentRowConstant_nonnegative tangentColumnConstant_nonnegative (tangentRow_bound L sigma gamma ell)
    (tangentColumn_bound L sigma gamma ell) grade

theorem eta_coefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    ‖etaCoefficient admissible gauge grade‖ ≤ etaConstant (fun _ => 1) grade * ‖gauge (grade + 2)‖ :=
  radial_sandwich_coefficient_bound admissible _ gauge _ tangentRowConstant scalarColumnConstant
    tangentRowConstant_nonnegative scalarColumnConstant_nonnegative (tangentRow_bound L sigma gamma ell)
    (scalarColumn_bound admissible) grade

theorem nu_coefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) :
    ‖nuCoefficient admissible gauge grade‖ ≤ nuConstant (fun _ => 1) grade * ‖gauge (grade + 2)‖ :=
  radial_sandwich_coefficient_bound admissible _ gauge _ scalarRowConstant tangentColumnConstant
    scalarRowConstant_nonnegative tangentColumnConstant_nonnegative (scalarRow_bound admissible)
    (tangentColumn_bound L sigma gamma ell) grade

def deltaDirectConstant (grade : ℕ) : ℝ :=
  deltaConstant (fun _ => 1) grade * Fintype.card (DerivativeIndex grade)

theorem deltaDirectConstant_nonnegative (grade : ℕ) : 0 ≤ deltaDirectConstant grade :=
  mul_nonneg (deltaConstant_nonnegative (fun _ => zero_le_one) grade) (Nat.cast_nonneg _)

theorem deltaDeviation_coefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) :
    ‖deltaDeviation admissible gauge grade‖ ≤ deltaDirectConstant grade * ‖gauge (grade + 2)‖ := by
  have angularNonnegative : 0 ≤ angularBound grade := by unfold angularBound; positivity
  have sandwich := sandwichFamily_bound admissible _ gauge _ scalarRowConstant scalarColumnConstant
    scalarRowConstant_nonnegative scalarColumnConstant_nonnegative (scalarRow_bound admissible) (scalarColumn_bound admissible) grade
  have bound := (coefficientAngular_bound L sigma gamma ell grade 1 1 _).trans
    (mul_le_mul_of_nonneg_left sandwich angularNonnegative)
  have sameGrade : ‖deltaDeviation admissible gauge grade‖ ≤ deltaConstant (fun _ => 1) grade * ‖gauge grade‖ :=
    bound.trans_eq (by unfold deltaConstant; ring)
  exact sameGrade.trans ((mul_le_mul_of_nonneg_left (coherent_coefficient_grade_bound gauge coherent (by omega : grade ≤ grade + 2))
    (deltaConstant_nonnegative (fun _ => zero_le_one) grade)).trans_eq (by unfold deltaDirectConstant; ring))

end Grad.GaugeCoefficients.Physical.Compensated
