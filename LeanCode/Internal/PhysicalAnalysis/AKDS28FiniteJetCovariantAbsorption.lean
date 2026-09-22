import AKDS27FiniteJetEndpointPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.RadialLedger

/-- The final CT absorption gives the full norm of the SAME covariant
core, at one fixed loss and on the original state ball. All constants are
selected before the current field and source. -/
theorem finiteJetCovariant_oneHigh_of_planar (parameters : PhaseParameters)
    (shift loss : ℕ) (lossLarge : shift+20≤loss)
    (cellConstants planarConstants : ℕ→ℝ)
    (cellNonnegative : ∀ grade,0≤cellConstants grade)
    (planarNonnegative : ∀ grade,0≤planarConstants grade) :
    ∃ constants : ℕ→ℝ, (∀ grade,0≤constants grade) ∧
      ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (source : SmoothQuotient parameters) (core : ACore parameters 3),
      physicalBudget parameters field rho epsilon 20≤1 →
      (∀ grade,originalCellNorm parameters grade core≤cellConstants grade*
        (‖quotientEta parameters (grade+20) source‖+
          physicalBudget parameters field rho epsilon (grade+20)*‖quotientEta parameters 20 source‖)) →
      (∀ grade,0<grade → originalPlanarNorm parameters grade core≤
        (1/(4*apMassEndpointConstant 0 grade+2))*originalGradeNorm grade core+
        planarConstants grade*(originalCellNorm parameters (grade+shift) core+
          (1+physicalBudget parameters field rho epsilon (grade+shift+20))*originalGradeNorm 0 core+
          ‖quotientEta parameters (grade+shift+20) source‖+
          (1+physicalBudget parameters field rho epsilon (grade+shift+20))*‖quotientEta parameters 20 source‖)) →
      ∀ grade,originalGradeNorm grade core≤constants grade*
        (‖quotientEta parameters (grade+loss) source‖+
          physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖) := by
  let paidConstant := fun grade => cellConstants (grade+shift)+2*cellConstants 0+2
  have paidNonnegative (grade : ℕ) : 0≤paidConstant grade := by
    have first := cellNonnegative (grade+shift)
    have second := cellNonnegative 0
    dsimp only [paidConstant]
    positivity
  let constants := fun grade => if grade=0 then cellConstants 0 else
    (4*apMassEndpointConstant 0 grade)*(planarConstants grade*paidConstant grade+cellConstants grade)
  have nonnegative (grade : ℕ) : 0≤constants grade := by
    dsimp only [constants]
    split
    · exact cellNonnegative 0
    · exact mul_nonneg (mul_nonneg (by norm_num) (apMassEndpointConstant_nonnegative 0 grade))
        (add_nonneg (mul_nonneg (planarNonnegative grade) (paidNonnegative grade)) (cellNonnegative grade))
  refine ⟨constants,nonnegative,?_⟩
  intro rho epsilon field source core bounded cell planar grade
  let payment := ‖quotientEta parameters (grade+loss) source‖+
    physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖
  have cellPaid := finiteJetCell_oneHigh_payment parameters grade loss (by omega) (cellConstants grade)
    (cellNonnegative grade) rho epsilon field source core (cell grade)
  by_cases zero : grade=0
  · subst grade
    rw [originalGradeNorm_zero_eq_cell parameters core]
    simpa only [constants,ite_true] using cellPaid
  · have positive : 0<grade := Nat.pos_of_ne_zero zero
    have endpointPaid := finiteJetEndpoint_oneHigh_payment parameters grade shift loss lossLarge
      cellConstants cellNonnegative rho epsilon field bounded source core cell
    have planarPaid : originalPlanarNorm parameters grade core≤
        (1/(4*apMassEndpointConstant 0 grade+2))*originalGradeNorm grade core+
          (planarConstants grade*paidConstant grade)*payment := by
      have estimate := (planar grade positive).trans
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left endpointPaid (planarNonnegative grade)))
      exact estimate.trans_eq (by rw [mul_assoc])
    have absorbed := originalMixedNorm_absorb_planar parameters grade positive core
      ((planarConstants grade*paidConstant grade)*payment) (cellConstants grade*payment) planarPaid cellPaid
    change originalGradeNorm grade core≤constants grade*payment
    dsimp only [constants]
    rw [if_neg zero]
    exact absorbed.trans_eq (by ring)

end Grad.OriginalCoreRealization
