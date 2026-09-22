import AKDS28FiniteJetCovariantAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.RadialLedger

/-- The Bessel estimate is required only from rank two. Monotonicity pays
the two lowest grades with one fixed additional loss, on the same state ball. -/
theorem finiteJetCore_oneHigh_of_planar_ge_two (parameters : PhaseParameters)
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
      (∀ grade,2≤grade → originalPlanarNorm parameters grade core≤
        (1/(4*apMassEndpointConstant 0 grade+2))*originalGradeNorm grade core+
        planarConstants grade*(originalCellNorm parameters (grade+shift) core+
          (1+physicalBudget parameters field rho epsilon (grade+shift+20))*originalGradeNorm 0 core+
          ‖quotientEta parameters (grade+shift+20) source‖+
          (1+physicalBudget parameters field rho epsilon (grade+shift+20))*‖quotientEta parameters 20 source‖)) →
      ∀ grade,originalGradeNorm grade core≤constants grade*
        (‖quotientEta parameters (grade+(loss+2)) source‖+
          physicalBudget parameters field rho epsilon (grade+(loss+2))*‖quotientEta parameters (loss+2) source‖) := by
  let paidConstant := fun grade => cellConstants (grade+shift)+2*cellConstants 0+2
  have paidNonnegative (grade : ℕ) : 0≤paidConstant grade := by
    have first := cellNonnegative (grade+shift)
    have second := cellNonnegative 0
    dsimp only [paidConstant]
    positivity
  let highConstant := fun grade => (4*apMassEndpointConstant 0 grade)*
    (planarConstants grade*paidConstant grade+cellConstants grade)
  have highNonnegative (grade : ℕ) : 0≤highConstant grade :=
    mul_nonneg (mul_nonneg (by norm_num) (apMassEndpointConstant_nonnegative 0 grade))
      (add_nonneg (mul_nonneg (planarNonnegative grade) (paidNonnegative grade)) (cellNonnegative grade))
  refine ⟨(fun grade => highConstant (max grade 2)),(fun grade => highNonnegative _),?_⟩
  intro rho epsilon field source core bounded cell planar grade
  let rank := max grade 2
  have rankLarge : 2≤rank := le_max_right _ _
  have rankLe : rank≤grade+2 := by dsimp only [rank]; omega
  let payment := ‖quotientEta parameters (rank+loss) source‖+
    physicalBudget parameters field rho epsilon (rank+loss)*‖quotientEta parameters loss source‖
  have cellPaid := finiteJetCell_oneHigh_payment parameters rank loss (by omega) (cellConstants rank)
    (cellNonnegative rank) rho epsilon field source core (cell rank)
  have endpointPaid := finiteJetEndpoint_oneHigh_payment parameters rank shift loss lossLarge
    cellConstants cellNonnegative rho epsilon field bounded source core cell
  have planarPaid : originalPlanarNorm parameters rank core≤
      (1/(4*apMassEndpointConstant 0 rank+2))*originalGradeNorm rank core+
        (planarConstants rank*paidConstant rank)*payment := by
    have estimate := (planar rank rankLarge).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left endpointPaid (planarNonnegative rank)))
    exact estimate.trans_eq (by rw [mul_assoc])
  have absorbed := originalMixedNorm_absorb_planar parameters rank (by omega) core
    ((planarConstants rank*paidConstant rank)*payment) (cellConstants rank*payment) planarPaid cellPaid
  have high : originalGradeNorm rank core≤highConstant rank*payment :=
    absorbed.trans_eq (by dsimp only [highConstant]; ring)
  have paymentLe : payment≤‖quotientEta parameters (grade+(loss+2)) source‖+
      physicalBudget parameters field rho epsilon (grade+(loss+2))*‖quotientEta parameters (loss+2) source‖ :=
    add_le_add (referenceSource_norm_mono parameters (by omega : rank+loss≤grade+(loss+2)) source)
      (mul_le_mul (physicalBudget_monotone parameters field rho epsilon (by omega : rank+loss≤grade+(loss+2)))
        (referenceSource_norm_mono parameters (by omega : loss≤loss+2) source) (norm_nonneg _)
        (physicalBudget_nonnegative _ _ _ _ _))
  exact (originalGradeNorm_mono (le_max_left grade 2) core).trans
    (high.trans (mul_le_mul_of_nonneg_left paymentLe (highNonnegative rank)))

end Grad.OriginalCoreRealization
