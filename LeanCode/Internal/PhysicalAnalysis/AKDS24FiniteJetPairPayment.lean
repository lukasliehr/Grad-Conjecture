import AKDS21OriginalNewtonHigherBase
import AKDM10OriginalBaseAndEndpointAbsorption
import SRC2OriginalSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCartesianTameEstimate
open Grad.SourceCollarBulk Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.ExhaustionSourceAllocation
open Grad.FlatSourceProjection

/-- The literal finite-jet U/S recovery has a one-high full-source payment
as soon as the covariant full norm is supplied. Its independent zeroth norm
is discharged from the already proved pure-cell endpoint. -/
theorem finiteJetPair_oneHigh_payment (parameters : PhaseParameters) (length : ℝ) (grade loss : ℕ)
    (lossLarge : 20≤loss) (covariantConstant cellZeroConstant : ℝ)
    (covariantNonnegative : 0≤covariantConstant) (cellZeroNonnegative : 0≤cellZeroConstant) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6≤originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 20≤1)
      (potential : ACore parameters 1) (source : SmoothQuotient parameters)
      (covariant vector : ACore parameters 3) (scalar : ACore parameters 1),
      originalGradeNorm grade vector+originalGradeNorm grade scalar ≤
        actualOriginalUSNormConstant parameters length grade *
          (originalGradeNorm grade covariant+
            originalGradeNorm grade (cartesianSourceVector
              (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source))+
            (1+physicalBudget parameters field rho epsilon (5+grade))*originalGradeNorm 0 covariant) →
      originalGradeNorm grade covariant ≤ covariantConstant*
        (‖quotientEta parameters (grade+loss) source‖+
          physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖) →
      originalCellNorm parameters 0 covariant ≤ cellZeroConstant*
        (‖quotientEta parameters 20 source‖+physicalBudget parameters field rho epsilon 20*‖quotientEta parameters 20 source‖) →
      originalGradeNorm grade vector+originalGradeNorm grade scalar ≤ constant*
        (‖quotientEta parameters (grade+loss) source‖+
          physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖) := by
  obtain ⟨residualConstant,residualNonnegative,residualBound⟩ := originalRealFiniteLiftResidual_payment parameters length grade
  refine ⟨|actualOriginalUSNormConstant parameters length grade| *
    (covariantConstant+residualConstant+2*cellZeroConstant),
    mul_nonneg (abs_nonneg _) (by positivity),?_⟩
  intro rho epsilon field low bounded potential source covariant vector scalar recovery covariantBound cellBound
  let payment := ‖quotientEta parameters (grade+loss) source‖+
    physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖
  let residual := originalRealFiniteLiftResidual parameters length rho epsilon field potential low source
  have residualEstimate := residualBound rho epsilon field low
    ((physicalBudget_monotone parameters field rho epsilon (by norm_num : 8≤20)).trans bounded) potential source
  have residualSource := originalSourcePlanar_bound parameters grade (quotientEta parameters grade residual)
  rw [originalSourcePlanar_core,Grad.CartesianState.aGradeEta_norm] at residualSource
  have residualHigh := referenceSource_norm_mono parameters (by omega : grade+12≤grade+loss) source
  have residualLow := mul_le_mul
    (physicalBudget_monotone parameters field rho epsilon (by omega : grade+12≤grade+loss))
    (referenceSource_norm_mono parameters (by omega : 12≤loss) source) (norm_nonneg _)
    (physicalBudget_nonnegative _ _ _ _ _)
  have residualPaid : originalGradeNorm grade (cartesianSourceVector residual) ≤ residualConstant*payment :=
    residualSource.trans (residualEstimate.trans
      (mul_le_mul_of_nonneg_left (add_le_add residualHigh residualLow) residualNonnegative))
  have zeroBound := originalGradeNorm_zero_of_cellTame parameters covariant cellZeroConstant
    ‖quotientEta parameters 20 source‖ (physicalBudget parameters field rho epsilon 20)
    cellZeroNonnegative (norm_nonneg _) bounded cellBound
  have zeroPaid := zeroBound.trans (mul_le_mul_of_nonneg_left
    (referenceSource_norm_mono parameters lossLarge source) (by positivity : 0≤2*cellZeroConstant))
  have budgetMono := physicalBudget_monotone parameters field rho epsilon (by omega : 5+grade≤grade+loss)
  have weighted := mul_le_mul (add_le_add_right budgetMono 1) zeroPaid
    (originalGradeNorm_nonnegative 0 covariant) (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _))
  have sourceMono := referenceSource_norm_mono parameters (by omega : loss≤grade+loss) source
  have lowInside : ‖quotientEta parameters loss source‖+
      physicalBudget parameters field rho epsilon (grade+loss)*‖quotientEta parameters loss source‖ ≤ payment :=
    add_le_add_left sourceMono _
  have zeroPayment : (1+physicalBudget parameters field rho epsilon (5+grade))*originalGradeNorm 0 covariant ≤
      (2*cellZeroConstant)*payment := by
    have paid := mul_le_mul_of_nonneg_left lowInside (by positivity : 0≤2*cellZeroConstant)
    nlinarith only [weighted,paid]
  have insideBound : originalGradeNorm grade covariant+originalGradeNorm grade (cartesianSourceVector residual)+
      (1+physicalBudget parameters field rho epsilon (5+grade))*originalGradeNorm 0 covariant ≤
      (covariantConstant+residualConstant+2*cellZeroConstant)*payment := by
    nlinarith only [covariantBound,residualPaid,zeroPayment]
  have insideNonnegative : 0≤originalGradeNorm grade covariant+originalGradeNorm grade (cartesianSourceVector residual)+
      (1+physicalBudget parameters field rho epsilon (5+grade))*originalGradeNorm 0 covariant := by
    exact add_nonneg (add_nonneg (originalGradeNorm_nonnegative _ _) (originalGradeNorm_nonnegative _ _))
      (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (originalGradeNorm_nonnegative _ _))
  have enlarged := recovery.trans (mul_le_mul_of_nonneg_right
    (le_abs_self (actualOriginalUSNormConstant parameters length grade)) insideNonnegative)
  exact enlarged.trans ((mul_le_mul_of_nonneg_left insideBound (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

end Grad.OriginalCoreRealization
