import AKDP11SameOriginalCellBinomial
import AKDP9ActualSignedMatrixOneHigh
import AKDP12ActualMatrixBaseAndInputBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments Grad.NonlinearProduct Grad.OriginalCartesianTameEstimate
open Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- No-loss pure-cell endpoint for the SAME original matrix image. Every
positive binomial displacement is paid against the complementary genuine
input moment; no high coefficient multiplies a high unknown. -/
theorem startupEstimatedMatrix_cellEndpoint (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (offset grade : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (coefficients reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile coefficients reference)
      (core : ACore parameters input) (family : StartupSignedFamily input L ell) (image : ACore parameters output),
      family.field = (originalSourceMoments parameters core).field →
      (originalSourceMoments parameters image).field =
        originalMatrixKernel admissible coefficients estimate.actualCoherent (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      originalCellNorm parameters grade image ≤ constant*(originalGradeNorm grade core+
        (1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
  classical
  let baseBound := startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma profile
  have baseNonnegative : 0≤baseBound := startupMatrixProfileBaseBound_nonnegative admissible profile fixedNonnegative deviationNonnegative
  let weights := fun power : Fin (grade+1) => Real.sqrt (grade.choose power.val : ℝ)*‖((((ell/L : ℝ) : ℂ)⁻¹)^power.val)‖
  have weightsNonnegative (power : Fin (grade+1)) : 0≤weights power := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have each (power : Fin (grade+1)) := startupPositiveAxialRemainder_oneHigh parameters admissible offset power.val profile
    fixedNonnegative deviationNonnegative 1 zero_lt_one
  choose constants nonnegative estimates using each
  refine ⟨∑ power,weights power*(baseBound+1+constants power),
    Finset.sum_nonneg (fun power _ => mul_nonneg (weightsNonnegative power) (by linarith [nonnegative power])),?_⟩
  intro input output baseField rho curvature coefficients reference estimate core family image same imageSame low
  let mapped := family.matrix admissible coefficients estimate.actualCoherent
  have mappedSame : mapped.field = (originalSourceMoments parameters image).field := by
    change originalMatrixKernel admissible coefficients estimate.actualCoherent family.field = _
    rw [same,← imageSame]
  have natural := startupOriginalCellNorm_le_signed parameters lengthNonzero scaleNonzero image mapped mappedSame grade
  apply natural.trans
  change (∑ power : Fin (grade+1),weights power*‖mapped.moment power.val‖) ≤ _
  have bound (power : Fin (grade+1)) : ‖mapped.moment power.val‖ ≤
      (baseBound+1+constants power)*(originalGradeNorm grade core+
        (1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
    have powerLe : power.val≤grade := by omega
    change ‖startupKernelAxialMoment admissible coefficients estimate.actualCoherent zeroDerivativeIndex power.val family.moment‖ ≤ _
    rw [startupKernelAxialMoment_leadingSplit]
    apply (norm_add_le _ _).trans
    have inputBound := (startupSigned_originalGrade_bound parameters admissible core family same power.val).trans
      (originalGradeNorm_mono powerLe core)
    have main := ((originalMatrixKernel admissible coefficients estimate.actualCoherent).le_opNorm _).trans
      (mul_le_mul (startupEstimatedMatrix_lowNorm parameters admissible estimate low) inputBound (norm_nonneg _) baseNonnegative)
    have lower := estimates power input output baseField rho curvature coefficients reference estimate core family same low
    have coreBound := originalGradeNorm_mono powerLe core
    have coefficientBound := physicalBudget_monotone parameters baseField rho curvature (by omega : offset+power.val≤offset+grade)
    have tailBound := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (add_le_add_right coefficientBound 1) (originalGradeNorm_nonnegative 0 core)) (nonnegative power)
    have paid := add_le_add main (lower.trans (add_le_add (by simpa only [one_mul] using coreBound) tailBound))
    apply paid.trans
    have highNonnegative := mul_nonneg (add_nonneg zero_le_one
      (physicalBudget_nonnegative parameters baseField rho curvature (offset+grade))) (originalGradeNorm_nonnegative 0 core)
    have first := mul_nonneg (nonnegative power) (originalGradeNorm_nonnegative grade core)
    have second := mul_nonneg (show 0≤baseBound+1 by linarith) highNonnegative
    nlinarith only [first,second]
  apply (Finset.sum_le_sum (fun power _ => mul_le_mul_of_nonneg_left (bound power) (weightsNonnegative power))).trans_eq
  simp only [Finset.sum_mul,mul_assoc]

end Grad.CartesianStartup
