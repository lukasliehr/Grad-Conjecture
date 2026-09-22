import AKDP44ActualSignedPureCellNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger

/-- The same actual matrix has an adjustable pure-cell endpoint: its
leading action pays only the input cell norm, while every positive cell
displacement pays epsilon times the full norm plus one high base term. -/
theorem startupEstimatedMatrix_cellAdjustable (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (offset grade : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade) :
    ∃ leading : ℝ,0≤leading ∧ ∀ epsilon : ℝ,0<epsilon →
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (coefficients reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile coefficients reference)
      (core : ACore parameters input) (family : StartupSignedFamily input L ell) (image : ACore parameters output),
      family.field=(originalSourceMoments parameters core).field →
      (originalSourceMoments parameters image).field=
        originalMatrixKernel admissible coefficients estimate.actualCoherent (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      originalCellNorm parameters grade image≤leading*originalCellNorm parameters grade core+
        epsilon*originalGradeNorm grade core+
        constant*((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
  classical
  let baseBound := startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma profile
  have baseNonnegative : 0≤baseBound := startupMatrixProfileBaseBound_nonnegative admissible profile fixedNonnegative deviationNonnegative
  let weights := fun power : Fin (grade+1) => Real.sqrt (grade.choose power.val : ℝ)*‖((((ell/L : ℝ) : ℂ)⁻¹)^power.val)‖
  have weightsNonnegative (power : Fin (grade+1)) : 0≤weights power := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  let mass : ℝ := ∑ power,weights power
  have massNonnegative : 0≤mass := Finset.sum_nonneg (fun power _ => weightsNonnegative power)
  refine ⟨mass*baseBound,mul_nonneg massNonnegative baseNonnegative,?_⟩
  intro epsilon positive
  let delta := epsilon/(mass+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  have each (power : Fin (grade+1)) := startupPositiveAxialRemainder_oneHigh parameters admissible offset power.val profile
    fixedNonnegative deviationNonnegative delta deltaPositive
  choose constants nonnegative estimates using each
  refine ⟨∑ power,weights power*constants power,
    Finset.sum_nonneg (fun power _ => mul_nonneg (weightsNonnegative power) (nonnegative power)),?_⟩
  intro input output baseField rho curvature coefficients reference estimate core family image same imageSame low
  let mapped := family.matrix admissible coefficients estimate.actualCoherent
  have mappedSame : mapped.field=(originalSourceMoments parameters image).field := by
    change originalMatrixKernel admissible coefficients estimate.actualCoherent family.field=_
    rw [same,←imageSame]
  have natural := startupOriginalCellNorm_le_signed parameters lengthNonzero scaleNonzero image mapped mappedSame grade
  apply natural.trans
  change (∑ power : Fin (grade+1),weights power*‖mapped.moment power.val‖)≤_
  have eachBound (power : Fin (grade+1)) : ‖mapped.moment power.val‖≤
      baseBound*originalCellNorm parameters grade core+delta*originalGradeNorm grade core+
      constants power*((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
    have powerLe : power.val≤grade := by omega
    change ‖startupKernelAxialMoment admissible coefficients estimate.actualCoherent zeroDerivativeIndex power.val family.moment‖≤_
    rw [startupKernelAxialMoment_leadingSplit]
    apply (norm_add_le _ _).trans
    have main := ((originalMatrixKernel admissible coefficients estimate.actualCoherent).le_opNorm _).trans
      (mul_le_mul (startupEstimatedMatrix_lowNorm parameters admissible estimate low)
        (startupSigned_originalCell_bound parameters admissible core family same grade power.val powerLe) (norm_nonneg _) baseNonnegative)
    have lower := estimates power input output baseField rho curvature coefficients reference estimate core family same low
    have derivative := mul_le_mul_of_nonneg_left (originalGradeNorm_mono powerLe core) deltaPositive.le
    have coefficient := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (add_le_add_right (physicalBudget_monotone parameters baseField rho curvature
          (by omega : offset+power.val≤offset+grade)) 1) (originalGradeNorm_nonnegative 0 core)) (nonnegative power)
    exact (add_le_add main (lower.trans (add_le_add derivative coefficient))).trans_eq (add_assoc _ _ _).symm
  have leadingBound : mass*delta≤epsilon := by
    have exactMass : delta*(mass+1)=epsilon := div_mul_cancel₀ epsilon (by positivity : mass+1≠0)
    nlinarith [deltaPositive]
  calc
    _ ≤ ∑ power : Fin (grade+1),weights power*(baseBound*originalCellNorm parameters grade core+
        delta*originalGradeNorm grade core+
        constants power*((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core)) :=
      Finset.sum_le_sum (fun power _ => mul_le_mul_of_nonneg_left (eachBound power) (weightsNonnegative power))
    _ = (mass*baseBound)*originalCellNorm parameters grade core+(mass*delta)*originalGradeNorm grade core+
        (∑ power,weights power*constants power)*
          ((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
      simp only [mul_add,Finset.sum_add_distrib,←mul_assoc,←Finset.sum_mul,mass]
    _ ≤ _ := add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right leadingBound (originalGradeNorm_nonnegative grade core))) le_rfl

end Grad.CartesianStartup
