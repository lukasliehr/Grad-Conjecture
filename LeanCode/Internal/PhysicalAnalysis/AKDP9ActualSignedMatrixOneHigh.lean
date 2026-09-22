import AKDP8SameSignedOriginalNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments Grad.NonlinearProduct Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Genuine positive signed-cell displacement acts on the complementary
moment of the SAME original core. Only one high coefficient times M0
remains after original interpolation. -/
theorem startupDisplacementOriginal_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset grade order : ℕ) (positive : 0<order) (within : order≤grade)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (coefficients reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile coefficients reference)
      (core : ACore parameters input) (family : StartupSignedFamily input L ell),
      family.field = (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖startupDisplacementKernel admissible coefficients estimate.actualCoherent (zeroDerivativeIndex : DerivativeIndex 0) order
        (family.moment (grade-order))‖ ≤ epsilon*originalGradeNorm grade core+
        constant*((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
  let multiplier := startupDerivativeConstant L parameters.sigma0 parameters.gamma (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))*
    (profile.fixed order+profile.deviation order)
  have multiplierNonnegative : 0≤multiplier := mul_nonneg
    (startupDerivativeConstant_nonnegative admissible (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))) (add_nonneg (fixedNonnegative order) (deviationNonnegative order))
  obtain ⟨constant,nonnegative,payment⟩ := originalPositiveOrder_oneHigh offset grade order
    (positive.trans_le within) positive within (epsilon/(multiplier+1)) (div_pos epsilonPositive (by linarith))
  refine ⟨multiplier*constant,mul_nonneg multiplierNonnegative nonnegative,?_⟩
  intro input output baseField rho curvature coefficients reference estimate core family same low
  have inputBound := startupSigned_originalGrade_bound parameters admissible core family same (grade-order)
  have kernel := (startupDisplacementKernel admissible coefficients estimate.actualCoherent (zeroDerivativeIndex : DerivativeIndex 0) order).le_opNorm
    (family.moment (grade-order))
  have normBound : ‖startupDisplacementKernel admissible coefficients estimate.actualCoherent (zeroDerivativeIndex : DerivativeIndex 0) order‖ ≤
      startupDerivativeConstant L parameters.sigma0 parameters.gamma (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))*‖coefficients order‖ := by
    have actual := startupDisplacementKernel_norm admissible coefficients estimate.actualCoherent (zeroDerivativeIndex : DerivativeIndex 0) order
    have identical := congrArg (fun index : ℕ => startupDerivativeConstant L parameters.sigma0 parameters.gamma
      (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))*‖coefficients index‖) (Nat.zero_add order)
    exact actual.trans_eq identical
  have coefficient := estimatedFamily_norm_le estimate order
  have whole : ‖startupDisplacementKernel admissible coefficients estimate.actualCoherent (zeroDerivativeIndex : DerivativeIndex 0) order
      (family.moment (grade-order))‖ ≤ multiplier*
        ((1+physicalBudget parameters baseField rho curvature (offset+order))*originalGradeNorm (grade-order) core) := by
    apply (kernel.trans (mul_le_mul normBound inputBound (norm_nonneg _)
      (mul_nonneg (startupDerivativeConstant_nonnegative admissible (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))) (norm_nonneg _)))).trans
    have result := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left coefficient (startupDerivativeConstant_nonnegative admissible (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))))
      (originalGradeNorm_nonnegative (grade-order) core)
    calc
      _ ≤ startupDerivativeConstant L parameters.sigma0 parameters.gamma (startupCellReserveIndex order (zeroDerivativeIndex : DerivativeIndex 0))*
        ((profile.fixed order+profile.deviation order)*(1+physicalBudget parameters baseField rho curvature (offset+order)))*
        originalGradeNorm (grade-order) core := result
      _ = _ := by dsimp only [multiplier]; ring
  have paid := mul_le_mul_of_nonneg_left (payment input parameters baseField rho curvature core low) multiplierNonnegative
  have leading : multiplier*(epsilon/(multiplier+1))≤epsilon := by
    have ratio : multiplier/(multiplier+1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = epsilon*(multiplier/(multiplier+1)) := by ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  apply (whole.trans paid).trans
  calc
    _ = (multiplier*(epsilon/(multiplier+1)))*originalGradeNorm grade core+(multiplier*constant)*
      ((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right leading (originalGradeNorm_nonnegative grade core)) le_rfl

/-- The literal full binomial signed-cell matrix remainder, with all
positive displacement terms and their original coefficients retained. -/
theorem startupPositiveAxialRemainder_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset power : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (coefficients reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile coefficients reference)
      (core : ACore parameters input) (family : StartupSignedFamily input L ell),
      family.field = (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖startupPositiveAxialRemainder admissible coefficients estimate.actualCoherent power family.moment‖ ≤
        epsilon*originalGradeNorm power core+
        constant*((1+physicalBudget parameters baseField rho curvature (offset+power))*originalGradeNorm 0 core) := by
  classical
  let multiplicity : ℝ := ∑ j : Fin power,(power.choose (j.val+1) : ℝ)
  have multiplicityNonnegative : 0≤multiplicity := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let delta := epsilon/(multiplicity+1)
  have deltaPositive : 0<delta := div_pos epsilonPositive (by linarith)
  have each (j : Fin power) := startupDisplacementOriginal_oneHigh parameters admissible offset power (j.val+1)
    (by omega) (by omega) profile fixedNonnegative deviationNonnegative delta deltaPositive
  choose constants nonnegative estimates using each
  refine ⟨∑ j,(power.choose (j.val+1) : ℝ)*constants j,
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (nonnegative j)),?_⟩
  intro input output baseField rho curvature coefficients reference estimate core family same low
  unfold startupPositiveAxialRemainder
  apply (norm_sum_le _ _).trans
  simp only [norm_smul,Complex.norm_natCast]
  apply (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
    (estimates j input output baseField rho curvature coefficients reference estimate core family same low) (Nat.cast_nonneg _))).trans
  have leading : multiplicity*delta≤epsilon := by
    have ratio : multiplicity/(multiplicity+1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = epsilon*(multiplicity/(multiplicity+1)) := by dsimp only [delta]; ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  calc
    _ = (multiplicity*delta)*originalGradeNorm power core+
      (∑ j : Fin power,(power.choose (j.val+1) : ℝ)*constants j)*
      ((1+physicalBudget parameters baseField rho curvature (offset+power))*originalGradeNorm 0 core) := by
        dsimp only [multiplicity]
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_mul,mul_assoc]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right leading (originalGradeNorm_nonnegative power core)) le_rfl

end Grad.CartesianStartup
