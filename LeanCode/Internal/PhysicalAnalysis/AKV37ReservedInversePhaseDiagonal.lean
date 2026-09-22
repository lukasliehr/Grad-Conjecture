import AKV36InversePhaseRadialJets
import AKC7FiniteOrderIntervalSeries
import AKC8FourierMatrixPoint
import AAZJ4TwoExtraGradeSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped ContDiff BigOperators Topology
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.SourceCollarCoefficients

def inversePhaseDiagonalTerm (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  (iteratedDeriv rank (inversePhaseCurve parameters mode.2) radius *
    (annularFrequency mode.1 mode.2 ^ reserve)⁻¹) •
      fourierMatrixPoint mode mode (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))

theorem inversePhaseDiagonalTerm_smooth (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (mode : ℤ × ℤ) : ContDiff ℝ ∞ (inversePhaseDiagonalTerm parameters dimension reserve rank mode) :=
  ((smoothCurve_iteratedDeriv_smooth _ (inversePhaseCurve_smooth parameters mode.2) rank).mul
    contDiff_const).smul contDiff_const

theorem inversePhaseDiagonalTerm_hasDerivAt (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) :
    HasDerivAt (inversePhaseDiagonalTerm parameters dimension reserve rank mode)
      (inversePhaseDiagonalTerm parameters dimension reserve (rank + 1) mode radius) radius := by
  exact ((smoothCurve_iteratedDeriv_hasDerivAt _ (inversePhaseCurve_smooth parameters mode.2)
    rank radius).mul_const (annularFrequency mode.1 mode.2 ^ reserve)⁻¹).smul_const
      (fourierMatrixPoint mode mode (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)))

theorem inversePhaseDiagonalTerm_bound (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (enough : rank + 4 ≤ reserve) (mode : ℤ × ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖inversePhaseDiagonalTerm parameters dimension reserve rank mode radius‖ ≤
      inversePhaseJetConstant parameters rank * (annularFrequency mode.1 mode.2 ^ 4)⁻¹ := by
  have frequencyPositive : 0 < annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    positivity
  have frequencyOne : 1 ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  have reserveBound : annularFrequency mode.1 mode.2 ^ rank *
      (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ ≤
        (annularFrequency mode.1 mode.2 ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (pow_pos frequencyPositive _) (pow_pos frequencyPositive _)]
    simpa only [← pow_add, one_mul] using (pow_le_pow_right₀ frequencyOne enough)
  unfold inversePhaseDiagonalTerm
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))]
  calc
    _ ≤ (inversePhaseJetConstant parameters rank * annularFrequency mode.1 mode.2 ^ rank) *
        (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (inversePhaseCurve_iterated_bound parameters mode rank radius nonnegative bounded)
          (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))
      · exact (fourierMatrixPoint_bound mode mode _).trans ContinuousLinearMap.norm_id_le
      · exact norm_nonneg _
      · exact mul_nonneg (mul_nonneg (inversePhaseJetConstant_nonnegative parameters rank)
          (pow_nonneg frequencyPositive.le _)) (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))
    _ ≤ _ := by
      rw [mul_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left reserveBound (inversePhaseJetConstant_nonnegative parameters rank)

theorem inversePhaseDiagonalTerm_summable (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (enough : rank + 4 ≤ reserve) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (fun mode => inversePhaseDiagonalTerm parameters dimension reserve rank mode radius) :=
  Summable.of_norm_bounded
    (Grad.AnnularJointRegularity.annularLattice_inverse_four_summable.mul_left _)
    (fun mode => inversePhaseDiagonalTerm_bound parameters dimension reserve rank enough mode radius nonnegative bounded)

def inversePhaseDiagonal (parameters : PhaseParameters) (dimension reserve : ℕ) (radius : ℝ) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  ∑' mode, inversePhaseDiagonalTerm parameters dimension reserve 0 mode radius

theorem inversePhaseDiagonal_contDiffOn (parameters : PhaseParameters) (dimension reserve order : ℕ)
    (enough : order + 4 ≤ reserve) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    ContDiffOn ℝ order (inversePhaseDiagonal parameters dimension reserve) (Icc lower 1) := by
  apply intervalSeries_contDiffOn_order lower 1 bounded order
    (inversePhaseDiagonalTerm parameters dimension reserve)
    (fun rank _ mode => (inversePhaseDiagonalTerm_smooth parameters dimension reserve rank mode).continuous.continuousOn)
    (fun rank _ mode radius _ => inversePhaseDiagonalTerm_hasDerivAt parameters dimension reserve rank mode radius)
    (fun rank mode => inversePhaseJetConstant parameters rank * (annularFrequency mode.1 mode.2 ^ 4)⁻¹)
    (fun _ _ => Grad.AnnularJointRegularity.annularLattice_inverse_four_summable.mul_left _)
  intro rank valid mode radius inside
  exact inversePhaseDiagonalTerm_bound parameters dimension reserve rank (by omega) mode radius (positive.le.trans inside.1) inside.2

end Grad.AnnularGeneralSourceRegularity
