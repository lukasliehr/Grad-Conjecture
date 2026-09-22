import AKH1ActualPhaseSlopeJets
import AKC7FiniteOrderIntervalSeries
import AKC8FourierMatrixPoint
import AAZJ4TwoExtraGradeSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped ContDiff BigOperators Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.SourceCollarCoefficients

def phaseSlopeDiagonalTerm (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  (iteratedDeriv rank (annularPhaseSlope parameters mode.2) radius *
    (annularFrequency mode.1 mode.2 ^ reserve)⁻¹) •
      fourierMatrixPoint mode mode (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))

theorem phaseSlopeDiagonalTerm_smooth (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (mode : ℤ × ℤ) : ContDiff ℝ ∞ (phaseSlopeDiagonalTerm parameters dimension reserve rank mode) :=
  ((smoothCurve_iteratedDeriv_smooth _ (annularPhaseSlope_smooth parameters mode.2) rank).mul
    contDiff_const).smul contDiff_const

theorem phaseSlopeDiagonalTerm_hasDerivAt (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) :
    HasDerivAt (phaseSlopeDiagonalTerm parameters dimension reserve rank mode)
      (phaseSlopeDiagonalTerm parameters dimension reserve (rank + 1) mode radius) radius := by
  exact ((smoothCurve_iteratedDeriv_hasDerivAt _ (annularPhaseSlope_smooth parameters mode.2)
    rank radius).mul_const (annularFrequency mode.1 mode.2 ^ reserve)⁻¹).smul_const
      (fourierMatrixPoint mode mode (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)))

theorem phaseSlopeDiagonalTerm_bound (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (enough : rank + 5 ≤ reserve) (mode : ℤ × ℤ) (radius : ℝ) :
    ‖phaseSlopeDiagonalTerm parameters dimension reserve rank mode radius‖ ≤
      phaseSlopeJetConstant parameters rank * (annularFrequency mode.1 mode.2 ^ 4)⁻¹ := by
  have frequencyPositive : 0 < annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    positivity
  have frequencyOne : 1 ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  have reserveBound : annularFrequency mode.1 mode.2 ^ (rank + 1) *
      (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ ≤
        (annularFrequency mode.1 mode.2 ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (pow_pos frequencyPositive _) (pow_pos frequencyPositive _)]
    simpa only [← pow_add, one_mul] using (pow_le_pow_right₀ frequencyOne enough)
  unfold phaseSlopeDiagonalTerm
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))]
  calc
    _ ≤ (phaseSlopeJetConstant parameters rank * annularFrequency mode.1 mode.2 ^ (rank + 1)) *
        (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (annularPhaseSlope_iterated_bound parameters mode rank radius)
          (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))
      · exact (fourierMatrixPoint_bound mode mode _).trans ContinuousLinearMap.norm_id_le
      · exact norm_nonneg _
      · exact mul_nonneg (mul_nonneg (phaseSlopeJetConstant_nonnegative parameters rank)
          (pow_nonneg frequencyPositive.le _)) (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))
    _ ≤ _ := by
      rw [mul_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left reserveBound (phaseSlopeJetConstant_nonnegative parameters rank)

theorem phaseSlopeDiagonalTerm_summable (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (enough : rank + 5 ≤ reserve) (radius : ℝ) :
    Summable (fun mode => phaseSlopeDiagonalTerm parameters dimension reserve rank mode radius) :=
  Summable.of_norm_bounded
    (Grad.AnnularJointRegularity.annularLattice_inverse_four_summable.mul_left _)
    (fun mode => phaseSlopeDiagonalTerm_bound parameters dimension reserve rank enough mode radius)

def phaseSlopeDiagonal (parameters : PhaseParameters) (dimension reserve : ℕ) (radius : ℝ) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  ∑' mode, phaseSlopeDiagonalTerm parameters dimension reserve 0 mode radius

theorem phaseSlopeDiagonal_contDiffOn (parameters : PhaseParameters) (dimension reserve order : ℕ)
    (enough : order + 5 ≤ reserve) (lower upper : ℝ) (ordered : lower < upper) :
    ContDiffOn ℝ order (phaseSlopeDiagonal parameters dimension reserve) (Icc lower upper) := by
  apply intervalSeries_contDiffOn_order lower upper ordered order
    (phaseSlopeDiagonalTerm parameters dimension reserve)
    (fun rank _ mode => (phaseSlopeDiagonalTerm_smooth parameters dimension reserve rank mode).continuous.continuousOn)
    (fun rank _ mode radius _ => phaseSlopeDiagonalTerm_hasDerivAt parameters dimension reserve rank mode radius)
    (fun rank mode => phaseSlopeJetConstant parameters rank * (annularFrequency mode.1 mode.2 ^ 4)⁻¹)
    (fun _ _ => Grad.AnnularJointRegularity.annularLattice_inverse_four_summable.mul_left _)
  intro rank valid mode radius _
  exact phaseSlopeDiagonalTerm_bound parameters dimension reserve rank (by omega) mode radius

end Grad.AnnularWeightedSmoothness
