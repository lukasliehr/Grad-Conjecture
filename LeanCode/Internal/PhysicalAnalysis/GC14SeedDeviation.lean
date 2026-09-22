import GC14SeedMatrix
import GC14SeedFourierRecovery

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

theorem seedMatrixDeviation_realizes {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ) :
    RealizesSameCoefficient (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter)
      (seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter) := by
  intro cell point
  change coefficientDerivative (_ + (seedAnisotropic rho : ℂ) • (_ + _)) cell
      (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade) point =
    coefficientDerivative (_ + (seedAnisotropic rho : ℂ) • (_ + _)) cell zeroDerivativeIndex point
  simp only [coefficientDerivative_add_apply, coefficientDerivative_smul_apply]
  rw [seedConstantCell_realizes L sigma gamma ell grade 0 _ cell point,
    seedScalarLift_realizes admissible seedPlusMatrix
      (seedAngleExponential_realizes admissible grade 1 alpha delta parameter) cell point,
    seedScalarLift_realizes admissible seedMinusMatrix
      (seedAngleExponential_realizes admissible grade (-1) alpha delta parameter) cell point]
  rfl

theorem seedMatrixDeviation_cell {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (rho alpha delta parameter : ℝ) (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative (seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter)
        cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt grade) point =
      seedDeviationCell rho alpha delta parameter cell := by
  rw [seedMatrixDeviation_realizes admissible grade rho alpha delta parameter cell point]
  rw [← seedCoefficient_integral admissible _ point cell]
  simp_rw [seedMatrixDeviation_fourier]
  rfl

def seedDeviationConstant (sigma radius : ℝ) (grade : ℕ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) +
    (seedScalarLiftConstant grade seedPlusMatrix + seedScalarLiftConstant grade seedMinusMatrix) *
      seedExponentialConstant sigma radius grade

theorem seedDeviationConstant_nonnegative (sigma radius : ℝ) (grade : ℕ) :
    0 ≤ seedDeviationConstant sigma radius grade := by
  unfold seedDeviationConstant seedExponentialConstant
  exact add_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (add_nonneg (seedScalarLiftConstant_nonnegative _ _)
      (seedScalarLiftConstant_nonnegative _ _)) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le))

theorem seedMatrixDeviation_norm_le {L sigma gamma ell radius rho alpha delta parameter : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (radiusNonnegative : 0 ≤ radius) (rhoSmall : |rho| ≤ 1)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) :
    ‖seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ ≤
      seedDeviationConstant sigma radius grade * |rho| := by
  have factors := seed_shape_factors_bound rhoSmall
  have plusBound := seedAngleExponential_norm_le admissible grade radiusNonnegative
    (show |(1 : ℝ)| ≤ 1 by norm_num) alphaSmall deltaSmall parameterSmall
  have minusBound := seedAngleExponential_norm_le admissible grade radiusNonnegative
    (show |(-1 : ℝ)| ≤ 1 by norm_num) alphaSmall deltaSmall parameterSmall
  have identityBound :
      ‖((seedIsotropic rho - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2)‖ ≤ |rho| := by
    calc
      _ ≤ ‖((seedIsotropic rho - 1 : ℝ) : ℂ)‖ * ‖ContinuousLinearMap.id ℂ (ComplexEuclidean 2)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖((seedIsotropic rho - 1 : ℝ) : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = |seedIsotropic rho - 1| := by rw [mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := factors.1
  have zerothBound := (seedZeroCell_norm_le admissible
    (((seedIsotropic rho - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2))).trans
      (mul_le_mul_of_nonneg_left identityBound (Nat.cast_nonneg (Fintype.card (DerivativeIndex grade))))
  have plusLift := (seedScalarLift_norm_le admissible seedPlusMatrix
    (seedAngleExponential admissible grade 1 alpha delta parameter)).trans
      (mul_le_mul_of_nonneg_left plusBound (seedScalarLiftConstant_nonnegative _ _))
  have minusLift := (seedScalarLift_norm_le admissible seedMinusMatrix
    (seedAngleExponential admissible grade (-1) alpha delta parameter)).trans
      (mul_le_mul_of_nonneg_left minusBound (seedScalarLiftConstant_nonnegative _ _))
  have scalarBound : ‖(seedAnisotropic rho : ℂ)‖ ≤ |rho| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact factors.2
  unfold seedMatrixDeviationCoefficient
  calc
    _ ≤ ‖seedConstantCell L sigma gamma ell grade 0 _‖ +
        ‖(seedAnisotropic rho : ℂ) • (_ + _)‖ := norm_add_le _ _
    _ ≤ (Fintype.card (DerivativeIndex grade) : ℝ) * |rho| +
        |rho| * (seedScalarLiftConstant grade seedPlusMatrix * seedExponentialConstant sigma radius grade +
          seedScalarLiftConstant grade seedMinusMatrix * seedExponentialConstant sigma radius grade) := by
      apply add_le_add zerothBound
      exact (coefficientScalarNorm_le _ _).trans (mul_le_mul scalarBound
        ((norm_add_le _ _).trans (add_le_add plusLift minusLift)) (norm_nonneg _) (abs_nonneg rho))
    _ = _ := by unfold seedDeviationConstant; ring

end Grad.GaugeCoefficients.Physical.Frame
