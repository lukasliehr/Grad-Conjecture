import GC14SeedScalarLift

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def seedCosineMatrix : OperatorValue 2 2 :=
  matrixEmbedding 2 2 (WithLp.toLp 2 ![1, 0, 0, -1])

def seedSineMatrix : OperatorValue 2 2 :=
  matrixEmbedding 2 2 (WithLp.toLp 2 ![0, 1, 1, 0])

def seedPlusMatrix : OperatorValue 2 2 :=
  (1 / 2 : ℂ) • (seedCosineMatrix - Complex.I • seedSineMatrix)

def seedMinusMatrix : OperatorValue 2 2 :=
  (1 / 2 : ℂ) • (seedCosineMatrix + Complex.I • seedSineMatrix)

theorem seedSplitMatrix_formula (angle : ℝ) :
    Complex.exp (2 * Complex.I * angle) • seedPlusMatrix +
      Complex.exp (-2 * Complex.I * angle) • seedMinusMatrix =
      (Real.cos (2 * angle) : ℂ) • seedCosineMatrix +
        (Real.sin (2 * angle) : ℂ) • seedSineMatrix := by
  have positivePhase := seedLaurentPhase 2 angle
  have negativePhase := seedLaurentPhase (-2) angle
  have positiveIdentity : fourierPhase 2 angle = Complex.exp (2 * Complex.I * angle) := by
    unfold fourierPhase
    congr 1
    push_cast
    ring
  have negativeIdentity : fourierPhase (-2) angle = Complex.exp (-2 * Complex.I * angle) := by
    unfold fourierPhase
    congr 1
    push_cast
    ring
  rw [positiveIdentity] at positivePhase
  rw [negativeIdentity] at negativePhase
  norm_num only [Int.cast_ofNat, Int.cast_neg] at positivePhase negativePhase
  rw [positivePhase, negativePhase]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  unfold seedPlusMatrix seedMinusMatrix
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [add_apply, smul_apply, sub_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

def seedMatrixDeviationCoefficient {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (rho alpha delta parameter : ℝ) : Coefficient L sigma gamma ell grade 2 2 :=
  seedConstantCell L sigma gamma ell grade 0
      (((seedIsotropic rho - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) +
    (seedAnisotropic rho : ℂ) •
      (seedScalarLift admissible seedPlusMatrix (seedAngleExponential admissible grade 1 alpha delta parameter) +
        seedScalarLift admissible seedMinusMatrix (seedAngleExponential admissible grade (-1) alpha delta parameter))

theorem seedMatrixDeviation_fourier_formula {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rho alpha delta parameter angle : ℝ)
    (point : ClosedDisk) :
    fourierEvaluation (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) angle point =
      (((seedIsotropic rho - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) +
        (seedAnisotropic rho : ℂ) •
          ((Real.cos (2 * Grad.GeometryClosure.seedAngle alpha delta parameter angle) : ℂ) • seedCosineMatrix +
            (Real.sin (2 * Grad.GeometryClosure.seedAngle alpha delta parameter angle) : ℂ) • seedSineMatrix) := by
  change seedFourierCLM admissible 2 2 angle point (_ + (seedAnisotropic rho : ℂ) • (_ + _)) = _
  rw [map_add, map_smul, map_add]
  change fourierEvaluation (seedConstantCell L sigma gamma ell 0 0 _) angle point +
    (seedAnisotropic rho : ℂ) •
      (fourierEvaluation (seedScalarLift admissible seedPlusMatrix _) angle point +
        fourierEvaluation (seedScalarLift admissible seedMinusMatrix _) angle point) = _
  rw [seedConstantCell_fourier,
    seedScalarLift_fourier admissible _ _ angle point _ (seedAngleExponential_fourier admissible 1 _ _ _ _ _),
    seedScalarLift_fourier admissible _ _ angle point _ (seedAngleExponential_fourier admissible (-1) _ _ _ _ _)]
  norm_num only [fourierPhase, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_smul,
    Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul]
  have split := seedSplitMatrix_formula (Grad.GeometryClosure.seedAngle alpha delta parameter angle)
  simp only [neg_mul] at split
  rw [split]

theorem seedOperator_double_angle (rho alpha delta parameter angle : ℝ) :
    harmonicSeedOperator rho alpha delta parameter angle =
      (seedIsotropic rho : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2) +
        (seedAnisotropic rho : ℂ) •
          ((Real.cos (2 * Grad.GeometryClosure.seedAngle alpha delta parameter angle) : ℂ) • seedCosineMatrix +
            (Real.sin (2 * Grad.GeometryClosure.seedAngle alpha delta parameter angle) : ℂ) • seedSineMatrix) := by
  unfold harmonicSeedOperator
  rw [seed_harmonic_double_angle]
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [add_apply, smul_apply, PiLp.add_apply, PiLp.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  change matrixEmbedding 2 2 _ vector coordinate = _
  rw [matrixEmbedding_apply]
  unfold seedCosineMatrix seedSineMatrix
  rw [matrixEmbedding_apply, matrixEmbedding_apply]
  fin_cases coordinate <;> norm_num [Fin.sum_univ_two, finProdFinEquiv, Fin.divNat, Fin.modNat] <;> ring

theorem seedMatrixDeviation_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rho alpha delta parameter angle : ℝ)
    (point : ClosedDisk) :
    fourierEvaluation (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) angle point =
      harmonicSeedOperator rho alpha delta parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  rw [seedMatrixDeviation_fourier_formula, seedOperator_double_angle]
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [add_apply, smul_apply, sub_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

end Grad.GaugeCoefficients.Physical.Frame
