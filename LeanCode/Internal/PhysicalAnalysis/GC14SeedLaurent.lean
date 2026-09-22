import GC14SeedConstants
import GC14SeedEvaluation
import Mathlib.Analysis.Complex.Trigonometric

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def seedLaurentCell : Fin 5 → ℤ := ![0, 1, -1, 2, -2]

def seedLaurentAmplitude (sign alpha delta parameter : ℝ) : Fin 5 → ℂ :=
  ![(sign : ℂ) * 2 * Complex.I * alpha,
    (sign : ℂ) * Complex.I * delta, (sign : ℂ) * Complex.I * delta,
    (sign : ℂ) * delta * parameter, -(sign : ℂ) * delta * parameter]

/-- The exact five Laurent modes of `sign * 2 i theta`; no Fourier
regularity premise enters its coefficient construction. -/
def seedAngleGenerator (L sigma gamma ell : ℝ) (grade : ℕ)
    (sign alpha delta parameter : ℝ) : Coefficient L sigma gamma ell grade 1 1 :=
  ∑ mode : Fin 5, seedConstantCell L sigma gamma ell grade (seedLaurentCell mode)
    (seedLaurentAmplitude sign alpha delta parameter mode •
      ContinuousLinearMap.id ℂ (ComplexEuclidean 1))

theorem seedLaurentPhase (cell : ℤ) (angle : ℝ) :
    fourierPhase cell angle =
      (Real.cos ((cell : ℝ) * angle) : ℂ) +
        (Real.sin ((cell : ℝ) * angle) : ℂ) * Complex.I := by
  unfold fourierPhase
  rw [show Complex.I * (cell : ℂ) * angle = (((cell : ℝ) * angle : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem seedLaurent_formula (sign alpha delta parameter angle : ℝ) :
    (∑ mode : Fin 5, fourierPhase (seedLaurentCell mode) angle *
      seedLaurentAmplitude sign alpha delta parameter mode) =
      (sign : ℂ) * 2 * Complex.I *
        (Grad.GeometryClosure.seedAngle alpha delta parameter angle : ℝ) := by
  simp_rw [seedLaurentPhase]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, seedLaurentCell, seedLaurentAmplitude,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [Grad.GeometryClosure.seedAngle, Real.cos_neg, Real.sin_neg]
  ring

theorem seedAngleGenerator_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (sign alpha delta parameter angle : ℝ)
    (point : ClosedDisk) :
    fourierEvaluation (seedAngleGenerator L sigma gamma ell 0 sign alpha delta parameter)
        angle point =
      ((sign : ℂ) * 2 * Complex.I *
        (Grad.GeometryClosure.seedAngle alpha delta parameter angle : ℝ)) •
          ContinuousLinearMap.id ℂ (ComplexEuclidean 1) := by
  change seedFourierCLM admissible 1 1 angle point (∑ mode : Fin 5, _) = _
  rw [map_sum]
  change (∑ mode : Fin 5, fourierEvaluation (seedConstantCell L sigma gamma ell 0
    (seedLaurentCell mode) (seedLaurentAmplitude sign alpha delta parameter mode •
      ContinuousLinearMap.id ℂ (ComplexEuclidean 1))) angle point) = _
  simp_rw [seedConstantCell_fourier, smul_smul]
  rw [← Finset.sum_smul, seedLaurent_formula]

theorem seedScalarOperator_exp (scalar : ℂ) :
    NormedSpace.exp (scalar • (1 : OperatorValue 1 1)) =
      Complex.exp scalar • (1 : OperatorValue 1 1) := by
  have commute := NormedSpace.algebraMap_exp_comm
    (𝕂 := ℂ) (𝔸 := OperatorValue 1 1) scalar
  rw [← Complex.exp_eq_exp_ℂ] at commute
  simpa only [Algebra.algebraMap_eq_smul_one] using commute.symm

def seedAngleExponential {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (sign alpha delta parameter : ℝ) : Coefficient L sigma gamma ell grade 1 1 :=
  seedCoefficientExponential admissible
    (seedAngleGenerator L sigma gamma ell grade sign alpha delta parameter)

theorem seedAngleExponential_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (sign alpha delta parameter angle : ℝ)
    (point : ClosedDisk) :
    fourierEvaluation (seedAngleExponential admissible 0 sign alpha delta parameter) angle point =
      Complex.exp ((sign : ℂ) * 2 * Complex.I *
        (Grad.GeometryClosure.seedAngle alpha delta parameter angle : ℝ)) •
          ContinuousLinearMap.id ℂ (ComplexEuclidean 1) := by
  unfold seedAngleExponential
  rw [seedExponential_fourier, seedAngleGenerator_fourier admissible]
  have identity : (1 : OperatorValue 1 1) = ContinuousLinearMap.id ℂ (ComplexEuclidean 1) := by
    apply ContinuousLinearMap.ext
    intro vector
    rfl
  rw [← identity]
  exact seedScalarOperator_exp _

end Grad.GaugeCoefficients.Physical.Frame
