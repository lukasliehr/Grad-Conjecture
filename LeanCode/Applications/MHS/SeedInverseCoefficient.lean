import SeedInverseGeometry

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GeometryClosure

def inverseDeterminant (rho : ℝ) : ℝ := (Real.sqrt (1 - rho ^ 2))⁻¹

theorem actualInverseOperator_formula (parameter : Parameters) (admissible : parameter ∈ parameterDomain) (angle : ℝ) :
    actualInverseOperator parameter angle = (inverseDeterminant (parameter 0) : ℂ) •
      harmonicSeedOperator (-(parameter 0)) (parameter 1) (parameter 2) (parameter 3) angle := by
  unfold actualInverseOperator harmonicSeedOperator
  have matrixIdentity := seed_inverse_reflected admissible (seedAngle (parameter 1) (parameter 2) (parameter 3) angle)
  have vectorIdentity :
      WithLp.toLp 2 (fun index : Fin (2 * 2) =>
        ((actualInverse parameter angle (finProdFinEquiv.symm index).2 (finProdFinEquiv.symm index).1 : ℝ) : ℂ)) =
      (inverseDeterminant (parameter 0) : ℂ) • WithLp.toLp 2 (fun index : Fin (2 * 2) =>
        (harmonicSeedMatrix (-(parameter 0)) (parameter 1) (parameter 2) (parameter 3) angle
          (finProdFinEquiv.symm index).2 (finProdFinEquiv.symm index).1 : ℂ)) := by
    apply PiLp.ext
    intro index
    change (actualInverse parameter angle _ _ : ℂ) = _
    unfold actualInverse
    rw [matrixIdentity]
    simp [harmonicSeedMatrix, inverseDeterminant, smul_eq_mul]
  rw [vectorIdentity, map_smul]

def inverseDeviationCoefficient (phase : PhaseParameters) (grade : ℕ) (parameter : Parameters) :
    Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2 :=
  (inverseDeterminant (parameter 0) : ℂ) •
    seedMatrixDeviationCoefficient (seedAdmissible phase) grade
      (-(parameter 0)) (parameter 1) (parameter 2) (parameter 3) +
    seedConstantCell 1 phase.sigma0 phase.gamma 1 grade 0
      (((inverseDeterminant (parameter 0) - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2))

theorem inverseDeviation_fourier (phase : PhaseParameters) (parameter : Parameters)
    (admissible : parameter ∈ parameterDomain) (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (inverseDeviationCoefficient phase 0 parameter) angle point =
      actualInverseOperator parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  change seedFourierCLM (seedAdmissible phase) 2 2 angle point (_ + _) = _
  rw [map_add, map_smul]
  change (inverseDeterminant (parameter 0) : ℂ) • fourierEvaluation _ angle point +
    fourierEvaluation _ angle point = _
  rw [seedMatrixDeviation_fourier, seedConstantCell_fourier, actualInverseOperator_formula parameter admissible angle]
  norm_num only [fourierPhase, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_smul]
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [smul_apply, add_apply, sub_apply, PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem inverseDeviation_realizes (phase : PhaseParameters) (grade : ℕ) (parameter : Parameters) :
    RealizesSameCoefficient (inverseDeviationCoefficient phase 0 parameter)
      (inverseDeviationCoefficient phase grade parameter) := by
  intro cell point
  unfold inverseDeviationCoefficient
  simp only [coefficientDerivative_add_apply, coefficientDerivative_smul_apply]
  rw [seedMatrixDeviation_realizes (seedAdmissible phase) grade (-(parameter 0))
    (parameter 1) (parameter 2) (parameter 3) cell point,
    seedConstantCell_realizes 1 phase.sigma0 phase.gamma 1 grade 0 _ cell point]
  simp only [coefficientValue, coefficientDerivative_add_apply, coefficientDerivative_smul_apply]

theorem inverseDeviation_cell (phase : PhaseParameters) (grade : ℕ) (parameter : Parameters)
    (admissible : parameter ∈ parameterDomain) (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative (inverseDeviationCoefficient phase grade parameter) cell (zeroDerivativeIndexAt grade) point =
      actualCells 1 parameter cell := by
  rw [inverseDeviation_realizes phase grade parameter cell point]
  rw [← seedCoefficient_integral (seedAdmissible phase) _ point cell]
  simp_rw [inverseDeviation_fourier phase parameter admissible]
  simp [actualCells, Complex.ofReal_mul, Complex.ofReal_ofNat]

end Grad.Constraints.Seed
