import GQ7PhysicalRows

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

theorem actualScaledSeedDerivative_formula {L ell : ℝ} {parameters : PhaseParameters}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (rho alpha delta parameter angle : ℝ) (point : ClosedDisk) :
    actualScaledSeedDerivative (admissible := admissible) (rho := rho) (alpha := alpha)
        (delta := delta) (parameter := parameter) angle point =
      ((ell / L : ℝ) : ℂ) • operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) angle) := by
  have each (cell : ℤ) : coefficientValue (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) cell point =
      scaledSeedDerivativeCell L ell rho alpha delta parameter cell := by
    change coefficientDerivative _ cell zeroDerivativeIndex point = _
    rw [seedDerivativeCoefficient_derivative]
    rfl
  unfold actualScaledSeedDerivative fourierEvaluation
  simp_rw [each]
  change operatorMatrix (∑' cell : ℤ, cellExponential cell angle •
    scaledSeedDerivativeCell L ell rho alpha delta parameter cell) = _
  rw [seedDerivativeValue_fourier admissible rho alpha delta parameter angle, operatorMatrix_smul]

/-- The unnormalised physical second covector L e_T + ell iota M'Y. -/
def unscaledToroidalCovector (L ell : ℝ) (derivative : Matrix (Fin 2) (Fin 2) ℂ) (point : ClosedDisk) : Fin 3 → ℂ :=
  fun row => (L : ℂ) * toroidalPhysicalColumn row 0 +
    (ell : ℂ) * (planarPhysicalInclusion * derivative * spatialColumn point) row 0

theorem physicalToroidalCovector_scale (L ell : ℝ) (nonzero : L ≠ 0)
    (derivative : Matrix (Fin 2) (Fin 2) ℂ) (point : ClosedDisk) (row : Fin 3) :
    (L : ℂ) * physicalToroidalCovector (((ell / L : ℝ) : ℂ) • derivative) point row =
      unscaledToroidalCovector L ell derivative point row := by
  simp only [physicalToroidalCovector, unscaledToroidalCovector, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_div]
  have complexNonzero : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  field_simp

theorem closedAngularMean_const_mul (scalar : ℂ) (field : ClosedDisk → ℂ) (point : ClosedDisk) :
    closedAngularMean (fun other => scalar * field other) point = scalar * closedAngularMean field point := by
  unfold closedAngularMean
  exact integral_const_mul _ _

theorem actualGauge_toroidal_unscaled {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    (L : ℂ) * fullGaugeValueAction ledger.val.gaugeDeviation grade angle field point 2 =
      ∑ row : Fin 3, ((physicalInverseTranspose ledger grade angle point).mulVec (field point)) row *
        unscaledToroidalCovector L ell (operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) angle)) point row := by
  rw [actualGauge_toroidal ledger, actualScaledSeedDerivative_formula, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [mul_left_comm, physicalToroidalCovector_scale L ell admissible.1.ne']

end Grad.GaugeCoefficients.Physical.GaugeTransfer
