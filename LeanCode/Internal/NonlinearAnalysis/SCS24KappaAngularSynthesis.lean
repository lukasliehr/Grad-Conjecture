import SCS23KappaCircle

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.Allocation Grad.PhaseAlgebra

theorem coefficientRadialEnvelope_one_le (parameters : PhaseParameters) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    1 ≤ coefficientRadialEnvelope parameters cell radius := by
  apply Real.one_le_exp_iff.mpr
  exact mul_nonneg (phaseWidth_nonneg parameters radius nonnegative bounded) (abs_nonneg _)

variable (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)

include nonnegative bounded

theorem kappaScalar_norm_summable :
    Summable (fun mode : ℤ × ℤ => ‖kappaScalar parameters L rho epsilon field small component 0 radius mode‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (kappaScalarMoment_summable parameters L rho epsilon field small component 0 0 radius nonnegative bounded)
  intro mode
  change ‖kappaScalar parameters L rho epsilon field small component 0 radius mode‖ ≤
    coefficientRadialEnvelope parameters mode.2 radius * annularFrequency mode.1 mode.2 ^ 0 *
      ‖kappaScalar parameters L rho epsilon field small component 0 radius mode‖
  simpa only [pow_zero, mul_one, one_mul] using
    mul_le_mul_of_nonneg_right (coefficientRadialEnvelope_one_le parameters radius nonnegative bounded mode.2)
      (norm_nonneg (kappaScalar parameters L rho epsilon field small component 0 radius mode))

theorem kappaScalar_angular_norm_summable (cell : ℤ) :
    Summable (fun mode : ℤ => ‖kappaScalar parameters L rho epsilon field small component 0 radius (mode, cell)‖) :=
  (kappaScalar_norm_summable parameters L rho epsilon field small component radius nonnegative bounded).comp_injective
    (fun _ _ equality => congrArg Prod.fst equality)

theorem kappaScalar_angular_hasSum (cell : ℤ) (angle : ℝ) :
    HasSum (fun mode : ℤ => cellExponential mode angle *
      kappaScalar parameters L rho epsilon field small component 0 radius (mode, cell))
      (kappaPolarCell parameters L rho epsilon field small component cell (radius, angle) 0) := by
  have norms := kappaScalar_angular_norm_summable parameters L rho epsilon field small component radius nonnegative bounded cell
  have summable : Summable (fourierCoeff
      (kappaCircle parameters L rho epsilon field small component cell radius nonnegative bounded)) := by
    exact norms.of_norm.congr (fun mode =>
      (kappaCircle_coefficient parameters L rho epsilon field small component cell radius nonnegative bounded mode).symm)
  have series := has_pointwise_sum_fourier_series_of_summable summable (angle : CellCircle)
  rw [kappaCircle_coe] at series
  apply series.congr_fun
  intro mode
  rw [kappaCircle_coefficient]
  change _ = kappaScalar parameters L rho epsilon field small component 0 radius (mode, cell) *
    cellCharacter mode (angle : CellCircle)
  rw [cellCharacter_coe, mul_comm]

end Grad.SourceCollarFullSource
