import SCS18LiteralG3Convolution

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarBulk Grad.AxisCore Grad.GaugeCoefficients.Physical.Allocation

theorem originalRowCoefficient_lowering_ae {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (annularWeightLoweringRowValue lower field) radius mode =
        originalRowCoefficient parameters (power + 1) lower field radius mode := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [Lp.coeFn_smul (annularWeightLoweringRatio mode) (field mode)] with radius same
  unfold originalRowCoefficient
  change _ • (annularWeightLoweringRatio mode • field mode) radius = _
  rw [same]
  change (originalRowWeight parameters power radius mode : ℂ)⁻¹ •
    (annularWeightLoweringRatio mode • field mode radius) = _
  rw [smul_smul]
  congr 1
  simp only [originalRowWeight, annularWeightLoweringRatio, pow_succ, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_inv_rev]
  ring

theorem g3Rows_actual_coefficients {grade order : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (paid : order + 4 ≤ grade) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : ZAmbient parameters grade)
    (planarFlat : OriginalValueFlat parameters (by omega) (originalSourcePlanar parameters grade source))
    (fourthFlat : OriginalValueFlat parameters (by omega) (source 3)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters order lower
        (g3ValueRow parameters L rho epsilon field small lower positive bounded paid source) radius mode =
        actualG3Coefficient parameters L rho epsilon field small (by omega) source radius
          (positive.le.trans inside.1) inside.2 mode ∧
      originalRowCoefficient parameters order lower
        (g3AngularRow parameters L rho epsilon field small lower positive bounded paid source) radius mode =
        (Complex.I * (mode.1 : ℂ)) • actualG3Coefficient parameters L rho epsilon field small (by omega) source radius
          (positive.le.trans inside.1) inside.2 mode := by
  filter_upwards [originalRowCoefficient_lowering_ae parameters order lower
      (fullG3Row (power := order + 1) parameters L rho epsilon field small lower positive bounded (by omega) source),
    fullG3Row_actual_coefficient parameters L rho epsilon field small (by omega) source
      (power := order + 1) (by omega) lower positive bounded planarFlat fourthFlat,
    g3AngularRow_literal parameters L rho epsilon field small lower positive bounded paid source]
    with radius lowerLaw actual angular
  intro inside mode
  have value : originalRowCoefficient parameters order lower
      (g3ValueRow parameters L rho epsilon field small lower positive bounded paid source) radius mode =
      actualG3Coefficient parameters L rho epsilon field small (by omega) source radius
        (positive.le.trans inside.1) inside.2 mode := (lowerLaw mode).trans (actual inside mode)
  exact ⟨value, (angular mode).trans (congrArg (fun value => (Complex.I * (mode.1 : ℂ)) • value) value)⟩

end Grad.SourceCollarFullSource
