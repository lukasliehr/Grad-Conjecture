import BT2TraceEnergy

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

local instance boundaryCoefficientPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem boundaryCirclePoint_continuous : Continuous boundaryCirclePoint := by
  have circleContinuous : Continuous (fun angle : CellCircle => (AddCircle.toCircle angle : ℂ)) :=
    continuous_induced_dom.comp AddCircle.continuous_toCircle
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro coordinate
  fin_cases coordinate
  · exact Complex.continuous_re.comp circleContinuous
  · exact Complex.continuous_im.comp circleContinuous

theorem boundaryDiskPoint_continuous : Continuous boundaryDiskPoint :=
  boundaryCirclePoint_continuous.subtype_mk _

theorem cartesianPhase_boundary (parameters : PhaseParameters) (cell : ℤ) (angle : CellCircle) :
    cartesianPhase parameters cell (boundaryDiskPoint angle).val = boundaryPhase parameters cell := by
  rw [cartesianPhase_formula]
  change parameters.sigma0 * cellFrequency cell - parameters.gamma *
      (Real.sqrt (1 + cellFrequency cell ^ 2 * ‖boundaryCirclePoint angle‖ ^ 2) - 1) = _
  rw [boundaryCirclePoint_norm, one_pow, mul_one]
  rfl

theorem cartesianWeight_boundary (parameters : PhaseParameters) (cell : ℤ) (angle : CellCircle) :
    cartesianWeight parameters cell (boundaryDiskPoint angle).val =
      Real.exp (boundaryPhase parameters cell) := by
  rw [cartesianWeight_exp, cartesianPhase_boundary]

theorem fourierCoeff_real_smul {dimension : ℕ} (factor : ℝ)
    (field : CellCircle → ComplexEuclidean dimension) (mode : ℤ) :
    fourierCoeff (fun angle => factor • field angle) mode = factor • fourierCoeff field mode := by
  unfold fourierCoeff
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact smul_comm _ _ _

/-- The actual two normalized Fourier integrals of W_gamma h on the unit
boundary, with angular index first and cell index second. -/
def weightedBoundaryCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  fourierCoeff (fun angle : CellCircle => fourierCoeff (fun cell : CellCircle =>
    (weightedSmoothEquiv parameters field).value (boundaryDiskPoint angle, cell)) mode.2) mode.1

theorem weightedBoundaryCoefficient_original {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    weightedBoundaryCoefficient parameters field mode =
      Real.exp (boundaryPhase parameters mode.2) • originalBoundaryCoefficient parameters field mode := by
  have innerCoefficient : ∀ angle : CellCircle,
      fourierCoeff (fun cell : CellCircle =>
        (weightedSmoothEquiv parameters field).value (boundaryDiskPoint angle, cell)) mode.2 =
      Real.exp (boundaryPhase parameters mode.2) • (field.1 mode.2).value (boundaryDiskPoint angle) := by
    intro angle
    rw [← diskCellFourierValue_apply, ← diskCellFourierCoefficientJet_value,
      diskCellFourierCoefficientJet_weightedSmoothEquiv, phaseWeightedJet_value,
      cartesianWeight_boundary]
  unfold weightedBoundaryCoefficient
  simp_rw [innerCoefficient]
  exact fourierCoeff_real_smul _ _ _

theorem weightedBoundaryCoefficient_integral {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    weightedBoundaryCoefficient parameters field mode =
      ∫ angle : CellCircle, ∫ cell : CellCircle,
        (fourier (-mode.1) angle * fourier (-mode.2) cell) •
          (weightedSmoothEquiv parameters field).value (boundaryDiskPoint angle, cell)
        ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  unfold weightedBoundaryCoefficient fourierCoeff
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [← integral_smul]
  simp only [mul_smul]

theorem weightedBoundaryCoefficient_norm_sq {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    ‖weightedBoundaryCoefficient parameters field mode‖ ^ 2 =
      Real.exp (2 * boundaryPhase parameters mode.2) * ‖originalBoundaryCoefficient parameters field mode‖ ^ 2 := by
  rw [weightedBoundaryCoefficient_original, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  congr 1
  rw [two_mul, Real.exp_add, pow_two]

end Grad.BoundaryTrace
