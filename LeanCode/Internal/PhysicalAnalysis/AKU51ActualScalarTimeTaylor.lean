import AKU49ActualAxialCorrectionOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear)

theorem secondAxisTrace_time_value {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (first second : Fin 2) (cell : ℤ) :
    (secondAxisTrace first second (timeDerivativeCore parameters field)).val cell =
      ((cell : ℂ)*Complex.I) • (secondAxisTrace first second field).val cell := by
  change (partialJetLinear dimension first (partialJetLinear dimension second
    ((timeDerivativeCore parameters field).val cell))).value closedOrigin = _
  rw [timeDerivativeCore_val,map_smul,map_smul,closedJet_value_smul]
  rfl

theorem secondTaylorAxis_time_value {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (cell : ℤ) (index : Fin 3) :
    (secondTaylorAxis (timeDerivativeCore parameters field) index).val cell =
      ((cell : ℂ)*Complex.I) • (secondTaylorAxis field index).val cell := by
  fin_cases index
  · change (1/2 : ℂ) • (secondAxisTrace 0 0 (timeDerivativeCore parameters field)).val cell = _
    rw [secondAxisTrace_time_value]
    exact smul_comm _ _ _
  · exact secondAxisTrace_time_value field 0 1 cell
  · change (1/2 : ℂ) • (secondAxisTrace 1 1 (timeDerivativeCore parameters field)).val cell = _
    rw [secondAxisTrace_time_value]
    exact smul_comm _ _ _

theorem secondTaylorAxis_localizedCubic_zero {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) :
    secondTaylorAxis (localizedCubicScalarAxisCore data) = 0 := by
  rw [localizedCubicScalarAxisCore_coordinates]
  simp only [secondTaylorAxis_add,secondTaylorAxis_three_coordinates,add_zero]

theorem originalFiniteLiftS_secondTaylor (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    secondTaylorAxis (originalFiniteLiftS parameters length rho epsilon field low source) =
      originalScalarHessianAxis source := by
  rw [originalFiniteLiftS_polynomial,secondTaylorAxis_add,secondTaylorAxis_localizedQuadraticVectorAxisCore,
    secondTaylorAxis_localizedCubic_zero,add_zero]

theorem scalarToroidalLift_coefficients_equation (length : ℝ) (positive : 0 < length) (cellMultiplier : ℂ)
    (scalar highSource : QuadraticScalarCoefficients)
    (scalarMean : scalar 0 + scalar 2 = 0) (sourceMean : highSource 0 + highSource 2 = 0) :
    (length : ℂ) • quadraticScalarRotation
      (scalarToroidalLiftCoefficients length cellMultiplier scalar highSource) - cellMultiplier • scalar = highSource := by
  have mean : (highSource+cellMultiplier • scalar) 0 + (highSource+cellMultiplier • scalar) 2 = 0 := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination sourceMean + cellMultiplier * scalarMean
  have rotationScalar (a : ℂ) (q : QuadraticScalarCoefficients) :
      quadraticScalarRotation (a • q) = a • quadraticScalarRotation q := by
    funext index
    fin_cases index <;> simp [quadraticScalarRotation]
    ring
  rw [scalarToroidalLiftCoefficients,rotationScalar,quadraticScalarAngularInverse_rotation _ mean,
    smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul]
  abel

end Grad.FinitePhysicalJetLift
