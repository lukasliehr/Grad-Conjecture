import AKU1QuadraticScalarJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Compensated (gradientJet gradientJet_value)

def quadraticScalarJetLinear : QuadraticScalarCoefficients →ₗ[ℂ] ClosedJet 1 where
  toFun := quadraticScalarJet
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    apply PiLp.ext
    intro component
    fin_cases component
    simp [quadraticScalarJet_value,closedJet_value_add]
    ring
  map_smul' scalar coefficients := by
    change quadraticScalarJet (scalar • coefficients) = scalar • quadraticScalarJet coefficients
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    apply PiLp.ext
    intro component
    fin_cases component
    simp [quadraticScalarJet_value,closedJet_value_smul]
    ring

/-- Half of the actual symmetric Hessian quadratic form. -/
def scalarHessianCoefficients (hessian : Matrix (Fin 2) (Fin 2) ℂ) : QuadraticScalarCoefficients :=
  ![hessian 0 0 / 2,hessian 0 1,hessian 1 1 / 2]

theorem scalarHessian_gradient_value (hessian : Matrix (Fin 2) (Fin 2) ℂ)
    (symmetric : hessian 0 1 = hessian 1 0) (point : ClosedDisk) (component : Fin 2) :
    (gradientJet (quadraticScalarJet (scalarHessianCoefficients hessian))).value point component =
      hessian component 0 * (point.val 0 : ℂ) + hessian component 1 * (point.val 1 : ℂ) := by
  rw [gradientJet_value]
  fin_cases component <;> simp [quadraticScalarJet_partial_value,scalarHessianCoefficients]
  · ring
  · rw [symmetric]
    ring

theorem scalarHessian_mean_zero (hessian : Matrix (Fin 2) (Fin 2) ℂ)
    (traceFree : hessian 0 0 + hessian 1 1 = 0) :
    angularClosedJet 0 (quadraticScalarJet (scalarHessianCoefficients hessian)) = 0 := by
  apply quadraticScalarJet_mean_zero
  dsimp [scalarHessianCoefficients]
  linear_combination (1/2 : ℂ) * traceFree

/-- The actual cell multiplier is left explicit so this polynomial identity
applies to every original cell, including the zero cell. -/
def scalarToroidalLiftCoefficients (length : ℝ) (cellMultiplier : ℂ)
    (scalar highSource : QuadraticScalarCoefficients) : QuadraticScalarCoefficients :=
  (length : ℂ)⁻¹ • quadraticScalarAngularInverse (highSource + cellMultiplier • scalar)

theorem scalarToroidalLift_equation (length : ℝ) (positive : 0 < length) (cellMultiplier : ℂ)
    (scalar highSource : QuadraticScalarCoefficients)
    (scalarMean : scalar 0 + scalar 2 = 0) (sourceMean : highSource 0 + highSource 2 = 0) :
    (length : ℂ) • rotationJet (quadraticScalarJet
      (scalarToroidalLiftCoefficients length cellMultiplier scalar highSource)) -
      cellMultiplier • quadraticScalarJet scalar = quadraticScalarJet highSource := by
  have totalMean : (highSource + cellMultiplier • scalar) 0 +
      (highSource + cellMultiplier • scalar) 2 = 0 := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination sourceMean + cellMultiplier * scalarMean
  have inverse := quadraticScalarAngularInverse_rotation _ totalMean
  have rotationScalar (a : ℂ) (q : QuadraticScalarCoefficients) :
      quadraticScalarRotation (a • q) = a • quadraticScalarRotation q := by
    funext index
    fin_cases index <;> simp [quadraticScalarRotation]; ring
  rw [quadraticScalarJet_rotation,scalarToroidalLiftCoefficients,rotationScalar,inverse]
  change (length : ℂ) • quadraticScalarJetLinear ((length : ℂ)⁻¹ •
      (highSource + cellMultiplier • scalar)) -
      cellMultiplier • quadraticScalarJetLinear scalar = quadraticScalarJetLinear highSource
  rw [map_smul,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul,
    map_add,map_smul]
  abel

theorem scalarToroidalLift_mean_zero (length : ℝ) (cellMultiplier : ℂ)
    (scalar highSource : QuadraticScalarCoefficients) :
    angularClosedJet 0 (quadraticScalarJet
      (scalarToroidalLiftCoefficients length cellMultiplier scalar highSource)) = 0 := by
  change angularClosedJet 0 (quadraticScalarJetLinear ((length : ℂ)⁻¹ •
    quadraticScalarAngularInverse (highSource + cellMultiplier • scalar))) = 0
  rw [map_smul,angularClosedJet_smul]
  change (length : ℂ)⁻¹ • angularClosedJet 0 (quadraticScalarJet
    (quadraticScalarAngularInverse (highSource + cellMultiplier • scalar))) = 0
  rw [quadraticScalarAngularInverse_mean_zero,smul_zero]

end Grad.FinitePhysicalJetLift
