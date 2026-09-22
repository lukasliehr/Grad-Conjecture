import AKU45ActualScalarLiftTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Ledger

theorem secondTaylorAxis_add {parameters : PhaseParameters} {dimension : ℕ}
    (first second : ACore parameters dimension) :
    secondTaylorAxis (first+second) = secondTaylorAxis first + secondTaylorAxis second := by
  funext index
  fin_cases index <;> simp [secondTaylorAxis,map_add,smul_add]

theorem secondTaylorAxis_sub {parameters : PhaseParameters} {dimension : ℕ}
    (first second : ACore parameters dimension) :
    secondTaylorAxis (first-second) = secondTaylorAxis first - secondTaylorAxis second := by
  funext index
  fin_cases index <;> simp [secondTaylorAxis,map_sub,smul_sub]

theorem localizedScalarQuadratic_eq_vector {parameters : PhaseParameters}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 1) :
    (∑ index, fixedAxisJetCore (localizedFiniteJet (quadraticScalarJet (Pi.single index 1))) (data index)) =
      localizedQuadraticVectorAxisCore data := by
  apply acore_ext
  intro cell point
  rw [localizedQuadraticVectorAxisCore_val,localizedFiniteJet_value,quadraticVectorJet_value]
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  simp [Fin.sum_univ_three,fixedAxisJetCore_val,closedJet_value_smul,
    localizedFiniteJet_value,quadraticScalarJet_value,Complex.real_smul]
  ring

theorem originalFiniteLiftS_polynomial (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    originalFiniteLiftS parameters length rho epsilon field low source =
      localizedQuadraticVectorAxisCore (originalScalarHessianAxis source) +
        localizedCubicScalarAxisCore (originalLiftS3Axis parameters length rho epsilon field low source) := by
  rw [originalFiniteLiftS,localizedScalarQuadratic_eq_vector]

theorem originalFiniteLiftS_secondTaylor_partial (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (direction : Fin 2) :
    secondTaylorAxis (partialCore parameters direction (originalFiniteLiftS parameters length rho epsilon field low source)) =
      if direction = 0 then
        ![(3 : ℂ) • originalLiftS3Axis parameters length rho epsilon field low source 0,
          (2 : ℂ) • originalLiftS3Axis parameters length rho epsilon field low source 1,
          originalLiftS3Axis parameters length rho epsilon field low source 2]
      else
        ![originalLiftS3Axis parameters length rho epsilon field low source 1,
          (2 : ℂ) • originalLiftS3Axis parameters length rho epsilon field low source 2,
          (3 : ℂ) • originalLiftS3Axis parameters length rho epsilon field low source 3] := by
  rw [originalFiniteLiftS_polynomial,map_add,secondTaylorAxis_add,
    secondTaylorAxis_partial_localizedQuadratic,zero_add,secondTaylorAxis_partial_localizedCubic]

theorem leadingPlanarLift_force_coefficients (linear : ComplexEuclidean 2) (force : QuadraticPlanarCoefficients) :
    cubicGradientCoefficients (cubicComplementCoefficients linear) -
      quadraticPlanarOperator (leadingPlanarLiftCoefficients linear force) = force := by
  apply quadraticPlanarJet_injective
  change quadraticPlanarJetLinear (cubicGradientCoefficients (cubicComplementCoefficients linear) -
      quadraticPlanarOperator (leadingPlanarLiftCoefficients linear force)) = quadraticPlanarJet force
  rw [map_sub]
  change quadraticPlanarJet (cubicGradientCoefficients (cubicComplementCoefficients linear)) -
      quadraticPlanarJet (quadraticPlanarOperator (leadingPlanarLiftCoefficients linear force)) = _
  rw [← cubicScalarJet_gradient,quadraticPlanarJet_operator]
  exact leadingPlanarLift_force linear force

end Grad.FinitePhysicalJetLift
