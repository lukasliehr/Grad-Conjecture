import AKQ3ActualQuadraticPlanarEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.Compensated
  (partialJet_coordinate_value partialJetLinear partialJetLinear_apply gradientJet gradientJet_value)

/-- Coefficients of y1³, y1²*y2, y1*y2², y2³. -/
abbrev CubicScalarCoefficients := Fin 4 → ℂ

def scalarCoefficientJet (coefficient : ℂ) : ClosedJet 1 :=
  constantValueJet (WithLp.toLp 2 (fun _ => coefficient))

def cubicScalarJet (coefficients : CubicScalarCoefficients) : ClosedJet 1 :=
  coordinateJet 0 (coordinateJet 0 (coordinateJet 0 (scalarCoefficientJet (coefficients 0)))) +
    coordinateJet 0 (coordinateJet 0 (coordinateJet 1 (scalarCoefficientJet (coefficients 1)))) +
    coordinateJet 0 (coordinateJet 1 (coordinateJet 1 (scalarCoefficientJet (coefficients 2)))) +
    coordinateJet 1 (coordinateJet 1 (coordinateJet 1 (scalarCoefficientJet (coefficients 3))))

theorem cubicScalarJet_value (coefficients : CubicScalarCoefficients) (point : ClosedDisk) :
    (cubicScalarJet coefficients).value point 0 =
      (point.val 0 : ℂ) ^ 3 * coefficients 0 + (point.val 0 : ℂ) ^ 2 * (point.val 1 : ℂ) * coefficients 1 +
        (point.val 0 : ℂ) * (point.val 1 : ℂ) ^ 2 * coefficients 2 + (point.val 1 : ℂ) ^ 3 * coefficients 3 := by
  simp [cubicScalarJet,scalarCoefficientJet,closedJet_value_add,coordinateJet_value,constantValueJet_value,Complex.real_smul]
  ring

theorem cubicScalarJet_partial_value (coefficients : CubicScalarCoefficients) (direction : Fin 2) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (cubicScalarJet coefficients)).value point 0 =
      if direction = 0 then
        3 * (point.val 0 : ℂ) ^ 2 * coefficients 0 + 2 * (point.val 0 : ℂ) * (point.val 1 : ℂ) * coefficients 1 +
          (point.val 1 : ℂ) ^ 2 * coefficients 2
      else (point.val 0 : ℂ) ^ 2 * coefficients 1 + 2 * (point.val 0 : ℂ) * (point.val 1 : ℂ) * coefficients 2 +
        3 * (point.val 1 : ℂ) ^ 2 * coefficients 3 := by
  change (partialJetLinear 1 direction
    (coordinateJet 0 (coordinateJet 0 (coordinateJet 0 (scalarCoefficientJet (coefficients 0)))) +
      coordinateJet 0 (coordinateJet 0 (coordinateJet 1 (scalarCoefficientJet (coefficients 1)))) +
      coordinateJet 0 (coordinateJet 1 (coordinateJet 1 (scalarCoefficientJet (coefficients 2)))) +
      coordinateJet 1 (coordinateJet 1 (coordinateJet 1 (scalarCoefficientJet (coefficients 3)))))).value point 0 = _
  rw [map_add,map_add,map_add,partialJetLinear_apply,partialJetLinear_apply,partialJetLinear_apply,partialJetLinear_apply]
  simp only [closedJet_value_add,ContinuousMap.add_apply,partialJet_coordinate_value,coordinateJet_value,
    scalarCoefficientJet,constantValueJet_value,partial_constantValueJet_value,smul_zero,add_zero]
  fin_cases direction <;> simp [spatialBasis,Complex.real_smul] <;> ring

def cubicGradientCoefficients (coefficients : CubicScalarCoefficients) : QuadraticPlanarCoefficients :=
  ![WithLp.toLp 2 ![3 * coefficients 0,coefficients 1],
    WithLp.toLp 2 ![2 * coefficients 1,2 * coefficients 2],
    WithLp.toLp 2 ![coefficients 2,3 * coefficients 3]]

/-- The finite derivative matrix is the genuine Cartesian gradient on the
whole closed disk, not a formal symbol replacing the actual differential. -/
theorem cubicScalarJet_gradient (coefficients : CubicScalarCoefficients) :
    gradientJet (cubicScalarJet coefficients) = quadraticPlanarJet (cubicGradientCoefficients coefficients) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [gradientJet_value,quadraticPlanarJet_value]
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [cubicScalarJet_partial_value,cubicGradientCoefficients,Complex.real_smul] <;> ring

def cubicPlanarLift (coefficients : CubicScalarCoefficients) : ClosedJet 2 :=
  quadraticPlanarJet (quadraticPlanarInverse (cubicGradientCoefficients coefficients))

def quadraticForceLift (force : QuadraticPlanarCoefficients) : ClosedJet 2 :=
  quadraticPlanarJet (-(quadraticPlanarInverse force))

/-- Exact JF3–JF4 forced equation for every homogeneous cubic scalar and
every quadratic planar force, with u_f=-T f and the original signs. -/
theorem cubicPlanarLift_forced_equation (scalar : CubicScalarCoefficients) (force : QuadraticPlanarCoefficients) :
    gradientJet (cubicScalarJet scalar) - leadingPlanarJetOperator (cubicPlanarLift scalar + quadraticForceLift force) =
      quadraticPlanarJet force := by
  have sum : cubicPlanarLift scalar + quadraticForceLift force =
      quadraticPlanarJet (quadraticPlanarInverse (cubicGradientCoefficients scalar - force)) := by
    change quadraticPlanarJetLinear (quadraticPlanarInverse (cubicGradientCoefficients scalar)) +
      quadraticPlanarJetLinear (-(quadraticPlanarInverse force)) =
        quadraticPlanarJetLinear (quadraticPlanarInverse (cubicGradientCoefficients scalar - force))
    rw [map_sub,map_sub,map_neg]
    rfl
  rw [sum,leadingPlanarJetOperator_inverse,cubicScalarJet_gradient]
  change quadraticPlanarJetLinear (cubicGradientCoefficients scalar) -
    quadraticPlanarJetLinear (cubicGradientCoefficients scalar - force) = quadraticPlanarJetLinear force
  rw [map_sub]
  abel

end Grad.FinitePhysicalJetLift
