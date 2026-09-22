import AKQ22ActualChartCubicInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Compensated
  (partialJet_coordinate_value partialJetLinear partialJetLinear_apply gradientJet gradientJet_value)

abbrev QuadraticScalarCoefficients := Fin 3 → ℂ

def quadraticScalarJet (coefficients : QuadraticScalarCoefficients) : ClosedJet 1 :=
  coordinateJet 0 (coordinateJet 0 (scalarCoefficientJet (coefficients 0))) +
    coordinateJet 0 (coordinateJet 1 (scalarCoefficientJet (coefficients 1))) +
    coordinateJet 1 (coordinateJet 1 (scalarCoefficientJet (coefficients 2)))

theorem quadraticScalarJet_value (coefficients : QuadraticScalarCoefficients) (point : ClosedDisk) :
    (quadraticScalarJet coefficients).value point 0 =
      (point.val 0 : ℂ)^2 * coefficients 0 +
        (point.val 0 : ℂ) * (point.val 1 : ℂ) * coefficients 1 +
        (point.val 1 : ℂ)^2 * coefficients 2 := by
  simp [quadraticScalarJet,scalarCoefficientJet,closedJet_value_add,coordinateJet_value,
    constantValueJet_value,Complex.real_smul]
  ring

theorem quadraticScalarJet_partial_value (coefficients : QuadraticScalarCoefficients)
    (direction : Fin 2) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (quadraticScalarJet coefficients)).value point 0 =
      if direction = 0 then 2 * (point.val 0 : ℂ) * coefficients 0 + (point.val 1 : ℂ) * coefficients 1
      else (point.val 0 : ℂ) * coefficients 1 + 2 * (point.val 1 : ℂ) * coefficients 2 := by
  change (partialJetLinear 1 direction
    (coordinateJet 0 (coordinateJet 0 (scalarCoefficientJet (coefficients 0))) +
      coordinateJet 0 (coordinateJet 1 (scalarCoefficientJet (coefficients 1))) +
      coordinateJet 1 (coordinateJet 1 (scalarCoefficientJet (coefficients 2))))).value point 0 = _
  rw [map_add,map_add,partialJetLinear_apply,partialJetLinear_apply,partialJetLinear_apply]
  simp only [closedJet_value_add,ContinuousMap.add_apply,partialJet_coordinate_value,coordinateJet_value,
    scalarCoefficientJet,constantValueJet_value,partial_constantValueJet_value,smul_zero,add_zero]
  fin_cases direction <;> simp [spatialBasis,Complex.real_smul] <;> ring

def quadraticScalarRotation (coefficients : QuadraticScalarCoefficients) : QuadraticScalarCoefficients :=
  ![coefficients 1,2 * coefficients 2 - 2 * coefficients 0,-coefficients 1]

theorem quadraticScalarJet_rotation (coefficients : QuadraticScalarCoefficients) :
    rotationJet (quadraticScalarJet coefficients) = quadraticScalarJet (quadraticScalarRotation coefficients) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  fin_cases component
  simp [rotationJet,sub_eq_add_neg,closedJet_value_add,closedJet_value_neg,
    coordinateJet_value,quotientPartialJet_eq,quadraticScalarJet_partial_value,
    quadraticScalarJet_value,quadraticScalarRotation,Complex.real_smul]
  ring

def quadraticScalarAngularInverse (coefficients : QuadraticScalarCoefficients) : QuadraticScalarCoefficients :=
  ![-coefficients 1 / 4,coefficients 0,-(-coefficients 1 / 4)]

/-- The inverse is defined only as used on the mean-free quadratic sector;
its actual angular derivative has the original sign and no cell division. -/
theorem quadraticScalarAngularInverse_rotation (coefficients : QuadraticScalarCoefficients)
    (meanFree : coefficients 0 + coefficients 2 = 0) :
    quadraticScalarRotation (quadraticScalarAngularInverse coefficients) = coefficients := by
  funext index
  fin_cases index <;> simp [quadraticScalarRotation,quadraticScalarAngularInverse]
  · ring
  · linear_combination -meanFree

theorem quadraticScalarJet_mean_zero (coefficients : QuadraticScalarCoefficients)
    (meanFree : coefficients 0 + coefficients 2 = 0) :
    angularClosedJet 0 (quadraticScalarJet coefficients) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [quadraticScalarJet,scalarCoefficientJet,angularClosedJet_add,
    closedJet_value_add,ContinuousMap.add_apply,Grad.ChartAxisLift.angular_quadraticCoordinate_value]
  norm_num
  rw [← smul_add]
  have sum : (WithLp.toLp 2 (fun _ : Fin 1 => coefficients 0) : ComplexEuclidean 1) +
      WithLp.toLp 2 (fun _ : Fin 1 => coefficients 2) = 0 := by
    apply PiLp.ext
    intro component
    exact meanFree
  rw [sum,smul_zero]

theorem quadraticScalarAngularInverse_mean_zero (coefficients : QuadraticScalarCoefficients) :
    angularClosedJet 0 (quadraticScalarJet (quadraticScalarAngularInverse coefficients)) = 0 :=
  quadraticScalarJet_mean_zero _ (by simp [quadraticScalarAngularInverse])

end Grad.FinitePhysicalJetLift
