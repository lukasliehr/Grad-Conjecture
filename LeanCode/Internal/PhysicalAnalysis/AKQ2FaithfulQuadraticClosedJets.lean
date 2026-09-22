import AKQ1QuadraticPlanarInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisLift Grad.AxisSplit Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.Compensated (partialJet_coordinate_value partialJetLinear partialJetLinear_apply)

/-- The original smooth closed-disk polynomial, with exactly its six
complex planar coefficients and no change of physical coordinates. -/
def quadraticPlanarJet (coefficients : QuadraticPlanarCoefficients) : ClosedJet 2 :=
  coordinateJet 0 (coordinateJet 0 (constantValueJet (coefficients 0))) +
    coordinateJet 0 (coordinateJet 1 (constantValueJet (coefficients 1))) +
    coordinateJet 1 (coordinateJet 1 (constantValueJet (coefficients 2)))

theorem quadraticPlanarJet_value (coefficients : QuadraticPlanarCoefficients) (point : ClosedDisk) :
    (quadraticPlanarJet coefficients).value point =
      (point.val 0 ^ 2) • coefficients 0 + (point.val 0 * point.val 1) • coefficients 1 +
        (point.val 1 ^ 2) • coefficients 2 := by
  simp only [quadraticPlanarJet,closedJet_value_add,ContinuousMap.add_apply,coordinateJet_value,
    constantValueJet_value,smul_smul,pow_two]

theorem partial_constantValueJet_value {dimension : ℕ} (direction : Fin 2)
    (value : ComplexEuclidean dimension) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (constantValueJet value)).value point = 0 := by
  change (Grad.NonlinearQuotientBounds.partialJet direction (constantValueJet value)).value point = 0
  rw [constantValueJet,partialJet_global_value]
  simp

theorem linearColumnJet_partial_value (first second : ComplexEuclidean 2)
    (direction : Fin 2) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (linearColumnJet first second)).value point =
      if direction = 0 then first else second := by
  change (partialJetLinear 2 direction
    (coordinateJet 0 (constantValueJet first) + coordinateJet 1 (constantValueJet second))).value point = _
  rw [map_add,partialJetLinear_apply,partialJetLinear_apply,closedJet_value_add,ContinuousMap.add_apply]
  simp only [partialJet_coordinate_value,constantValueJet_value,partial_constantValueJet_value,smul_zero,add_zero]
  fin_cases direction <;> simp [spatialBasis]

theorem quadraticPlanarJet_partial_value (coefficients : QuadraticPlanarCoefficients)
    (direction : Fin 2) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (quadraticPlanarJet coefficients)).value point =
      if direction = 0 then
        (2 * point.val 0) • coefficients 0 + point.val 1 • coefficients 1
      else point.val 0 • coefficients 1 + (2 * point.val 1) • coefficients 2 := by
  change (partialJetLinear 2 direction
    (coordinateJet 0 (coordinateJet 0 (constantValueJet (coefficients 0))) +
      coordinateJet 0 (coordinateJet 1 (constantValueJet (coefficients 1))) +
      coordinateJet 1 (coordinateJet 1 (constantValueJet (coefficients 2))))).value point = _
  rw [map_add,map_add,partialJetLinear_apply,partialJetLinear_apply,partialJetLinear_apply]
  simp only [closedJet_value_add,ContinuousMap.add_apply,partialJet_coordinate_value,coordinateJet_value,
    constantValueJet_value,partial_constantValueJet_value,smul_zero,add_zero]
  fin_cases direction <;> simp [spatialBasis] <;> module

theorem quadraticPlanarJet_partial_zero (coefficients : QuadraticPlanarCoefficients) :
    Grad.GaugeCoefficients.Physical.Compensated.partialJet 0 (quadraticPlanarJet coefficients) = linearColumnJet ((2 : ℂ) • coefficients 0) (coefficients 1) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [quadraticPlanarJet_partial_value,if_pos rfl,linearColumnJet_value]
  module

theorem quadraticPlanarJet_partial_one (coefficients : QuadraticPlanarCoefficients) :
    Grad.GaugeCoefficients.Physical.Compensated.partialJet 1 (quadraticPlanarJet coefficients) = linearColumnJet (coefficients 1) ((2 : ℂ) • coefficients 2) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [quadraticPlanarJet_partial_value,if_neg (by decide : (1 : Fin 2) ≠ 0),linearColumnJet_value]
  module

theorem quadraticPlanarJet_injective : Function.Injective quadraticPlanarJet := by
  intro first second same
  have twice (outer inner : Fin 2) := congrArg (fun field : ClosedJet 2 =>
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet outer (Grad.GaugeCoefficients.Physical.Compensated.partialJet inner field)).value closedOrigin) same
  funext index
  fin_cases index
  · change first (0 : Fin 3) = second 0
    have equality := twice 0 0
    rw [quadraticPlanarJet_partial_zero,quadraticPlanarJet_partial_zero,
      linearColumnJet_partial_value,linearColumnJet_partial_value,if_pos rfl] at equality
    have scaled := congrArg (fun value : ComplexEuclidean 2 => (1 / 2 : ℂ) • value) equality
    simpa only [smul_smul,show (1 / 2 : ℂ) * 2 = 1 by norm_num,one_smul,if_true,if_false,show (1 : Fin 2) ≠ 0 by decide] using scaled
  · change first (1 : Fin 3) = second 1
    have equality := twice 1 0
    simpa only [quadraticPlanarJet_partial_zero,linearColumnJet_partial_value,show (1 : Fin 2) ≠ 0 by decide,if_false] using equality
  · change first (2 : Fin 3) = second 2
    have equality := twice 1 1
    rw [quadraticPlanarJet_partial_one,quadraticPlanarJet_partial_one,
      linearColumnJet_partial_value,linearColumnJet_partial_value,if_neg (by decide : (1 : Fin 2) ≠ 0)] at equality
    have scaled := congrArg (fun value : ComplexEuclidean 2 => (1 / 2 : ℂ) • value) equality
    simpa only [smul_smul,show (1 / 2 : ℂ) * 2 = 1 by norm_num,one_smul,if_true,if_false,show (1 : Fin 2) ≠ 0 by decide] using scaled

end Grad.FinitePhysicalJetLift
