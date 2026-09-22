import AKU3CurrentLeadingSourceSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

theorem quadraticMonomial_angular_odd {dimension : ℕ} (first second : Fin 2)
    (vector : ComplexEuclidean dimension) (mode : ℤ) (oddMode : mode = 1 ∨ mode = -1) :
    angularClosedJet mode (coordinateJet first (coordinateJet second (constantValueJet vector))) = 0 := by
  rcases oddMode with rfl | rfl
  all_goals fin_cases first <;> fin_cases second
  all_goals norm_num [angular_coordinateJet_zero,angular_coordinateJet_one,
    angularClosedJet_constant,Grad.Cor18.coordinateMultiplyJet_zero_jet]

theorem cubicMonomial_mean_zero {dimension : ℕ} (first second third : Fin 2)
    (vector : ComplexEuclidean dimension) :
    angularClosedJet 0 (coordinateJet first (coordinateJet second (coordinateJet third (constantValueJet vector)))) = 0 := by
  fin_cases first
  · change angularClosedJet 0 (coordinateJet 0 (coordinateJet second (coordinateJet third (constantValueJet vector)))) = 0
    rw [angular_coordinateJet_zero,show (0 : ℤ) - 1 = -1 by norm_num,zero_add,quadraticMonomial_angular_odd second third vector (-1) (Or.inr rfl),
      quadraticMonomial_angular_odd second third vector 1 (Or.inl rfl)]
    simp [Grad.Cor18.coordinateMultiplyJet_zero_jet]
  · change angularClosedJet 0 (coordinateJet 1 (coordinateJet second (coordinateJet third (constantValueJet vector)))) = 0
    rw [angular_coordinateJet_one,show (0 : ℤ) - 1 = -1 by norm_num,zero_add,quadraticMonomial_angular_odd second third vector (-1) (Or.inr rfl),
      quadraticMonomial_angular_odd second third vector 1 (Or.inl rfl)]
    simp [Grad.Cor18.coordinateMultiplyJet_zero_jet]

theorem cubicScalarJet_mean_zero (coefficients : CubicScalarCoefficients) :
    angularClosedJet 0 (cubicScalarJet coefficients) = 0 := by
  simp only [cubicScalarJet,scalarCoefficientJet,angularClosedJet_add,cubicMonomial_mean_zero,add_zero]

theorem quadraticPlanarJet_angular_odd (coefficients : QuadraticPlanarCoefficients)
    (mode : ℤ) (oddMode : mode = 1 ∨ mode = -1) :
    angularClosedJet mode (quadraticPlanarJet coefficients) = 0 := by
  simp only [quadraticPlanarJet,angularClosedJet_add,quadraticMonomial_angular_odd _ _ _ mode oddMode,add_zero]

theorem quadraticPlanarJet_equivariant_zero (coefficients : QuadraticPlanarCoefficients) :
    equivariantAverageJet (quadraticPlanarJet coefficients) = 0 := by
  rw [equivariantAverageJet_eq,quadraticPlanarJet_angular_odd coefficients 1 (Or.inl rfl),
    quadraticPlanarJet_angular_odd coefficients (-1) (Or.inr rfl)]
  simp only [valueMapJet_map_zero,add_zero]

theorem quadraticPlanarJet_tangential_zero (coefficients : QuadraticPlanarCoefficients) :
    tangentialJet (quadraticPlanarJet coefficients) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [tangentialJet_value,quadraticPlanarJet_equivariant_zero]
  simp only [closedJet_value_zero,ContinuousMap.zero_apply,map_zero,sub_zero,smul_zero]

end Grad.FinitePhysicalJetLift
