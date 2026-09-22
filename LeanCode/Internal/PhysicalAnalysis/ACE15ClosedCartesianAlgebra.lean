import ACE14EulerDilationCommutation
import GQF12RadialRotation

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear partialJet_coordinate_value)

theorem centerPartial_add {dimension : ℕ} (direction : Fin 2) (first second : ClosedJet dimension) :
    partialJet direction (first + second) = partialJet direction first + partialJet direction second :=
  (partialJetLinear dimension direction).map_add first second

theorem centerPartial_smul {dimension : ℕ} (direction : Fin 2) (scalar : ℂ) (field : ClosedJet dimension) :
    partialJet direction (scalar • field) = scalar • partialJet direction field :=
  (partialJetLinear dimension direction).map_smul scalar field

theorem centerPartial_zero (dimension : ℕ) (direction : Fin 2) : partialJet direction (0 : ClosedJet dimension) = 0 :=
  (partialJetLinear dimension direction).map_zero

theorem centerCoordinate_add {dimension : ℕ} (coordinate : Fin 2) (first second : ClosedJet dimension) :
    coordinateJet coordinate (first + second) = coordinateJet coordinate first + coordinateJet coordinate second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact smul_add _ _ _

theorem centerCoordinate_smul {dimension : ℕ} (coordinate : Fin 2) (scalar : ℂ) (field : ClosedJet dimension) :
    coordinateJet coordinate (scalar • field) = scalar • coordinateJet coordinate field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact smul_comm _ _ _

theorem centerPartial_coordinate {dimension : ℕ} (direction coordinate : Fin 2) (field : ClosedJet dimension) :
    partialJet direction (coordinateJet coordinate field) =
      ((spatialBasis direction coordinate : ℝ) : ℂ) • field + coordinateJet coordinate (partialJet direction field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_add, ContinuousMap.add_apply,
    closedJet_value_smul, ContinuousMap.smul_apply, coordinateJet_value, Complex.coe_smul]
  exact partialJet_coordinate_value direction coordinate field point

theorem centerPartial_commute {dimension : ℕ} (first second : Fin 2) (field : ClosedJet dimension) :
    partialJet first (partialJet second field) = partialJet second (partialJet first field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change closedDerivative (partialJet second field) 1 (fun _ => first) point =
    closedDerivative (partialJet first field) 1 (fun _ => second) point
  rw [partialJet_closedDerivative, partialJet_closedDerivative, closedDerivative_eq_multi, closedDerivative_eq_multi]
  congr 2
  fin_cases first <;> fin_cases second <;> decide

theorem centerCoordinate_decomposition {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension) :
    coordinateMultiplyJet sign field = coordinateJet 0 field + (Complex.I * (sign : ℂ)) • coordinateJet 1 field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateMultiplyJet_value, closedJet_value_add, ContinuousMap.add_apply,
    closedJet_value_smul, ContinuousMap.smul_apply, coordinateJet_value, coordinateJet_value]
  simp only [signedComplexCoordinate, add_smul, mul_smul, Complex.coe_smul]

theorem radiusPower_one_decomposition {dimension : ℕ} (field : ClosedJet dimension) :
    radiusPowerJet 1 field = coordinateJet 0 (coordinateJet 0 field) + coordinateJet 1 (coordinateJet 1 field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [radiusPowerJet_value, pow_one, radiusSquare, closedJet_value_add,
    ContinuousMap.add_apply, coordinateJet_value, pow_two, add_smul, mul_smul]

end Grad.ActualCenterVolterra
