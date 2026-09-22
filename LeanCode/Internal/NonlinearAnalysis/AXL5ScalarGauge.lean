import AXL4RadialActions
import PCO2PhysicalChartRange
import CP9ModeAnnihilation

noncomputable section

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.PhysicalCoordinates

theorem angularClosedJet_constant (dimension : ℕ) (mode : ℤ) (vector : ComplexEuclidean dimension) :
    angularClosedJet mode (constantValueJet vector) =
      if mode = 0 then constantValueJet vector else 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value]
  simp only [constantValueJet_value]
  rw [angularCharacter_normalized_integral]
  by_cases same : mode = 0
  · rw [if_pos same, if_pos same, constantValueJet_value]
  · rw [if_neg same, if_neg same, closedJet_value_zero]
    rfl

theorem coordinateJet_eq_realCoordinateJet {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    coordinateJet coordinate field = Gauges.realCoordinateJet coordinate field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateJet_value, Gauges.realCoordinateJet_value]

theorem angularClosedJet_coordinateConstant_zero {dimension : ℕ} (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) :
    angularClosedJet 0 (coordinateJet coordinate (constantValueJet vector)) = 0 := by
  rw [coordinateJet_eq_realCoordinateJet]
  fin_cases coordinate
  · change angularClosedJet 0 (Gauges.realCoordinateJet 0 (constantValueJet vector)) = 0
    rw [Grad.Cor18.realCoordinateJet_zero_eq, angularClosedJet_smul, angularClosedJet_add,
      angularClosedJet_z, angularClosedJet_zbar, angularClosedJet_constant, angularClosedJet_constant]
    norm_num [Grad.Cor18.coordinateMultiplyJet_zero_jet]
  · change angularClosedJet 0 (Gauges.realCoordinateJet 1 (constantValueJet vector)) = 0
    rw [Grad.Cor18.realCoordinateJet_one_eq, angularClosedJet_add, angularClosedJet_smul,
      angularClosedJet_smul, angularClosedJet_z, angularClosedJet_zbar,
      angularClosedJet_constant, angularClosedJet_constant]
    norm_num [Grad.Cor18.coordinateMultiplyJet_zero_jet]

theorem angularClosedJet_radialCap_zero {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) (vector : ComplexEuclidean dimension) :
    angularClosedJet 0 (radialCapJet radius positive coordinate vector) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_factor 0 _ (coordinateJet coordinate (constantValueJet vector))
    (fun point => (radialCap radius positive point.val : ℂ))
    (radialCap_closedRadial radius positive) (radialCapJet_value_factor radius positive coordinate vector),
    angularClosedJet_coordinateConstant_zero, closedJet_value_zero]
  simp

theorem capScalarCoordinate_mean_zero (parameters : PhaseParameters) (radius : ℝ)
    (positive : 0 < radius) (coordinate : Fin 2) :
    angularCore parameters 0 (capScalarCoordinate parameters radius positive coordinate) = 0 := by
  apply Subtype.ext
  funext cell
  rw [angularCore_apply]
  change angularClosedJet 0 (if cell = 0 then radialCapJet radius positive coordinate
    (EuclideanSpace.single 0 1) else 0) = 0
  by_cases same : cell = 0
  · rw [if_pos same, angularClosedJet_radialCap_zero]
  · rw [if_neg same]
    exact (angularClosedJetLinear 1 0).map_zero

theorem scalarMultiplier_mean_zero {parameters : PhaseParameters} (coefficient : TameCoefficient parameters)
    (field : ACore parameters 1) (mean : angularCore parameters 0 field = 0) :
    angularCore parameters 0 (tameScalarMultiplier 1 coefficient field) = 0 := by
  have vanish : Grad.Cor18.ModesVanish ({0} : Set ℤ) field := by
    intro mode member
    have same : mode = 0 := member
    subst mode
    exact mean
  exact Grad.Cor18.modesVanish_smoothMultiplier (tameScalarOperator 1 coefficient.val)
    (tameScalarOperator_summable coefficient) vanish 0 rfl

/-- The actual scalar component chi(sigma dot y) of AL15. -/
def capScalarAffine (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) : ACore parameters 1 :=
  tameScalarMultiplier 1 (tangentComponent sigma 0) (capScalarCoordinate parameters radius positive 0) +
    tameScalarMultiplier 1 (tangentComponent sigma 1) (capScalarCoordinate parameters radius positive 1)

theorem capScalarAffine_mean_zero (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (sigma : TangentCoefficient parameters) : angularCore parameters 0 (capScalarAffine parameters radius positive sigma) = 0 := by
  rw [capScalarAffine, map_add,
    scalarMultiplier_mean_zero _ _ (capScalarCoordinate_mean_zero parameters radius positive 0),
    scalarMultiplier_mean_zero _ _ (capScalarCoordinate_mean_zero parameters radius positive 1), add_zero]

end Grad.ChartAxisLift
