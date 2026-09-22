import AXL0RadialCap

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.ChartAxisSplit

theorem zeroFirstJets_of_origin {dimension : ℕ} (field : ClosedJet dimension)
    (value : originValue field = 0) (partials : ∀ direction, originPartial direction field = 0) :
    ZeroCartesianFirstJets field := by
  intro order bounded word
  change closedDerivative field order word originPoint = 0
  have cases : order = 0 ∨ order = 1 := by omega
  rcases cases with rfl | rfl
  · have wordEq : word = emptyCartesianWord := Subsingleton.elim _ _
    rw [wordEq, closedDerivative_zero_order]
    exact value
  · have wordEq : word = fun _ => word 0 := by
      funext index
      congr 1
      exact Fin.eq_zero index
    rw [wordEq]
    exact partials (word 0)

theorem radialCapJet_sub_coordinate_zeroJets {dimension : ℕ} (radius : ℝ)
    (positive : 0 < radius) (coordinate : Fin 2) (vector : ComplexEuclidean dimension) :
    ZeroCartesianFirstJets (radialCapJet radius positive coordinate vector -
      coordinateJet coordinate (constantValueJet vector)) := by
  apply zeroFirstJets_of_origin
  · rw [originValue_sub, radialCapJet_originValue, coordinateJet_originValue, sub_self]
  · intro direction
    rw [originPartial_sub, radialCapJet_originPartial, coordinateJet_originPartial]
    by_cases same : direction = coordinate
    · rw [if_pos same, if_pos same]
      change vector - vector = 0
      exact sub_self _
    · rw [if_neg same, if_neg same, sub_self]

theorem singletonCore_sub {dimension : ℕ} (parameters : PhaseParameters)
    (first second : ClosedJet dimension) :
    singletonCore parameters first - singletonCore parameters second =
      singletonCore parameters (first - second) := by
  apply Subtype.ext
  funext cell
  change (if cell = 0 then first else 0) - (if cell = 0 then second else 0) = _
  by_cases zeroCell : cell = 0 <;> simp [singletonCore_val, zeroCell]

theorem singletonCore_zeroJets {dimension : ℕ} (parameters : PhaseParameters)
    (field : ClosedJet dimension) (zeroJets : ZeroCartesianFirstJets field) (cell : ℤ) :
    ZeroCartesianFirstJets ((singletonCore parameters field).val cell) := by
  rw [singletonCore_val]
  by_cases zeroCell : cell = 0
  · simpa only [if_pos zeroCell] using zeroJets
  · rw [if_neg zeroCell]
    apply zeroFirstJets_of_origin
    · exact originValue_zero
    · exact originPartial_zero

def capCoordinateCore (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    {dimension : ℕ} (coordinate : Fin 2) (vector : ComplexEuclidean dimension) :
    ACore parameters dimension := singletonCore parameters (radialCapJet radius positive coordinate vector)

theorem capCoordinateCore_difference_zeroJets (parameters : PhaseParameters) (radius : ℝ)
    (positive : 0 < radius) {dimension : ℕ} (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) (cell : ℤ) :
    ZeroCartesianFirstJets ((capCoordinateCore parameters radius positive coordinate vector -
      singletonCore parameters (coordinateJet coordinate (constantValueJet vector))).val cell) := by
  rw [capCoordinateCore, singletonCore_sub]
  exact singletonCore_zeroJets parameters _
    (radialCapJet_sub_coordinate_zeroJets radius positive coordinate vector) cell

def capScalarCoordinate (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (coordinate : Fin 2) : ACore parameters 1 :=
  capCoordinateCore parameters radius positive coordinate (EuclideanSpace.single 0 1)

def capPlanarCoordinate (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius) :
    ACore parameters 2 :=
  capCoordinateCore parameters radius positive 0 (EuclideanSpace.single 0 1) +
    capCoordinateCore parameters radius positive 1 (EuclideanSpace.single 1 1)

theorem capScalarCoordinate_difference_zeroJets (parameters : PhaseParameters) (radius : ℝ)
    (positive : 0 < radius) (coordinate : Fin 2) (cell : ℤ) :
    ZeroCartesianFirstJets ((capScalarCoordinate parameters radius positive coordinate -
      tameCoordinateScalarField parameters coordinate).val cell) :=
  capCoordinateCore_difference_zeroJets parameters radius positive coordinate _ cell

theorem capPlanarCoordinate_difference_zeroJets (parameters : PhaseParameters) (radius : ℝ)
    (positive : 0 < radius) (cell : ℤ) :
    ZeroCartesianFirstJets ((capPlanarCoordinate parameters radius positive -
      tamePlanarCoordinateField parameters).val cell) := by
  have expansion : capPlanarCoordinate parameters radius positive - tamePlanarCoordinateField parameters =
      (capCoordinateCore parameters radius positive 0 (EuclideanSpace.single 0 1) -
        singletonCore parameters (coordinateJet 0 (constantValueJet (EuclideanSpace.single 0 1)))) +
      (capCoordinateCore parameters radius positive 1 (EuclideanSpace.single 1 1) -
        singletonCore parameters (coordinateJet 1 (constantValueJet (EuclideanSpace.single 1 1)))) := by
    unfold capPlanarCoordinate tamePlanarCoordinateField
    abel
  rw [expansion]
  exact Gauges.zeroJets_add
    (capCoordinateCore_difference_zeroJets parameters radius positive 0 _ cell)
    (capCoordinateCore_difference_zeroJets parameters radius positive 1 _ cell)

end Grad.ChartAxisLift
