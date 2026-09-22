import AXL1CutoffJets

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.ChartAxisSplit

variable {parameters : PhaseParameters}

theorem tameScalarMultiplier_zeroJets {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (coefficient : TameCoefficient parameters) (field : ACore parameters dimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.val cell)) (cell : ℤ) :
    ZeroCartesianFirstJets ((tameScalarMultiplier dimension coefficient field).val cell) :=
  Gauges.smoothMultiplier_preserves_zero_first_jets parameters _ _ field zeroJets cell

theorem valueMap_zeroJets {inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (field : ACore parameters inputDimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.val cell)) (cell : ℤ) :
    ZeroCartesianFirstJets ((valueMapCore parameters mapping field).val cell) := by
  intro order bounded word
  exact valueMapJet_preserves_zero_derivatives mapping (field.val cell)
    (fun innerWord => zeroJets cell order bounded innerWord) word

def capSeedField (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) : ACore parameters 3 :=
  valueMapCore parameters tamePlanarInclusion
    (Gauges.seedMatrixCore parameters seed inside (capPlanarCoordinate parameters radius positive))

theorem capSeedField_difference_zeroJets (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (cell : ℤ) :
    ZeroCartesianFirstJets ((capSeedField parameters radius positive seed inside -
      tameSeedField parameters seed inside).val cell) := by
  rw [capSeedField, tameSeedField, tameSeedPlanarField, ← map_sub, ← map_sub]
  exact valueMap_zeroJets _ _
    (Gauges.seedMatrixCore_zero_first_jets parameters seed inside _
      (capPlanarCoordinate_difference_zeroJets parameters radius positive)) cell

/-- Literal chi Q(c,eta)y. The actual root derivative is supplied as c;
the accompanying chart remainder below is chi Q minus Q, not the physical field. -/
def capAffineField (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    ACore parameters 3 :=
  tameScalarMultiplier 3 coefficient (capSeedField parameters radius positive seed inside) +
    valueMapCore parameters tameTangentInclusion
      (tameScalarMultiplier 1 (tangentComponent tangent 0) (capScalarCoordinate parameters radius positive 0) +
        tameScalarMultiplier 1 (tangentComponent tangent 1) (capScalarCoordinate parameters radius positive 1))

def capChartRemainder (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    ACore parameters 3 :=
  capAffineField parameters radius positive seed inside coefficient tangent -
    chartAffineField parameters seed inside coefficient tangent 0

theorem capChartRemainder_zeroJets (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) (cell : ℤ) :
    ZeroCartesianFirstJets ((capChartRemainder parameters radius positive seed inside coefficient tangent).val cell) := by
  have expansion : capChartRemainder parameters radius positive seed inside coefficient tangent =
      tameScalarMultiplier 3 coefficient (capSeedField parameters radius positive seed inside -
        tameSeedField parameters seed inside) +
      valueMapCore parameters tameTangentInclusion
        (tameScalarMultiplier 1 (tangentComponent tangent 0)
            (capScalarCoordinate parameters radius positive 0 - tameCoordinateScalarField parameters 0) +
          tameScalarMultiplier 1 (tangentComponent tangent 1)
            (capScalarCoordinate parameters radius positive 1 - tameCoordinateScalarField parameters 1)) := by
    unfold capChartRemainder capAffineField chartAffineField
    simp only [map_add, map_sub]
    abel
  rw [expansion]
  apply Gauges.zeroJets_add
  · exact tameScalarMultiplier_zeroJets coefficient _
      (capSeedField_difference_zeroJets radius positive seed inside) cell
  · apply valueMap_zeroJets
    intro innerCell
    exact Gauges.zeroJets_add
      (tameScalarMultiplier_zeroJets _ _ (capScalarCoordinate_difference_zeroJets parameters radius positive 0) innerCell)
      (tameScalarMultiplier_zeroJets _ _ (capScalarCoordinate_difference_zeroJets parameters radius positive 1) innerCell)

theorem chartAffineField_capRemainder (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    chartAffineField parameters seed inside coefficient tangent
      (capChartRemainder parameters radius positive seed inside coefficient tangent) =
        capAffineField parameters radius positive seed inside coefficient tangent := by
  unfold capChartRemainder chartAffineField
  abel

end Grad.ChartAxisLift
