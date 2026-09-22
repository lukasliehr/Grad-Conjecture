import AXF11ProjectorConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore

variable {parameters : PhaseParameters}

theorem angularClosedJet_zero_local {dimension : ℕ} (mode : ℤ) :
    angularClosedJet mode (0 : ClosedJet dimension) = 0 :=
  (angularClosedJetLinear dimension mode).map_zero

theorem profileJetZero_zero_local {dimension : ℕ} (cell : ℤ) :
    profileJetZero cell (0 : ComplexEuclidean dimension) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change profileScalarZero cell point.val • (0 : ComplexEuclidean dimension) = 0
  exact smul_zero _

theorem radialValueInsertion_zero_cell {dimension : ℕ}
    (data : AxisSmoothCore parameters dimension) (cell : ℤ) (zero : data.val cell = 0) :
    (radialValueInsertion data).val cell = 0 := by
  change angularClosedJet 0 (profileJetZero cell (data.val cell)) = 0
  rw [zero, profileJetZero_zero_local, angularClosedJet_zero_local]

theorem radialFirstInsertion_zero_cell {dimension : ℕ} (direction : Fin 2)
    (data : AxisSmoothCore parameters dimension) (cell : ℤ) (zero : data.val cell = 0) :
    (radialFirstInsertion direction data).val cell = 0 := by
  change coordinateJet direction ((radialValueInsertion data).val cell) = 0
  rw [radialValueInsertion_zero_cell data cell zero]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change point.val direction • (0 : ComplexEuclidean dimension) = 0
  exact smul_zero _

theorem firstMode_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) :
    (firstMode parameters source).val cell = 0 := by
  change (1 / 2 : ℂ) • (angularClosedJet 1 ((source 0).val cell) +
    orthogonalJet cartesianReflectionEquiv (angularClosedJet (-1) ((source 1).val cell))) = 0
  rw [zero, zero, angularClosedJet_zero_local, angularClosedJet_zero_local]
  change (1 / 2 : ℂ) • (0 + (orthogonalJetLinear 1 cartesianReflectionEquiv) 0) = 0
  rw [map_zero, add_zero, smul_zero]

theorem modeProjection_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) (row : Fin 4) :
    ((modeProjection parameters source) row).val cell = 0 := by
  rw [modeProjection_apply]
  fin_cases row
  · exact firstMode_zero_cell source cell zero
  · change orthogonalJet cartesianReflectionEquiv ((firstMode parameters source).val cell) = 0
    rw [firstMode_zero_cell source cell zero]
    exact (orthogonalJetLinear 1 cartesianReflectionEquiv).map_zero
  · rfl
  · rfl

theorem affineTrace_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) :
    (affineTrace parameters source).val cell = 0 := by
  change (4 * Complex.I)⁻¹ •
    ((originPartial 0 ((source 0).val cell) - Complex.I • originPartial 1 ((source 0).val cell)) -
      (originPartial 0 ((source 1).val cell) + Complex.I • originPartial 1 ((source 1).val cell))) = 0
  rw [zero, zero, originPartial_zero, originPartial_zero]
  simp

theorem traceZero_zero_cell {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) (zero : field.val cell = 0) :
    (traceZero field).val cell = 0 := by
  change originValue (field.val cell) = 0
  rw [zero]
  rfl

theorem traceFirst_zero_cell {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) (cell : ℤ) (zero : field.val cell = 0) :
    (traceFirst direction field).val cell = 0 := by
  change originPartial direction (field.val cell) = 0
  rw [zero, originPartial_zero]

theorem valueCorrection_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) (row : Fin 4) :
    ((valueCorrection source) row).val cell = 0 := by
  fin_cases row
  · exact radialValueInsertion_zero_cell _ cell (traceZero_zero_cell _ cell (zero 0))
  · exact radialValueInsertion_zero_cell _ cell (traceZero_zero_cell _ cell (zero 1))
  · rfl
  · rfl

theorem radialAffineInsertion_zero_cell (data : AxisSmoothCore parameters 1)
    (cell : ℤ) (zero : data.val cell = 0) (row : Fin 4) :
    ((radialAffineInsertion data) row).val cell = 0 := by
  fin_cases row
  · change Complex.I • ((radialFirstInsertion 0 data).val cell +
      Complex.I • (radialFirstInsertion 1 data).val cell) = 0
    rw [radialFirstInsertion_zero_cell _ data cell zero,
      radialFirstInsertion_zero_cell _ data cell zero]
    simp
  · change (-Complex.I) • ((radialFirstInsertion 0 data).val cell -
      Complex.I • (radialFirstInsertion 1 data).val cell) = 0
    rw [radialFirstInsertion_zero_cell _ data cell zero,
      radialFirstInsertion_zero_cell _ data cell zero]
    simp
  · rfl
  · rfl

theorem scalarGradientCorrection_zero_cell (field : ACore parameters 1)
    (cell : ℤ) (zero : field.val cell = 0) :
    (scalarGradientCorrection field).val cell = 0 := by
  change (radialFirstInsertion 0 (traceFirst 0 field)).val cell +
    (radialFirstInsertion 1 (traceFirst 1 field)).val cell = 0
  rw [radialFirstInsertion_zero_cell _ _ cell (traceFirst_zero_cell _ field cell zero),
    radialFirstInsertion_zero_cell _ _ cell (traceFirst_zero_cell _ field cell zero), add_zero]

theorem meanRemoved_zero_cell (field : ACore parameters 1)
    (cell : ℤ) (zero : field.val cell = 0) :
    (field - angularCore parameters 0 field).val cell = 0 := by
  change field.val cell - angularClosedJet 0 (field.val cell) = 0
  rw [zero, angularClosedJet_zero_local, sub_self]

theorem meanPair_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) (row : Fin 4) :
    ((meanPair parameters source) row).val cell = 0 := by
  rw [meanPair_apply]
  fin_cases row
  · exact zero 0
  · exact zero 1
  · exact meanRemoved_zero_cell _ cell (zero 2)
  · exact meanRemoved_zero_cell _ cell (zero 3)

theorem fourthCorrection_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) (row : Fin 4) :
    ((fourthCorrection source) row).val cell = 0 := by
  fin_cases row
  · rfl
  · rfl
  · rfl
  · exact scalarGradientCorrection_zero_cell _ cell (meanRemoved_zero_cell _ cell (zero 3))

/-- The fixed source flattening never creates a Fourier cell. -/
theorem flatSourceProjection_zero_cell (source : SmoothQuotient parameters) (cell : ℤ)
    (zero : ∀ row, (source row).val cell = 0) (row : Fin 4) :
    ((flatSourceProjection source) row).val cell = 0 := by
  have zeroDifference : ∀ row, ((source - modeProjection parameters source) row).val cell = 0 := by
    intro row
    change (source row).val cell - ((modeProjection parameters source) row).val cell = 0
    rw [zero, modeProjection_zero_cell source cell zero row, sub_self]
  rw [flatSourceProjection_apply]
  change ((meanPair parameters source) row).val cell -
    ((modeProjection parameters source) row).val cell -
    ((valueCorrection (source - modeProjection parameters source)) row).val cell -
    ((radialAffineInsertion (affineTrace parameters source)) row).val cell -
    ((fourthCorrection source) row).val cell = 0
  rw [meanPair_zero_cell source cell zero row, modeProjection_zero_cell source cell zero row,
    valueCorrection_zero_cell _ cell zeroDifference row,
    radialAffineInsertion_zero_cell _ cell (affineTrace_zero_cell source cell zero) row,
    fourthCorrection_zero_cell source cell zero row]
  simp

end Grad.FlatSourceProjection
