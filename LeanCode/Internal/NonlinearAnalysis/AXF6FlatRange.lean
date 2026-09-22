import AXF5SourceProjector

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore

variable {parameters : PhaseParameters}

theorem traceZero_flatSourceProjection_zero (source : SmoothQuotient parameters) :
    traceZero (flatSourceProjection source 0) = 0 := by
  rw [flatSourceProjection_apply, meanPair_apply, modeProjection_apply]
  change traceZero (source 0 - firstMode parameters source -
    radialValueInsertion (traceZero (source 0 - firstMode parameters source)) -
    Complex.I • (radialFirstInsertion 0 (affineTrace parameters source) +
      Complex.I • radialFirstInsertion 1 (affineTrace parameters source)) - 0) = 0
  simp only [map_sub, map_add, map_smul, traceZero_radialValueInsertion,
    traceZero_radialFirstInsertion, smul_zero, add_zero, sub_zero, sub_self]

theorem traceZero_flatSourceProjection_one (source : SmoothQuotient parameters) :
    traceZero (flatSourceProjection source 1) = 0 := by
  rw [flatSourceProjection_apply, meanPair_apply, modeProjection_apply]
  change traceZero (source 1 - reflection parameters (firstMode parameters source) -
    radialValueInsertion (traceZero (source 1 - reflection parameters (firstMode parameters source))) -
    (-Complex.I) • (radialFirstInsertion 0 (affineTrace parameters source) -
      Complex.I • radialFirstInsertion 1 (affineTrace parameters source)) - 0) = 0
  simp only [map_sub, map_smul, traceZero_radialValueInsertion,
    traceZero_radialFirstInsertion, smul_zero, sub_zero, sub_self]

def IsFlat (source : SmoothQuotient parameters) : Prop :=
  IsConstrained parameters source ∧ traceZero (source 0) = 0 ∧ traceZero (source 1) = 0 ∧
    ∀ direction, traceFirst direction (source 3) = 0

theorem flatSourceProjection_flat (source : SmoothQuotient parameters) :
    IsFlat (flatSourceProjection source) := by
  refine ⟨flatSourceProjection_constrained source, traceZero_flatSourceProjection_zero source,
    traceZero_flatSourceProjection_one source, ?_⟩
  intro direction
  rw [flatSourceProjection_fourth, traceFirst_scalarFlatProjection]

theorem valueCorrection_zero (source : SmoothQuotient parameters)
    (first : traceZero (source 0) = 0) (second : traceZero (source 1) = 0) :
    valueCorrection source = 0 := by
  funext coordinate
  fin_cases coordinate
  · change radialValueInsertion (traceZero (source 0)) = 0
    rw [first, map_zero]
  · change radialValueInsertion (traceZero (source 1)) = 0
    rw [second, map_zero]
  · rfl
  · rfl

theorem fourthCorrection_zero (source : SmoothQuotient parameters)
    (mean : angularCore parameters 0 (source 3) = 0)
    (gradient : ∀ direction, traceFirst direction (source 3) = 0) :
    fourthCorrection source = 0 := by
  funext coordinate
  fin_cases coordinate
  · rfl
  · rfl
  · rfl
  · change scalarGradientCorrection (source 3 - angularCore parameters 0 (source 3)) = 0
    rw [mean, sub_zero, scalarGradientCorrection_apply, gradient, gradient, map_zero, map_zero, add_zero]

theorem flatSourceProjection_fixes (source : SmoothQuotient parameters) (flat : IsFlat source) :
    flatSourceProjection source = source := by
  obtain ⟨⟨fourth, third, modes, affine⟩, firstValue, secondValue, gradient⟩ := flat
  rw [flatSourceProjection_apply, modes, affine, map_zero]
  simp only [sub_zero]
  rw [valueCorrection_zero source firstValue secondValue,
    fourthCorrection_zero source fourth gradient, sub_zero, sub_zero,
    meanPair_apply, third, fourth, sub_zero, sub_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

theorem flatSourceProjection_idempotent (source : SmoothQuotient parameters) :
    flatSourceProjection (flatSourceProjection source) = flatSourceProjection source :=
  flatSourceProjection_fixes _ (flatSourceProjection_flat source)

theorem flatSourceProjection_range (source : SmoothQuotient parameters) :
    source ∈ LinearMap.range (flatSourceProjection (parameters := parameters)) ↔ IsFlat source := by
  constructor
  · rintro ⟨other, rfl⟩
    exact flatSourceProjection_flat other
  · intro flat
    exact ⟨source, flatSourceProjection_fixes source flat⟩

end Grad.FlatSourceProjection
