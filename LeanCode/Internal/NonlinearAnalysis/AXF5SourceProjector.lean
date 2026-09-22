import AXF4SpinCorrections

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore

variable {parameters : PhaseParameters}

def scalarGradientCorrection : ACore parameters 1 →ₗ[ℂ] ACore parameters 1 :=
  (radialFirstInsertion 0).comp (traceFirst 0) + (radialFirstInsertion 1).comp (traceFirst 1)

def scalarFlatProjection : ACore parameters 1 →ₗ[ℂ] ACore parameters 1 :=
  (LinearMap.id - scalarGradientCorrection).comp (LinearMap.id - angularCore parameters 0)

theorem scalarGradientCorrection_apply (field : ACore parameters 1) :
    scalarGradientCorrection field =
      radialFirstInsertion 0 (traceFirst 0 field) + radialFirstInsertion 1 (traceFirst 1 field) := rfl

theorem scalarFlatProjection_apply (field : ACore parameters 1) :
    scalarFlatProjection field = field - angularCore parameters 0 field -
      scalarGradientCorrection (field - angularCore parameters 0 field) := rfl

theorem scalarGradientCorrection_mean (field : ACore parameters 1) :
    angularCore parameters 0 (scalarGradientCorrection field) = 0 := by
  rw [scalarGradientCorrection_apply, map_add, radialFirstInsertion_mean, radialFirstInsertion_mean, add_zero]

theorem traceFirst_scalarGradientCorrection (direction : Fin 2) (field : ACore parameters 1) :
    traceFirst direction (scalarGradientCorrection field) = traceFirst direction field := by
  rw [scalarGradientCorrection_apply, map_add, traceFirst_radialFirstInsertion, traceFirst_radialFirstInsertion]
  fin_cases direction <;> norm_num

theorem scalarFlatProjection_mean (field : ACore parameters 1) :
    angularCore parameters 0 (scalarFlatProjection field) = 0 := by
  rw [scalarFlatProjection_apply, map_sub, map_sub, scalarGradientCorrection_mean,
    angularCore_projection, if_pos rfl, sub_self, sub_zero]

theorem traceFirst_scalarFlatProjection (direction : Fin 2) (field : ACore parameters 1) :
    traceFirst direction (scalarFlatProjection field) = 0 := by
  rw [scalarFlatProjection_apply, map_sub, traceFirst_scalarGradientCorrection, sub_self]

theorem scalarFlatProjection_fixes (field : ACore parameters 1)
    (mean : angularCore parameters 0 field = 0)
    (gradient : ∀ direction, traceFirst direction field = 0) :
    scalarFlatProjection field = field := by
  rw [scalarFlatProjection_apply, mean, sub_zero, scalarGradientCorrection_apply,
    gradient, gradient, map_zero, map_zero, add_zero, sub_zero]

def fourthCorrection : SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi ![0, 0, 0, scalarGradientCorrection.comp
    ((LinearMap.id - angularCore parameters 0).comp (LinearMap.proj 3))]

/-- BS6 in the unchanged spin coordinates. Its fixed radial M28 profiles
come from averaging the accepted fixed bump, never the current-state lift. -/
def flatSourceProjection : SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  meanPair parameters - modeProjection parameters -
    valueCorrection.comp (LinearMap.id - modeProjection parameters) -
    radialAffineInsertion.comp (affineTrace parameters) - fourthCorrection

theorem flatSourceProjection_apply (source : SmoothQuotient parameters) :
    flatSourceProjection source = meanPair parameters source - modeProjection parameters source -
      valueCorrection (source - modeProjection parameters source) -
      radialAffineInsertion (affineTrace parameters source) - fourthCorrection source := rfl

theorem flatSourceProjection_third (source : SmoothQuotient parameters) :
    flatSourceProjection source 2 = source 2 - angularCore parameters 0 (source 2) := by
  rw [flatSourceProjection_apply, meanPair_apply, modeProjection_apply]
  change (source 2 - angularCore parameters 0 (source 2)) - 0 - 0 - 0 - 0 = _
  simp

theorem flatSourceProjection_fourth (source : SmoothQuotient parameters) :
    flatSourceProjection source 3 = scalarFlatProjection (source 3) := by
  rw [flatSourceProjection_apply, meanPair_apply, modeProjection_apply, scalarFlatProjection_apply]
  change (source 3 - angularCore parameters 0 (source 3)) - 0 - 0 - 0 -
    scalarGradientCorrection (source 3 - angularCore parameters 0 (source 3)) = _
  simp

theorem firstMode_fourthCorrection (source : SmoothQuotient parameters) :
    firstMode parameters (fourthCorrection source) = 0 := by
  change (1 / 2 : ℂ) • (angularCore parameters 1 0 + reflection parameters (angularCore parameters (-1) 0)) = 0
  simp

theorem modeProjection_fourthCorrection (source : SmoothQuotient parameters) :
    modeProjection parameters (fourthCorrection source) = 0 := by
  rw [modeProjection_apply, firstMode_fourthCorrection, map_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

theorem affineTrace_fourthCorrection (source : SmoothQuotient parameters) :
    affineTrace parameters (fourthCorrection source) = 0 := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 0 - Complex.I • traceFirst 1 0) -
      (traceFirst 0 0 + Complex.I • traceFirst 1 0)) = 0
  simp

theorem modeProjection_flatSourceProjection (source : SmoothQuotient parameters) :
    modeProjection parameters (flatSourceProjection source) = 0 := by
  rw [flatSourceProjection_apply, map_sub, map_sub, map_sub, map_sub,
    modeProjection_meanPair, modeProjection_idempotent, modeProjection_valueCorrection,
    modeProjection_radialAffineInsertion, modeProjection_fourthCorrection]
  simp

theorem affineTrace_flatSourceProjection (source : SmoothQuotient parameters) :
    affineTrace parameters (flatSourceProjection source) = 0 := by
  rw [flatSourceProjection_apply, map_sub, map_sub, map_sub, map_sub,
    affineTrace_meanPair, affineTrace_modeProjection, affineTrace_valueCorrection,
    affineTrace_radialAffineInsertion, affineTrace_fourthCorrection]
  simp

theorem flatSourceProjection_constrained (source : SmoothQuotient parameters) :
    IsConstrained parameters (flatSourceProjection source) := by
  refine ⟨?_, ?_, modeProjection_flatSourceProjection source, affineTrace_flatSourceProjection source⟩
  · rw [flatSourceProjection_fourth, scalarFlatProjection_mean]
  · rw [flatSourceProjection_third, map_sub, angularCore_projection, if_pos rfl, sub_self]

end Grad.FlatSourceProjection
