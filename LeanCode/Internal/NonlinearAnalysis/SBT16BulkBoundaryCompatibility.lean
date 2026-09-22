import SBT15TangentialGraphTrace
import SRC4LiteralCore

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarAngular Grad.SourceCollarBulk
open Grad.CompatibleCompletion Grad.FlatSourceProjection

/-- The independently constructed connectors are the same original
completed Cartesian source map, by the accepted dense smooth core. -/
theorem sourceCartesianCompleted_eq_originalSourcePlanar (parameters : PhaseParameters) (grade : ℕ) :
    sourceCartesianCompleted parameters grade = originalSourcePlanar parameters grade := by
  apply ContinuousLinearMap.ext
  exact congrFun ((quotientEta_denseRange parameters grade).equalizer
    (sourceCartesianCompleted parameters grade).continuous (originalSourcePlanar parameters grade).continuous
    (by
      funext core
      simp only [Function.comp_def]
      rw [sourceCartesianCompleted_core, originalSourcePlanar_core]))

theorem sourceComponent_eq_originalSourceComponent (parameters : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 4) :
    sourceComponent parameters grade coordinate = originalSourceComponent parameters grade coordinate := rfl

theorem highForceTrace_bulk_endpoint (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power : ℕ) (source : ZAmbient parameters (power + 2)) (mode : ℤ × ℤ) :
    (((completedForceTangential lower positive bounded parameters power source).val 0 mode,
      (completedForceTangential lower positive bounded parameters power source).val 1 mode),
      highForceTrace parameters power source mode) ∈ radialEndpointGraph 1 lower := by
  have actual := completedTangentialContraction_endpoint lower positive bounded parameters (power + 1)
    (originalSourcePlanar parameters (power + 2) source) mode
  simpa only [completedForceTangential, highForceTrace, ContinuousLinearMap.comp_apply,
    sourceCartesianCompleted_eq_originalSourcePlanar] using actual

/-- F0 is stored at nu^(t+1) in BS36; the outer s tuple uses nu^t.
The same factor lowers both its value and genuine radial derivative. -/
theorem forceOuterTrace_bulk_endpoint (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power : ℕ) (source : ZAmbient parameters (power + 2)) (mode : ℤ × ℤ) :
    ((((annularFrequency mode.1 mode.2 : ℂ)⁻¹) •
        (completedForceTangential lower positive bounded parameters power source).val 0 mode,
      ((annularFrequency mode.1 mode.2 : ℂ)⁻¹) •
        (completedForceTangential lower positive bounded parameters power source).val 1 mode),
      forceOuterTrace parameters power source mode) ∈ radialEndpointGraph 1 lower := by
  exact radialEndpointGraph_complex_smul lower ((annularFrequency mode.1 mode.2 : ℂ)⁻¹) _
    (highForceTrace_bulk_endpoint lower positive bounded parameters power source mode)

/-- RF0 is the actual completed angular derivative graph from BS36,
including the radial derivative of the fully phase-weighted RF0. -/
theorem rotationOuterTrace_bulk_endpoint (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power : ℕ) (source : ZAmbient parameters (power + 2)) (mode : ℤ × ℤ) :
    (((completedForceAngular lower positive bounded parameters power source).val 0 mode,
      (completedForceAngular lower positive bounded parameters power source).val 1 mode),
      rotationOuterTrace parameters power source mode) ∈ radialEndpointGraph 1 lower := by
  exact radialEndpointGraph_complex_smul lower (annularAngularRatio mode) _
    (highForceTrace_bulk_endpoint lower positive bounded parameters power source mode)

theorem fourthOuterTrace_bulk_endpoint (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (power : ℕ) (source : ZAmbient parameters (power + 2)) (mode : ℤ × ℤ) :
    (((completedFourthSource lower positive bounded parameters L power source).val 0 mode,
      (completedFourthSource lower positive bounded parameters L power source).val 1 mode),
      fourthOuterTrace parameters L power source mode) ∈ radialEndpointGraph 1 lower := by
  have trace := completedRestriction_endpoint lower positive bounded parameters power
    (completedInclusion parameters (show power + 1 ≤ power + 2 by omega)
      (originalSourceComponent parameters (power + 2) 3 source)) mode
  have actual := radialEndpointGraph_complex_smul lower ((L : ℂ)⁻¹) _ trace
  change (((completedFourthSource lower positive bounded parameters L power source).val 0 mode,
    (completedFourthSource lower positive bounded parameters L power source).val 1 mode),
    fourthOuterTrace parameters L power source mode) ∈ radialEndpointGraph 1 lower at actual
  exact actual

end Grad.SourceBoundaryTrace
