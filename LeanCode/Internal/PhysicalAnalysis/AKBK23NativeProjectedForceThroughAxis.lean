import AKBK20OriginalProjectedFluxEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.Constraints Grad.Constraints.Gauges Grad.PDEBootstrap Grad.CartesianStartup
open Grad.PhysicalAxisEquation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The original native force equation crosses the axis using exactly the
accepted flux/r criterion and literal radial projector. -/
theorem nativePlanarForce_weak (xi : Spatial → ComplexEuclidean 1)
    (covariant correction : Spatial → ComplexEuclidean 3) (source : Spatial → ComplexEuclidean 2)
    (xiSmooth : ContDiffOn ℝ ∞ xi (openUnitDisk \ {(0 : Spatial)}))
    (covariantSmooth : ContDiffOn ℝ ∞ covariant (openUnitDisk \ {(0 : Spatial)}))
    (correctionContinuous : ContinuousOn correction (openUnitDisk \ {(0 : Spatial)}))
    (sourceContinuous : ContinuousOn source (openUnitDisk \ {(0 : Spatial)}))
    (xiIntegrable : IntegrableOn xi openUnitDisk)
    (xiWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖xi point‖) openUnitDisk)
    (covariantIntegrable : IntegrableOn covariant openUnitDisk)
    (covariantWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖covariant point‖) openUnitDisk)
    (correctionIntegrable : IntegrableOn correction openUnitDisk)
    (sourceIntegrable : IntegrableOn source openUnitDisk)
    (equation : ∀ point : ClosedDisk, 0 < ‖point.val‖ → ‖point.val‖ < 1 →
      closedRadialReflectionValue (fun closed : ClosedDisk => nativePlanarForceSource source covariant correction closed.val) point =
      closedRadialReflectionValue (fun closed : ClosedDisk => originalPlanarDivergence (nativePlanarForceFlux xi covariant) closed.val) point) :
    ∀ output (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∑ coordinate : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest output test coordinate point • nativePlanarForceSource source covariant correction point coordinate) =
      -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in openUnitDisk,
        fderiv ℝ (startupRawQradTest output test coordinate) point (spatialDirection direction) •
          nativePlanarForceFlux xi covariant coordinate direction point) := by
  let xiProjection := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ
  have scalarPair := boundedPhysicalFlux_integrable_pair openUnitDisk xi xiIntegrable xiWeighted
    (fun _ => xiProjection) aestronglyMeasurable_const ‖xiProjection‖ (Eventually.of_forall (fun _ => le_rfl))
  have planarPair := boundedPhysicalFlux_integrable_pair openUnitDisk covariant covariantIntegrable covariantWeighted
    (fun _ => planarPartMap.restrictScalars ℝ) aestronglyMeasurable_const ‖planarPartMap.restrictScalars ℝ‖
    (Eventually.of_forall (fun _ => le_rfl))
  have fluxPair := originalForceFlux_integrable_pair (fun point => xi point 0)
    (fun point => planarPartMap (covariant point)) scalarPair.1 scalarPair.2 planarPair.1 planarPair.2
  have quarterIntegrable := (quarterValueMap.restrictScalars ℝ).integrable_comp planarPair.1
  have correctionPlanar := (planarPartMap.restrictScalars ℝ).integrable_comp correctionIntegrable
  have rhsIntegrable : IntegrableOn (nativePlanarForceSource source covariant correction) openUnitDisk :=
    sourceIntegrable.add (quarterIntegrable.sub correctionPlanar)
  exact originalProjectedDivergence_weak (nativePlanarForceFlux xi covariant) (nativePlanarForceSource source covariant correction)
    (nativePlanarForceFlux_smooth xi covariant xiSmooth covariantSmooth)
    (sourceContinuous.add (nativePlanarForceLower_continuous covariant correction covariantSmooth.continuousOn correctionContinuous))
    (fun coordinate => ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) coordinate).restrictScalars ℝ).integrable_comp rhsIntegrable)
    (fun coordinate direction => (fluxPair coordinate direction).1)
    (fun coordinate direction => (fluxPair coordinate direction).2) equation

end Grad.ActualCartesianWeakEquations
