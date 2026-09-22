import AKBE18PuncturedPolarProjector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.PhysicalAxisEquation
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedAxisRemoval
open Grad.GaugeCoefficients.Physical.RadialLedger

def originalPlanarDivergence (flux : Fin 2 → Fin 2 → Spatial → ℂ) (point : Spatial) : ComplexEuclidean 2 :=
  WithLp.toLp 2 (fun coordinate => ∑ direction : Fin 2, directionDerivative direction (flux coordinate direction) point)

/-- The exact projected classical equation, together with the native flux
and flux/r integrability, supplies the original whole-disk projected weak
equation. All projector and axis-cutoff identities are discharged here. -/
theorem originalProjectedDivergence_weak
    (flux : Fin 2 → Fin 2 → Spatial → ℂ) (source : Spatial → ComplexEuclidean 2)
    (fluxSmooth : ∀ coordinate direction, ContDiffOn ℝ ∞ (flux coordinate direction) (openUnitDisk \ {(0 : Spatial)}))
    (sourceContinuous : ContinuousOn source (openUnitDisk \ {(0 : Spatial)}))
    (sourceIntegrable : ∀ coordinate, IntegrableOn (fun point => source point coordinate) openUnitDisk)
    (fluxIntegrable : ∀ coordinate direction, IntegrableOn (flux coordinate direction) openUnitDisk)
    (weightedIntegrable : ∀ coordinate direction,
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖flux coordinate direction point‖) openUnitDisk)
    (equation : ∀ point : ClosedDisk, 0 < ‖point.val‖ → ‖point.val‖ < 1 →
      closedRadialReflectionValue (fun closed : ClosedDisk => source closed.val) point =
      closedRadialReflectionValue (fun closed : ClosedDisk => originalPlanarDivergence flux closed.val) point) :
    ∀ output (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∑ coordinate : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest output test coordinate point • source point coordinate) =
      -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in openUnitDisk,
        fderiv ℝ (startupRawQradTest output test coordinate) point (spatialDirection direction) • flux coordinate direction point) := by
  have openPunctured : IsOpen (openUnitDisk \ {(0 : Spatial)}) := openUnitDisk_isOpen.sdiff isClosed_singleton
  have divergenceContinuous : ContinuousOn (originalPlanarDivergence flux) (openUnitDisk \ {(0 : Spatial)}) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro coordinate
    exact continuousOn_finsetSum _ (fun direction _ =>
      (directionDerivative_smooth openPunctured direction (fluxSmooth coordinate direction)).continuousOn)
  apply projectedForce_equation_remove_axis openUnitDisk (fun coordinate point => source point coordinate) flux
    sourceIntegrable fluxIntegrable weightedIntegrable startupRawQradTest
    startupRawQradTest_smooth startupRawQradTest_compact startupRawQradTest_axisCutoff
  intro output test smooth compact supported away
  have projectedSource := puncturedRadialProjection_rawTranspose source sourceContinuous output test smooth compact supported away
  have projectedFlux := puncturedRadialProjection_rawTranspose (originalPlanarDivergence flux) divergenceContinuous
    output test smooth compact supported away
  have sameProjection : (∫ point in openUnitDisk, test point • closedFieldExtension
      (closedRadialReflectionValue (fun closed : ClosedDisk => source closed.val)) point output) =
      ∫ point in openUnitDisk, test point • closedFieldExtension
        (closedRadialReflectionValue (fun closed : ClosedDisk => originalPlanarDivergence flux closed.val)) point output := by
    apply integral_congr_ae
    have punctured : ∀ᵐ point ∂volume.restrict openUnitDisk, point ∈ openUnitDisk \ {(0 : Spatial)} := by
      rw [← puncturedDisk_restrict_measure]
      exact ae_restrict_mem openPunctured.measurableSet
    filter_upwards [punctured] with point inside
    let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.1.le⟩
    have positive : 0 < ‖point‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using inside.2)
    have actual := equation closed positive inside.1
    have firstAt := closedFieldExtension_value (closedRadialReflectionValue (fun closed : ClosedDisk => source closed.val)) closed
    have secondAt := closedFieldExtension_value (closedRadialReflectionValue (fun closed : ClosedDisk => originalPlanarDivergence flux closed.val)) closed
    rw [firstAt,secondAt,actual]
  rw [← projectedSource,sameProjection,projectedFlux]
  calc
    _ = ∑ coordinate : Fin 2, -(∑ direction : Fin 2, ∫ point in openUnitDisk,
        fderiv ℝ (startupRawQradTest output test coordinate) point (spatialDirection direction) • flux coordinate direction point) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      exact punctured_classical_divergence_weak (flux coordinate) (fun point => originalPlanarDivergence flux point coordinate)
        (fluxSmooth coordinate) (fun _ _ => rfl) (startupRawQradTest output test coordinate)
        (startupRawQradTest_smooth output test smooth coordinate) (startupRawQradTest_compact output test compact coordinate)
        (originalRawQradTest_supported output coordinate test smooth compact supported)
        (originalRawQradTest_away output coordinate test away)
    _ = _ := by rw [Finset.sum_neg_distrib]

end Grad.ActualCartesianWeakEquations
