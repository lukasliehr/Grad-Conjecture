import AKBE3AngularTransportDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.RepresentedKernel.SpatialProduct Grad.PhysicalAxisEquation
open Grad.ActualSmoothPhysicalField Grad.PhysicalFamily Grad.WeightedAxisRemoval Grad.ClosedJets

/-- The genuine angular row passes through the axis with its original
Cartesian transport flux. This applies before H1 to the integrable physical
covariant field, using its already proved punctured classical equation. -/
theorem originalRotation_equation_remove_axis {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (field : Spatial → E) (fieldIntegrable : IntegrableOn field openUnitDisk)
    (weightedIntegrable : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk)
    (source : Spatial → E) (sourceIntegrable : IntegrableOn source openUnitDisk)
    (smooth : ContDiffOn ℝ ∞ field (openUnitDisk \ {(0 : Spatial)}))
    (equation : ∀ point ∈ openUnitDisk \ {(0 : Spatial)},
      source point = fderiv ℝ field point (planeQuarterTurn point)) :
    ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • source point) =
        -(∑ direction : Fin 2, ∫ point in openUnitDisk,
          fderiv ℝ test point (spatialDirection direction) • angularTransportFlux field direction point) := by
  have fluxPair := angularTransportFlux_integrable_pair field fieldIntegrable weightedIntegrable
  apply firstOrder_equation_remove_axis openUnitDisk (angularTransportFlux field) source sourceIntegrable
    (fun direction => (fluxPair direction).1) (fun direction => (fluxPair direction).2)
  apply punctured_classical_divergence_weak (angularTransportFlux field) source
    (fun direction => angularTransportFlux_smooth _ field smooth direction)
  intro point inside
  apply (equation point inside).trans
  symm
  exact angularTransportFlux_divergence field point
    ((smooth.contDiffAt ((openUnitDisk_isOpen.sdiff isClosed_singleton).mem_nhds inside)).differentiableAt (by simp))

end Grad.ActualCartesianWeakEquations
