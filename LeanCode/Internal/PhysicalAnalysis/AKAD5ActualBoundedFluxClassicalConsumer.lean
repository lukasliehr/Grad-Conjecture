import AKAD4BoundedPhysicalFluxIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.PhysicalAxisEquation
open Grad.PDEBootstrap Grad.RepresentedKernel.SpatialProduct Grad.ClosedJets Grad.WeightedAxisRemoval

/-- Original physical U/S integrability suffices for normalized equations
whose fluxes are bounded actual coefficient multipliers. Their classical
punctured equations become ordinary whole-disk weak equations. -/
theorem boundedFlux_classical_equation_remove_axis {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (field : Spatial → E)
    (fieldIntegrable : IntegrableOn field openUnitDisk)
    (weightedIntegrable : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk)
    (coefficient : Fin 2 → Spatial → E →L[ℝ] F)
    (measurable : ∀ index, AEStronglyMeasurable (coefficient index) (volume.restrict openUnitDisk))
    (C : Fin 2 → ℝ) (bounded : ∀ index, ∀ᵐ point ∂volume.restrict openUnitDisk, ‖coefficient index point‖ ≤ C index)
    (source : Spatial → F) (sourceIntegrable : IntegrableOn source openUnitDisk)
    (smooth : ∀ index, ContDiffOn ℝ ∞ (fun point => coefficient index point (field point))
      (openUnitDisk \ {(0 : Spatial)}))
    (equation : ∀ point ∈ openUnitDisk \ {(0 : Spatial)}, source point =
      ∑ index : Fin 2, directionDerivative index (fun point => coefficient index point (field point)) point) :
    ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • source point) =
        -(∑ index : Fin 2, ∫ point in openUnitDisk,
          (fderiv ℝ test point (spatialDirection index)) • coefficient index point (field point)) := by
  have integrability (index : Fin 2) := boundedPhysicalFlux_integrable_pair openUnitDisk field
    fieldIntegrable weightedIntegrable (coefficient index) (measurable index) (C index) (bounded index)
  exact firstOrder_equation_remove_axis openUnitDisk (fun index point => coefficient index point (field point))
    source sourceIntegrable (fun index => (integrability index).1) (fun index => (integrability index).2)
    (punctured_classical_divergence_weak _ source smooth equation)

end Grad.PhysicalAxisEquation
