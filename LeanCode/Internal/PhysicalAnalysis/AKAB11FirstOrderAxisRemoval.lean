import AKAB10WeakCutoffTestConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.WeightedAxisRemoval
open Grad.PDEBootstrap Grad.WeakTesting Grad.ActualAnnularExhaustion

/-- Actual first-order weak equations extend through the axis once their
flux and flux/r are locally integrable. The proof constructs the radial
cutoff tests and takes their integrals to the limit; no distribution is
divided by r and no value or jet at the axis is assumed. -/
theorem firstOrder_equation_remove_axis {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (domain : Set Spatial) (flux : Fin 2 → Spatial → E) (source : Spatial → E)
    (sourceIntegrable : Integrable source (volume.restrict domain))
    (fluxIntegrable : ∀ index, Integrable (flux index) (volume.restrict domain))
    (weightedIntegrable : ∀ index, Integrable (fun point => ‖point‖⁻¹ * ‖flux index point‖) (volume.restrict domain))
    (punctured : ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ domain → (0 : Spatial) ∉ tsupport test →
      (∫ point in domain, test point • source point) =
        -(∑ index : Fin 2, ∫ point in domain,
          (fderiv ℝ test point (spatialDirection index)) • flux index point)) :
    ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ domain →
      (∫ point in domain, test point • source point) =
        -(∑ index : Fin 2, ∫ point in domain,
          (fderiv ℝ test point (spatialDirection index)) • flux index point) := by
  intro test smooth compact supported
  have away : ∀ᵐ point ∂volume.restrict domain, point ≠ (0 : Spatial) := by simp [ae_iff]
  let epsilon := originalExhaustionRadius (1 : ℝ)
  have positive : ∀ index, 0 < epsilon index := originalExhaustionRadius_positive 1 (by norm_num)
  have vanishing : Tendsto epsilon atTop (𝓝 0) := originalExhaustionRadius_tendsto 1
  have left := axisCutoffTest_integral_tendsto (volume.restrict domain) away epsilon positive vanishing
    test smooth compact source sourceIntegrable
  have right := (tendsto_finsetSum Finset.univ (fun index _ =>
    axisCutoffTest_derivative_integral_tendsto (volume.restrict domain) away epsilon positive vanishing
      test smooth compact (flux index) (fluxIntegrable index) (weightedIntegrable index) (spatialDirection index))).neg
  have equality (index : ℕ) :
      (∫ point in domain, axisCutoffTest (epsilon index) test point • source point) =
        -(∑ direction : Fin 2, ∫ point in domain,
          (fderiv ℝ (axisCutoffTest (epsilon index) test) point (spatialDirection direction)) • flux direction point) :=
    punctured _ (axisCutoffTest_smooth _ test smooth) (axisCutoffTest_compact _ test compact)
      ((axisCutoffTest_support _ test).trans supported) (axisCutoffTest_away _ (positive index) test)
  exact tendsto_nhds_unique (left.congr' (Eventually.of_forall equality)) right

end Grad.WeightedAxisRemoval
