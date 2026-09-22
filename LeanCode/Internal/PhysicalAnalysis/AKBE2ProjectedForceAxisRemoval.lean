import AKBE1OriginalCellDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.WeakTesting Grad.WeightedAxisRemoval Grad.ActualAnnularExhaustion

/-- The actual radial projector's compact-test transpose may be kept on the
tests throughout axis removal. Radial cutoff commutation is the only extra
property needed beyond the accepted flux and flux/r convergence estimates. -/
theorem projectedForce_equation_remove_axis
    (domain : Set Spatial)
    (source : Fin 2 → Spatial → ℂ) (flux : Fin 2 → Fin 2 → Spatial → ℂ)
    (sourceIntegrable : ∀ coordinate, IntegrableOn (source coordinate) domain)
    (fluxIntegrable : ∀ coordinate direction, IntegrableOn (flux coordinate direction) domain)
    (weightedIntegrable : ∀ coordinate direction,
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖flux coordinate direction point‖) domain)
    (projectTest : Fin 2 → (Spatial → ℝ) → Fin 2 → Spatial → ℝ)
    (projectSmooth : ∀ output test, ContDiff ℝ ∞ test → ∀ coordinate,
      ContDiff ℝ ∞ (projectTest output test coordinate))
    (projectCompact : ∀ output test, HasCompactSupport test → ∀ coordinate,
      HasCompactSupport (projectTest output test coordinate))
    (cutoffCommutes : ∀ output epsilon test coordinate,
      projectTest output (axisCutoffTest epsilon test) coordinate =
        axisCutoffTest epsilon (projectTest output test coordinate))
    (punctured : ∀ output (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ domain → (0 : Spatial) ∉ tsupport test →
      (∑ coordinate : Fin 2, ∫ point in domain, projectTest output test coordinate point • source coordinate point) =
        -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in domain,
          fderiv ℝ (projectTest output test coordinate) point (spatialDirection direction) • flux coordinate direction point)) :
    ∀ output (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
      (∑ coordinate : Fin 2, ∫ point in domain, projectTest output test coordinate point • source coordinate point) =
        -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in domain,
          fderiv ℝ (projectTest output test coordinate) point (spatialDirection direction) • flux coordinate direction point) := by
  intro output test smooth compact supported
  have away : ∀ᵐ point ∂volume.restrict domain, point ≠ (0 : Spatial) := by simp [ae_iff]
  let epsilon := originalExhaustionRadius (1 : ℝ)
  have positive : ∀ index, 0 < epsilon index := originalExhaustionRadius_positive 1 (by norm_num)
  have vanishing : Tendsto epsilon atTop (𝓝 0) := originalExhaustionRadius_tendsto 1
  have left := tendsto_finsetSum Finset.univ (fun coordinate _ =>
    axisCutoffTest_integral_tendsto (volume.restrict domain) away epsilon positive vanishing
      (projectTest output test coordinate) (projectSmooth output test smooth coordinate)
      (projectCompact output test compact coordinate) (source coordinate) (sourceIntegrable coordinate))
  have right := (tendsto_finsetSum Finset.univ (fun coordinate _ =>
    tendsto_finsetSum Finset.univ (fun direction _ =>
      axisCutoffTest_derivative_integral_tendsto (volume.restrict domain) away epsilon positive vanishing
        (projectTest output test coordinate) (projectSmooth output test smooth coordinate)
        (projectCompact output test compact coordinate) (flux coordinate direction)
        (fluxIntegrable coordinate direction) (weightedIntegrable coordinate direction) (spatialDirection direction)))).neg
  have equality (index : ℕ) :
      (∑ coordinate : Fin 2, ∫ point in domain,
        axisCutoffTest (epsilon index) (projectTest output test coordinate) point • source coordinate point) =
      -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in domain,
        fderiv ℝ (axisCutoffTest (epsilon index) (projectTest output test coordinate)) point (spatialDirection direction) •
          flux coordinate direction point) := by
    simpa only [cutoffCommutes] using punctured output (axisCutoffTest (epsilon index) test)
      (axisCutoffTest_smooth _ test smooth) (axisCutoffTest_compact _ test compact)
      ((axisCutoffTest_support _ test).trans supported) (axisCutoffTest_away _ (positive index) test)
  exact tendsto_nhds_unique (left.congr' (Eventually.of_forall equality)) right

end Grad.ActualCartesianWeakEquations
