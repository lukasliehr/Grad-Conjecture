import ADW4ExactNormalizationEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A single genuine radial H1 mode, with the actual nu^-1 derivative. -/
def annularNuModeCoordinates (lower : ℝ) (mode : HighAnnularMode) :
    WeightedRadialH1 1 lower →L[ℝ] AnnularFluxGraphAmbient lower :=
  ((lp.singleContinuousLinearMap ℝ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode).comp
    (weightedRadialCoordinate 1 lower 0)).prod
  ((lp.singleContinuousLinearMap ℝ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode).comp
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ • weightedRadialCoordinate 1 lower 1))

theorem annularNuModeCoordinates_mem (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (field : WeightedRadialH1 1 lower) :
    annularNuModeCoordinates lower mode field ∈ annularFluxWeakGraph lower positive := by
  intro other
  change CollarWeakDerivative lower
    (radialOrdinary 1 lower positive ((lp.single 2 mode (weightedRadialCoordinate 1 lower 0 field) : AnnularBulk lower) other))
    ((Grad.AnnularVariational.annularFrequency other.val.1 other.val.2 : ℝ) •
      radialOrdinary 1 lower positive ((lp.single 2 mode
        ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ • weightedRadialCoordinate 1 lower 1 field) : AnnularBulk lower) other))
  by_cases same : other = mode
  · subst other
    simp only [lp.single_apply, Pi.single_eq_same]
    rw [(radialOrdinary 1 lower positive).map_smul_of_tower, smul_smul,
      mul_inv_cancel₀ (Grad.AnnularFluxTrace.annularFrequency_pos mode).ne', one_smul,
      weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le,
      weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le,
      radialOrdinary_sqrt, radialOrdinary_sqrt]
    exact weightedRadial_weak 1 lower positive bounded.le field
  · simp only [lp.single_apply, Pi.single_eq_of_ne same, map_zero, smul_zero]
    intro test vector
    simp only [map_zero, neg_zero]

/-- Finite Fourier sums of the accepted genuine infinitely smooth radial core. -/
def annularNuFiniteSmoothCore (lower : ℝ) :
    (HighAnnularMode →₀ SmoothRadialCore 1) →ₗ[ℝ] AnnularFluxGraphAmbient lower :=
  Finsupp.lsum ℝ (fun mode => (annularNuModeCoordinates lower mode).toLinearMap.comp
    (weightedRadialCoreInto 1 lower))

theorem annularNuFiniteSmoothCore_single (lower : ℝ) (mode : HighAnnularMode) (core : SmoothRadialCore 1) :
    annularNuFiniteSmoothCore lower (Finsupp.single mode core) =
      annularNuModeCoordinates lower mode (weightedRadialCoreInto 1 lower core) := by
  rw [annularNuFiniteSmoothCore, Finsupp.lsum_single]
  rfl

theorem annularNuFiniteSmoothCore_mem (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : HighAnnularMode →₀ SmoothRadialCore 1) :
    annularNuFiniteSmoothCore lower core ∈ annularFluxWeakGraph lower positive := by
  rw [annularNuFiniteSmoothCore, Finsupp.lsum_apply, Finsupp.sum]
  exact (annularFluxWeakGraph lower positive).sum_mem
    (fun mode _ => annularNuModeCoordinates_mem lower positive bounded mode (weightedRadialCoreInto 1 lower (core mode)))

theorem annularNuModeCoordinates_recover (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularNuModeCoordinates lower mode (annularFluxRadialGraph lower positive bounded field mode) =
      (lp.single 2 mode (field.val.1 mode), lp.single 2 mode (field.val.2 mode)) := by
  apply Prod.ext
  · change (lp.single 2 mode (weightedRadialCoordinate 1 lower 0 (annularFluxRadialGraph lower positive bounded field mode)) : AnnularBulk lower) = _
    rw [annularFluxRadialGraph_value]
  · change (lp.single 2 mode ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ •
      weightedRadialCoordinate 1 lower 1 (annularFluxRadialGraph lower positive bounded field mode)) : AnnularBulk lower) = _
    rw [annularFluxRadialGraph_slope, smul_smul,
      inv_mul_cancel₀ (Grad.AnnularFluxTrace.annularFrequency_pos mode).ne', one_smul]

/-- Density in the independently specified actual weak graph. -/
theorem annularNuFiniteSmoothCore_closure (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    (LinearMap.range (annularNuFiniteSmoothCore lower)).topologicalClosure =
      (annularFluxWeakGraph lower positive).restrictScalars ℝ := by
  let subspace := (LinearMap.range (annularNuFiniteSmoothCore lower)).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨core, rfl⟩
      exact annularNuFiniteSmoothCore_mem lower positive bounded core
    · exact annularFluxWeakGraph_closed lower positive
  · intro value member
    let field : annularFluxWeakGraph lower positive := ⟨value, member⟩
    have singleMember (mode : HighAnnularMode) (radial : WeightedRadialH1 1 lower) :
        annularNuModeCoordinates lower mode radial ∈ subspace := by
      apply isClosed_property (weightedRadialCoreInto_denseRange 1 lower)
        ((LinearMap.range (annularNuFiniteSmoothCore lower)).isClosed_topologicalClosure.preimage
          (annularNuModeCoordinates lower mode).continuous) _ radial
      intro core
      apply Submodule.le_topologicalClosure
      exact ⟨Finsupp.single mode core, annularNuFiniteSmoothCore_single lower mode core⟩
    have convergence : HasSum (fun mode : HighAnnularMode =>
        annularNuModeCoordinates lower mode (annularFluxRadialGraph lower positive bounded field mode)) value := by
      have original := (lp.hasSum_single (by norm_num) field.val.1).prodMk
        (lp.hasSum_single (by norm_num) field.val.2)
      exact original.congr_fun (fun mode => annularNuModeCoordinates_recover lower positive bounded field mode)
    exact (LinearMap.range (annularNuFiniteSmoothCore lower)).isClosed_topologicalClosure.mem_of_tendsto
      convergence (Filter.Eventually.of_forall (fun support =>
        subspace.sum_mem (fun mode _ => singleMember mode (annularFluxRadialGraph lower positive bounded field mode))))

end Grad.AnnularOmegaGraph
