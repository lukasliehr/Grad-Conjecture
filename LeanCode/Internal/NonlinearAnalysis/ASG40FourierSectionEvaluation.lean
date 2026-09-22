import ASG39CompletedFourierSection

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularFourierSection_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    annularFourierSection parameters dimension lower positive bounded angular cell field radius mode =
      weightedRadialSection dimension lower positive bounded (field mode) radius := by
  let first : AnnularSourceH1 parameters dimension lower angular cell →L[ℝ] ComplexEuclidean dimension :=
    (lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).comp
      ((ContinuousMap.evalCLM ℝ radius).comp
        (annularFourierSection parameters dimension lower positive bounded angular cell))
  let second : AnnularSourceH1 parameters dimension lower angular cell →L[ℝ] ComplexEuclidean dimension :=
    (ContinuousMap.evalCLM ℝ radius).comp ((weightedRadialSection dimension lower positive bounded).comp
      (lp.evalCLM ℝ (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 mode))
  change first field = second field
  apply isClosed_property (finiteSourceCore_denseRange parameters dimension lower angular cell)
    (isClosed_eq first.continuous second.continuous) _ field
  intro core
  change annularFourierSection parameters dimension lower positive bounded angular cell
      (finiteSourceCore parameters dimension lower angular cell core) radius mode =
    weightedRadialSection dimension lower positive bounded
      (finiteSourceCore parameters dimension lower angular cell core mode) radius
  rw [annularFourierSection_core, finiteFourierSection_apply, finiteSourceCore_apply, weightedRadialSection_core]
  rfl

/-- The endpoint trace is evaluation of the full l2-valued continuous
representative, at either original one-sided endpoint. -/
theorem annularFourierSection_endpoint (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (endpoint : Fin 2) :
    annularFourierSection parameters dimension lower positive bounded angular cell field
      ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ =
    annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field := by
  apply Subtype.ext
  funext mode
  rw [annularFourierSection_apply, weightedRadialSection_endpoint]
  rfl

theorem annularFourierSection_physical_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    annularFourierSection parameters dimension lower positive bounded angular cell
      (physicalSourceCore parameters dimension lower angular cell core) radius mode =
    annularConjugatingWeight parameters angular cell mode radius.val • (core mode).val.val.1 radius.val := by
  rw [annularFourierSection_apply, physicalSourceCore_apply, weightedRadialSection_core]
  rfl

end Grad.AnnularSourceGraph
