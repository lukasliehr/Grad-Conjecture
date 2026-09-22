import AEE15UniformSmoothCoreCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem lowSmoothGraph_denseRange (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    DenseRange (lowSmoothGraph lower length positive bounded) := by
  let source := LinearMap.range (lowFiniteSmoothCore lower length positive bounded)
  have inclusion : (source : Set (LowEnergyAmbient lower)) ⊆ lowEnergyGraph lower length positive := by
    rintro _ ⟨core, rfl⟩
    exact lowFiniteSmoothCore_mem lower length positive bounded core
  have inclusionDense : DenseRange (Set.inclusion inclusion) := by
    apply (denseRange_inclusion_iff _).mpr
    intro value member
    change value ∈ (LinearMap.range (lowFiniteSmoothCore lower length positive bounded)).topologicalClosure
    rw [lowFiniteSmoothCore_closure]
    exact member
  apply inclusionDense.mono
  rintro _ ⟨point, rfl⟩
  rcases point.property with ⟨core, equality⟩
  exact ⟨core, Subtype.ext equality⟩

/-- Uniform coercivity on the independently defined complete original Y.
Only proven smooth density, actual data-map continuity, and the original
reference estimate are used in passage to the completed graph. -/
theorem lowReferenceDataOperator_coercivity (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    ‖field‖ ^ 2 ≤ lowReferenceGraphConstant parameters length *
      ‖lowReferenceDataOperator parameters length lower lengthPositive positive bounded field‖ ^ 2 := by
  apply isClosed_property (lowSmoothGraph_denseRange lower length positive bounded)
    (isClosed_le (by fun_prop) (by fun_prop)) _ field
  intro core
  exact lowSmoothGraph_coercivity parameters length lower lengthPositive positive bounded core

theorem lowReferenceDataOperator_lowerBound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    ‖field‖ ≤ Real.sqrt (lowReferenceGraphConstant parameters length) *
      ‖lowReferenceDataOperator parameters length lower lengthPositive positive bounded field‖ := by
  have squared := lowReferenceDataOperator_coercivity parameters length lower lengthPositive positive bounded field
  have root := Real.sq_sqrt (lowReferenceGraphConstant_pos parameters length lengthPositive).le
  have nonnegative : 0 ≤ Real.sqrt (lowReferenceGraphConstant parameters length) *
      ‖lowReferenceDataOperator parameters length lower lengthPositive positive bounded field‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) nonnegative).mp
  rw [mul_pow, root]
  exact squared

end Grad.AnnularLowCompletion
