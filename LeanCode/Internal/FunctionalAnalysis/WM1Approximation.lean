import WM1Graph
import MP1Bump

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.SpatialTranslation
open scoped Topology ContDiff

namespace Grad.Mollifier.WeakJets

universe valueUniverse

theorem scaledAverage_tendsto (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (field : DomainL2 Value Set.univ) :
    Filter.Tendsto (fun epsilon : ℝ => average Value (Pointwise.scaledEta epsilon) field)
      (𝓝[>] 0) (𝓝 field) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positiveTolerance
  obtain ⟨radius, positiveRadius, bound⟩ := average_smallSupport Value field tolerance positiveTolerance
  filter_upwards [Ioo_mem_nhdsGT positiveRadius] with epsilon bounds
  rw [dist_eq_norm]
  apply bound (Pointwise.scaledEta epsilon) (Pointwise.scaledEta_integrable epsilon bounds.1)
    (Filter.Eventually.of_forall (Pointwise.scaledEta_nonneg epsilon bounds.1))
    (Pointwise.scaledEta_integral epsilon bounds.1)
  apply Filter.Eventually.of_forall
  intro offset nonzero
  have support : offset ∈ Metric.ball (0 : Spatial) epsilon := by
    rw [← Pointwise.scaledEta_support epsilon bounds.1]
    exact nonzero
  exact (show ‖offset‖ < epsilon by simpa only [Metric.mem_ball, dist_zero_right] using support).trans bounds.2

theorem approximationGoal : ApproximationGoal := by
  intro dimension order exponent jet
  have coordinates := tendsto_pi_nhds.mpr
    (fun index : JetIndex order => scaledAverage_tendsto (CellValues dimension) (jet.val index))
  have continuity : Continuous (graphOfCoordinates (Index := JetIndex order)
      (Fiber := fun _ => FieldL2 dimension Set.univ)) :=
    PiLp.continuous_toLp 2 (fun _ : JetIndex order => FieldL2 dimension Set.univ)
  exact continuity.continuousAt.tendsto.comp coordinates

def jetRegularizer (dimension order : ℕ) (exponent : JetIndex order → ℕ) (epsilon : ℝ) :
    WJet dimension order Set.univ exponent →L[ℂ] WJet dimension order Set.univ exponent :=
  if positive : 0 < epsilon then
    jetAveraging dimension order exponent (Pointwise.scaledEta epsilon)
      (Pointwise.scaledEta_integrable epsilon positive)
  else 0

theorem jetRegularizer_specification (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    LiftSpecification dimension order exponent (Pointwise.scaledEta epsilon)
        (jetRegularizer dimension order exponent epsilon) ∧
      ‖jetRegularizer dimension order exponent epsilon‖ ≤ 1 := by
  rw [jetRegularizer, dif_pos positive]
  refine ⟨jetAveraging_specification dimension order exponent _ _, ?_⟩
  simpa only [Pointwise.scaledEta_kernelL1 epsilon positive] using
    jetAveraging_norm_le dimension order exponent (Pointwise.scaledEta epsilon)
      (Pointwise.scaledEta_integrable epsilon positive)

theorem jetRegularizer_tendsto (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order Set.univ exponent) :
    Filter.Tendsto (fun epsilon : ℝ => jetRegularizer dimension order exponent epsilon jet)
      (𝓝[>] 0) (𝓝 jet) := by
  apply tendsto_subtype_rng.mpr
  apply (approximationGoal dimension order exponent jet).congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon positive
  exact ((jetRegularizer_specification dimension order exponent epsilon positive).1.1 jet).symm

theorem regularizationGoal : RegularizationGoal := by
  intro dimension order exponent
  exact ⟨jetRegularizer dimension order exponent,
    jetRegularizer_specification dimension order exponent, jetRegularizer_tendsto dimension order exponent⟩

theorem zeroGoal : ZeroGoal := by
  constructor
  · intro dimension exponent epsilon positive jet
    exact graphGoal dimension 0 exponent (Pointwise.scaledEta epsilon)
      (Pointwise.scaledEta_integrable epsilon positive) jet
  · intro order exponent epsilon _ jet
    apply PiLp.ext
    intro index
    apply Lp.ext
    apply Filter.Eventually.of_forall
    intro point
    apply lp.ext
    funext cell
    apply PiLp.ext
    intro physical
    exact Fin.elim0 physical

end Grad.Mollifier.WeakJets
