import AKCY15ConstructedOriginalNewtonConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit

/-- A bound on differences transfers continuity without completing or
changing the original domain of either family. -/
theorem continuousOn_of_norm_control {Parameter Input Output : Type*}
    [TopologicalSpace Parameter] [NormedAddCommGroup Input] [NormedAddCommGroup Output]
    (domain : Set Parameter) (input : Parameter → Input) (output : Parameter → Output)
    (constant : ℝ) (continuous : ContinuousOn input domain)
    (bounded : ∀ point ∈ domain, ∀ base ∈ domain,
      ‖output point-output base‖ ≤ constant*‖input point-input base‖) :
    ContinuousOn output domain := by
  intro base member
  rw [ContinuousWithinAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (by filter_upwards [self_mem_nhdsWithin] with point pointMember; exact bounded point pointMember base member)
  have difference := (continuous base member).tendsto.sub (tendsto_const_nhds (x := input base))
  simpa only [sub_self,norm_zero,mul_zero] using tendsto_const_nhds.mul difference.norm

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain)

/-- Fixed-time actual full constrained smoothing preserves continuity in
its SAME original completed grade. It is the smoothing used by CY stages. -/
theorem originalStateSmoothing_continuousOn {Parameter : Type*} [TopologicalSpace Parameter]
    (domain : Set Parameter) (branch : Parameter → stateSmoothRange parameters reference inside)
    (grade : ℕ) (large : 3 ≤ grade) (time : ℝ) (positive : 0 < time)
    (continuous : ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside grade large
      (branch point)) domain) :
    ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside grade large
      (originalStateSmoothing parameters reference inside time (branch point))) domain := by
  apply continuousOn_of_norm_control domain
    (fun point => stateSmoothEmbedding parameters reference inside grade large (branch point)) _
    (originalSmoothingGain parameters reference inside grade grade) continuous
  intro point pointMember base baseMember
  rw [← map_sub,← map_sub]
  rw [← map_sub (originalStateSmoothing parameters reference inside time)]
  have estimate := originalStateSmoothing_norm_le parameters reference inside time positive grade grade
    (le_refl grade) large (branch point-branch base)
  rw [stateSmoothEmbedding_norm,stateSmoothEmbedding_norm]
  simpa only [Nat.sub_self,pow_zero,mul_one] using estimate

end Grad.NashMoser.OriginalIteration
