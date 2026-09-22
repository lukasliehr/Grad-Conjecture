import AJF9SameCoupledInsertedGraphGrade
import AJB26GenuineLowWeightedGraphClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open Filter
open scoped Topology
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCoupledInverse Grad.AnnularLowOrbit

/-- The exact same coupled solution admits the literal BF grade after a
uniformly bounded finite-data approximation. All three actual weak graphs
are recovered at once, and the bound remains independent of the inner radius. -/
theorem coupled_insertedGrade_of_bounded_approximation {κ : Type*} (source : Filter κ) [NeBot source]
    (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) (grade : ℕ)
    (approximation weightedApproximation : κ → CoupledSpace lower length positive lengthPositive)
    (field : CoupledSpace lower length positive lengthPositive)
    (converges : Tendsto approximation source (𝓝 field))
    (actual : ∀ stage, CoupledInsertedGrade lower length positive lengthPositive grade (approximation stage) (weightedApproximation stage))
    (bound : ℝ) (nonnegative : 0 ≤ bound) (bounded : ∀ stage, ‖weightedApproximation stage‖ ≤ bound) :
    ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted ∧ ‖weighted‖ ≤ 5 * bound := by
  obtain ⟨energyWeighted, energyActual, energyBound⟩ := energy_weighted_of_bounded_approximation source
    lower length positive (fun stage => (approximation stage).ofLp.1.ofLp.1)
    (fun stage => (weightedApproximation stage).ofLp.1.ofLp.1) field.ofLp.1.ofLp.1
    (fun index => ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ))
    (((coupledEnergy lower length positive lengthPositive).continuous.tendsto field).comp converges)
    (fun stage => (actual stage).1) bound nonnegative
    (fun stage => (coupledEnergy_bound lower length positive lengthPositive (weightedApproximation stage)).trans (bounded stage))
  obtain ⟨fluxWeighted, fluxActual, fluxBound⟩ := flux_weighted_of_bounded_approximation source
    lower length positive lengthPositive (fun stage => (approximation stage).ofLp.1.ofLp.2)
    (fun stage => (weightedApproximation stage).ofLp.1.ofLp.2) field.ofLp.1.ofLp.2
    (fun index => ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ))
    (((coupledFlux lower length positive lengthPositive).continuous.tendsto field).comp converges)
    (fun stage => (actual stage).2.1) bound nonnegative
    (fun stage => (coupledFlux_bound lower length positive lengthPositive (weightedApproximation stage)).trans (bounded stage))
  obtain ⟨lowWeighted, lowActual, lowBound⟩ := lowGraph_weighted_of_bounded_approximation source
    lower length positive (fun stage => (approximation stage).ofLp.2)
    (fun stage => (weightedApproximation stage).ofLp.2) field.ofLp.2
    (fun index => ((lowInsertedFrequency index ^ grade : ℝ) : ℂ))
    (((coupledLow lower length positive lengthPositive).continuous.tendsto field).comp converges)
    (fun stage => (actual stage).2.2) bound nonnegative
    (fun stage => (coupledLow_bound lower length positive lengthPositive (weightedApproximation stage)).trans (bounded stage))
  let weighted : CoupledSpace lower length positive lengthPositive :=
    WithLp.toLp 2 (WithLp.toLp 2 (energyWeighted, fluxWeighted), lowWeighted)
  refine ⟨weighted, ⟨energyActual, fluxActual, lowActual⟩, ?_⟩
  have combined := (coupled_norm_le_three lower length positive lengthPositive weighted).trans
    (add_le_add (add_le_add energyBound fluxBound) lowBound)
  exact combined.trans_eq (by ring)

end Grad.AnnularHighGenerators
