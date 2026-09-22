import AKDN24ActualNativePhaseOneOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.SourceCollarCoefficients Grad.AnnularReconstruction
open Grad.AnnularSmoothCore

/-- The literal j/c/rV flux assembly only introduces fixed kinematic
constants and lower row Euler ranks, preserving all coefficient allocations. -/
theorem balancedFluxCurve_EulerNormRows (parameters : PhaseParameters) (length : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (lower : ℝ) (_positive : 0 < lower) (_bounded : lower < 1)
      (first second third : ℝ → CellL2 1) (rank : ℕ),
    ContDiffOn ℝ rank first (Icc lower 1) →
    ContDiffOn ℝ rank second (Icc lower 1) →
    ContDiffOn ℝ rank third (Icc lower 1) →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => balancedFluxOutput parameters length point (first point,(second point,third point))) radius.val‖ ≤
      constant*eulerAllocationSum (fun _ order =>
        ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order first radius.val‖+
        ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order second radius.val‖+
        ‖vectorEulerWithinIteratedDerivative (Icc lower 1) order third radius.val‖) (eulerLeibnizTerms rank) := by
  obtain ⟨constant,constant0,bound⟩ := balancedFluxCurve_EulerBound parameters length
  refine ⟨constant,constant0,?_⟩
  intro lower positive bounded first second third rank firstSmooth secondSmooth thirdSmooth radius inside
  have actual := bound lower positive bounded (fun point => (first point,(second point,third point))) rank
    (firstSmooth.prodMk (secondSmooth.prodMk thirdSmooth)) radius inside
  apply actual.trans
  apply mul_le_mul_of_nonneg_left _ constant0
  apply eulerAllocationSum_mono
  intro term member
  have allocated := eulerLeibnizTerms_rank rank term member
  have one : ContDiffOn ℝ term.2 first (Icc lower 1) := firstSmooth.of_le (by exact_mod_cast (show term.2 ≤ rank by omega))
  have two : ContDiffOn ℝ term.2 second (Icc lower 1) := secondSmooth.of_le (by exact_mod_cast (show term.2 ≤ rank by omega))
  have three : ContDiffOn ℝ term.2 third (Icc lower 1) := thirdSmooth.of_le (by exact_mod_cast (show term.2 ≤ rank by omega))
  rw [vectorEulerWithin_pair (Icc lower 1) (uniqueDiffOn_Icc bounded) first
    (fun point => (second point,third point)) term.2 one (two.prodMk three) radius.val inside,
    vectorEulerWithin_pair (Icc lower 1) (uniqueDiffOn_Icc bounded) second third term.2 two three radius.val inside,
    Prod.norm_def,Prod.norm_def]
  have first0 := norm_nonneg (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 first radius.val)
  have second0 := norm_nonneg (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 second radius.val)
  have third0 := norm_nonneg (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 third radius.val)
  apply max_le
  · linarith
  · apply max_le <;> linarith

end Grad.OriginalCartesianTameEstimate
