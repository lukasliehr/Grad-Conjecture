import AJI1ClosedScaleRadialBootstrap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology ENNReal
namespace Grad.AnnularSmoothCore

variable {Index X E : Type*} [DecidableEq Index] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def hilbertSectionValue (sections : Index → X → E) (point : X) : lp (fun _ : Index => E) 2 :=
  ∑' index, lp.single 2 index (sections index point)

omit [TopologicalSpace X] [NormedSpace ℂ E] in
theorem hilbertSection_summable (sections : Index → X → E)
    (majorant : Index → ℝ) (summable : Summable majorant)
    (bound : ∀ index point, ‖sections index point‖ ≤ majorant index) (point : X) :
    Summable (fun index => (lp.single 2 index (sections index point) : lp (fun _ : Index => E) 2)) := by
  apply Summable.of_norm_bounded summable
  intro index
  rw [lp.norm_single (by norm_num)]
  exact bound index point

/-- An all-grade H1 bound will supply the summable majorant. The result is
one continuous Hilbert-valued representative, with exactly the given modes. -/
theorem hilbertSection_continuous (sections : Index → X → E)
    (continuous : ∀ index, Continuous (sections index))
    (majorant : Index → ℝ) (summable : Summable majorant)
    (bound : ∀ index point, ‖sections index point‖ ≤ majorant index) :
    Continuous (hilbertSectionValue sections) := by
  exact continuous_tsum
    (fun index => (lp.singleContinuousLinearMap ℂ (fun _ : Index => E) 2 index).continuous.comp (continuous index))
    summable (fun index point => by rw [lp.norm_single (by norm_num)]; exact bound index point)

omit [TopologicalSpace X] in
theorem hilbertSection_coefficient (sections : Index → X → E)
    (majorant : Index → ℝ) (summable : Summable majorant)
    (bound : ∀ index point, ‖sections index point‖ ≤ majorant index) (point : X) (index : Index) :
    hilbertSectionValue sections point index = sections index point := by
  classical
  have sum := (lp.evalCLM ℂ (fun _ : Index => E) 2 index).hasSum
    (hilbertSection_summable sections majorant summable bound point).hasSum
  change HasSum (fun other => (lp.single 2 other (sections other point) : lp (fun _ : Index => E) 2) index)
    (hilbertSectionValue sections point index) at sum
  rw [← sum.tsum_eq, tsum_eq_single index]
  · simp
  · intro other nonzero
    simp [lp.single_apply, nonzero]

end Grad.AnnularSmoothCore
