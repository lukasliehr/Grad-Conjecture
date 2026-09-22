import AEC7OriginalIntegratedReferenceEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

def lowForcingComponent (lower : ℝ) (ordered : lower ≤ 1)
    (forcing : C(Icc lower 1, LowReferencePair)) (entry : Fin 2) (radius : ℝ) : ℂ :=
  curveExtension lower 1 ordered forcing radius entry

theorem lowForcingComponent_continuous (lower : ℝ) (ordered : lower ≤ 1)
    (forcing : C(Icc lower 1, LowReferencePair)) (entry : Fin 2) :
    Continuous (lowForcingComponent lower ordered forcing entry) :=
  (continuous_apply entry).comp (curveExtension_continuous lower 1 ordered forcing)

theorem lowForcingComponent_of_mem (lower : ℝ) (ordered : lower ≤ 1)
    (forcing : C(Icc lower 1, LowReferencePair)) (entry : Fin 2) (radius : ℝ)
    (member : radius ∈ Icc lower 1) :
    lowForcingComponent lower ordered forcing entry radius = forcing ⟨radius, member⟩ entry := by
  rw [lowForcingComponent, curveExtension_of_mem lower 1 ordered forcing radius member]

/-- Constructed actual reference solutions, together with their original
incoming-to-bulk/outer-energy estimate. This is not a conditional estimate
for an assumed ODE solution. All original low signs and n=0 are included. -/
theorem originalLowReferenceEnergySolution_exists (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode)
    (positive : 0 < lower) (ordered : lower ≤ 1)
    (forcing : C(Icc lower 1, LowReferencePair)) (initial : LowReferencePair) :
    ∃ first second : ℝ → ℂ, first lower = initial 0 ∧ second lower = initial 1 ∧
      (∀ point : Icc lower 1,
        HasDerivAt first (lowReferenceFirst parameters length point.val mode (first point.val) (second point.val) +
          lowMu length point.val mode.val.2 • forcing point 0) point.val ∧
        HasDerivAt second (lowReferenceSecond parameters length point.val mode (first point.val) (second point.val) +
          lowMu length point.val mode.val.2 • forcing point 1) point.val) ∧
      lowPairEnergy length 1 mode (first 1) (second 1) +
        (lowEta length parameters.gamma / 2) *
          (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) * (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2)) ≤
      lowPairEnergy length lower mode (initial 0) (initial 1) +
        (4 / lowEta length parameters.gamma) *
          (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
            (‖lowForcingComponent lower ordered forcing 0 radius‖ ^ 2 +
              ‖lowForcingComponent lower ordered forcing 1 radius‖ ^ 2)) := by
  obtain ⟨first, second, firstInitial, secondInitial, derivatives⟩ :=
    lowReferenceModeCauchy_exists parameters length lower 1 mode positive ordered forcing initial
  refine ⟨first, second, firstInitial, secondInitial, derivatives, ?_⟩
  have integrated := lowPairEnergy_integrated_bound parameters length lower 1 lengthPositive mode positive ordered
    first second (lowForcingComponent lower ordered forcing 0) (lowForcingComponent lower ordered forcing 1)
    (fun _ _ => (lowForcingComponent_continuous lower ordered forcing 0).continuousAt)
    (fun _ _ => (lowForcingComponent_continuous lower ordered forcing 1).continuousAt)
    (fun radius member => by
      rw [lowForcingComponent_of_mem lower ordered forcing 0 radius member]
      exact (derivatives ⟨radius, member⟩).1)
    (fun radius member => by
      rw [lowForcingComponent_of_mem lower ordered forcing 1 radius member]
      exact (derivatives ⟨radius, member⟩).2)
  rw [firstInitial, secondInitial] at integrated
  exact integrated

end Grad.AnnularLowVolterra
