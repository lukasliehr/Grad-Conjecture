import AEC11LiteralLowGraphEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

/-- Actual full-interval reference solutions with a uniform estimate in the
literal original low Y norm. The incoming term is exactly rho(ell)/mu(ell)
times the squared incoming pair, and the source is the original F. -/
theorem originalLowReferenceYSolution_exists (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode)
    (positive : 0 < lower) (ordered : lower ≤ 1)
    (forcing : C(Icc lower 1, LowReferencePair)) (initial : LowReferencePair) :
    ∃ first second : ℝ → ℂ, first lower = initial 0 ∧ second lower = initial 1 ∧
      (∀ point : Icc lower 1,
        HasDerivAt first (lowReferenceFirst parameters length point.val mode (first point.val) (second point.val) +
          lowMu length point.val mode.val.2 • forcing point 0) point.val ∧
        HasDerivAt second (lowReferenceSecond parameters length point.val mode (first point.val) (second point.val) +
          lowMu length point.val mode.val.2 • forcing point 1) point.val) ∧
      (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2 +
          ‖(lowMu length radius mode.val.2)⁻¹ • deriv first radius‖ ^ 2 +
          ‖(lowMu length radius mode.val.2)⁻¹ • deriv second radius‖ ^ 2)) ≤
      lowReferenceGraphConstant parameters length *
        (lowPairEnergy length lower mode (initial 0) (initial 1) +
          ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
            (‖lowForcingComponent lower ordered forcing 0 radius‖ ^ 2 +
              ‖lowForcingComponent lower ordered forcing 1 radius‖ ^ 2)) := by
  obtain ⟨first, second, firstInitial, secondInitial, derivatives⟩ :=
    lowReferenceModeCauchy_exists parameters length lower 1 mode positive ordered forcing initial
  refine ⟨first, second, firstInitial, secondInitial, derivatives, ?_⟩
  have estimate := lowReferenceGraph_integrated_bound parameters length lower lengthPositive mode positive ordered
    first second (lowForcingComponent lower ordered forcing 0) (lowForcingComponent lower ordered forcing 1)
    (fun _ _ => (lowForcingComponent_continuous lower ordered forcing 0).continuousAt)
    (fun _ _ => (lowForcingComponent_continuous lower ordered forcing 1).continuousAt)
    (fun radius member => by
      rw [lowForcingComponent_of_mem lower ordered forcing 0 radius member]
      exact (derivatives ⟨radius, member⟩).1)
    (fun radius member => by
      rw [lowForcingComponent_of_mem lower ordered forcing 1 radius member]
      exact (derivatives ⟨radius, member⟩).2)
  rw [firstInitial, secondInitial] at estimate
  exact estimate

end Grad.AnnularLowVolterra
