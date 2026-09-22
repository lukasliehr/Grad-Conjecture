import PA4PhaseProof

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra.Consumer

open Grad.CartesianState Grad.PhaseAlgebra

/-- Immediate exact consumer of the subadditive goal against the ACCEPTED
Cartesian phase: subadditivity at every actual disk point. -/
theorem cartesian_phase_subadditive (parameters : PhaseParameters)
    (point : Grad.ClosedJets.SpatialPlane) (normLe : ‖point‖ ≤ 1) (n m : ℤ) :
    cartesianPhase parameters (n + m) point ≤
      cartesianPhase parameters n point + cartesianPhase parameters m point := by
  have subadd := actualPhaseSubadditive parameters ‖point‖ (norm_nonneg point) normLe n m
  rw [← radialPhase_eq_cartesianPhase parameters ‖point‖ (n + m) point rfl,
    ← radialPhase_eq_cartesianPhase parameters ‖point‖ n point rfl,
    ← radialPhase_eq_cartesianPhase parameters ‖point‖ m point rfl] at subadd
  exact subadd

/-- Immediate exact consumer of the equivalence goal against the ACCEPTED
Cartesian weight: the two-sided replacement-weight comparison at every
actual disk point, with the literal constant `exp (sigma0 + gamma)`. -/
theorem cartesian_weight_equivalent (parameters : PhaseParameters)
    (point : Grad.ClosedJets.SpatialPlane) (normLe : ‖point‖ ≤ 1) (cell : ℤ) :
    phaseWeight parameters ‖point‖ cell ≤
        Real.exp (cartesianPhase parameters cell point) ∧
      Real.exp (cartesianPhase parameters cell point) ≤
        Real.exp (parameters.sigma0 + parameters.gamma) *
          phaseWeight parameters ‖point‖ cell := by
  obtain ⟨⟨lowerBound, upperBound⟩, -⟩ :=
    actualPhaseEquivalent parameters ‖point‖ (norm_nonneg point) normLe cell
  rw [← radialPhase_eq_cartesianPhase parameters ‖point‖ cell point rfl]
    at lowerBound upperBound
  exact ⟨lowerBound, upperBound⟩

/-- The B3 exponential ratio at every actual disk point. -/
theorem cartesian_phase_ratio (parameters : PhaseParameters)
    (point : Grad.ClosedJets.SpatialPlane) (normLe : ‖point‖ ≤ 1) (n m : ℤ) :
    Real.exp (cartesianPhase parameters n point - cartesianPhase parameters m point) ≤
      Real.exp (cartesianPhase parameters (n - m) point) := by
  have ratio := exp_radialPhase_ratio parameters ‖point‖ (norm_nonneg point) normLe n m
  rw [← radialPhase_eq_cartesianPhase parameters ‖point‖ n point rfl,
    ← radialPhase_eq_cartesianPhase parameters ‖point‖ m point rfl,
    ← radialPhase_eq_cartesianPhase parameters ‖point‖ (n - m) point rfl] at ratio
  exact ratio

end Grad.PhaseAlgebra.Consumer
