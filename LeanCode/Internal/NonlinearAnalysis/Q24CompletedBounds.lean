import Q24FixedSeedDerivatives
import Q24JointGrades
import Q24DensityBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.Constraints

/-- The exact one-high expression on the original completed joint norms. -/
def completedOneHigh (parameters : PhaseParameters) (grade order : ℕ)
    (base : JointAmbient parameters (grade + 6))
    (directions : Fin order → JointAmbient parameters (grade + 6)) : ℝ :=
  (1 + ‖base‖) * ∏ position, ‖jointLowering parameters (show 4 ≤ grade + 6 by omega) (directions position)‖ +
    ∑ position, ‖directions position‖ *
      ∏ other ∈ Finset.univ.erase position,
        ‖jointLowering parameters (show 4 ≤ grade + 6 by omega) (directions other)‖

theorem completedOneHigh_core (parameters : PhaseParameters) (grade order : ℕ)
    (base : JointState parameters) (directions : Fin order → JointState parameters) :
    completedOneHigh parameters grade order (jointCoreEmbed parameters (grade + 6) base)
      (fun position => jointCoreEmbed parameters (grade + 6) (directions position)) =
    (1 + jointNorm (grade + 6) base) * ∏ position, jointNorm 4 (directions position) +
      ∑ position, jointNorm (grade + 6) (directions position) *
        ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) := by
  simp only [completedOneHigh, jointCoreEmbed_norm, jointLowering_core]

theorem completedOneHigh_continuous (parameters : PhaseParameters) (grade order : ℕ) :
    Continuous (fun pair : JointAmbient parameters (grade + 6) ×
        (Fin order → JointAmbient parameters (grade + 6)) =>
      completedOneHigh parameters grade order pair.1 pair.2) := by
  unfold completedOneHigh
  fun_prop

/-- Full completed Q22 estimate. The constant is uniform in unrestricted
high state norms; only the original low grade-four ball is bounded. -/
theorem completedFixedSlice_derivative_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointAmbient parameters (grade + 6))
        (directions : Fin order → JointAmbient parameters (grade + 6)),
        base ∈ jointDomain parameters (grade + 6) →
        ‖jointLowering parameters (show 4 ≤ grade + 6 by omega) base‖ ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedFixedSlice parameters cellLength reference insideR seed insideS grade) base directions‖ ≤
          constant * completedOneHigh parameters grade order base directions := by
  obtain ⟨constant, nonneg, bounded⟩ := completedFixedSlice_derivative_core_bound parameters cellLength
    reference insideR seed insideS grade order (bound + 1)
  refine ⟨constant, nonneg, fun base directions inside lowBound => ?_⟩
  apply derivative_bound_of_dense_core
    (jointCoreEmbed parameters (grade + 6)) (jointCoreEmbed_denseRange parameters (grade + 6))
    (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
    (jointDomain parameters (grade + 6))
    (jointDomain_isOpen parameters (grade + 6))
    (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade)
    order (fun state => ‖jointLowering parameters (show 4 ≤ grade + 6 by omega) state‖)
    (jointLowering parameters (show 4 ≤ grade + 6 by omega)).continuous.norm (bound + 1)
    (fun pair => constant * completedOneHigh parameters grade order pair.1 pair.2)
    (continuous_const.mul (completedOneHigh_continuous parameters grade order))
  · intro core tuple coreInside strict
    rw [completedOneHigh_core]
    rw [jointLowering_core, jointCoreEmbed_norm] at strict
    exact bounded core tuple ((jointDomain_core_iff parameters (grade + 6) core).1 coreInside) strict.le
  · exact inside
  · exact lowBound.trans_lt (lt_add_one bound)

end Grad.Q24Realization
