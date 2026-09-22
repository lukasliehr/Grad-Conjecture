import Q23SeedTransferActual

noncomputable section

set_option maxHeartbeats 1600000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Seed

/-- Literal Mathlib Fréchet derivatives of the actual completed N18 transfer
with respect to all four finite seed parameters. -/
def completedSeedTransferParameterDerivative (phase : PhaseParameters)
    (grade order : ℕ) (reference parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    AGrade phase 3 grade →L[ℂ] AGrade phase 3 grade :=
  iteratedFDeriv ℝ order (completedSeedTransferFamily phase grade reference)
    parameter directions

theorem completedSeedTransferParameterDerivative_zero (phase : PhaseParameters)
    (grade : ℕ) (reference parameter : Seed.Parameters) :
    completedSeedTransferParameterDerivative phase grade 0 reference parameter
        (fun position => position.elim0) =
      completedSeedTransferFamily phase grade reference parameter := by
  rfl

theorem completedSeedTransferParameterDerivative_zero_core (phase : PhaseParameters)
    (grade : ℕ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    completedSeedTransferParameterDerivative phase grade 0 reference parameter
        (fun position => position.elim0)
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (Grad.Constraints.Gauges.seedTransfer phase reference insideR parameter inside field)) := by
  rw [completedSeedTransferParameterDerivative_zero]
  exact completedSeedTransferFamily_core phase grade reference insideR parameter inside field

/-- Uniform bounds for every actual finite-seed derivative on an arbitrary
compact patch contained in the exact admissible seed domain. -/
theorem completedSeedTransferParameterDerivative_compact_bound
    (phase : PhaseParameters) (grade order : ℕ) (reference : Seed.Parameters)
    (compact : Set Seed.Parameters) (compactness : IsCompact compact)
    (insideCompact : compact ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ parameter ∈ compact, ∀ directions : Fin order → Seed.Parameters,
        ‖completedSeedTransferParameterDerivative phase grade order reference parameter
            directions‖ ≤ constant * ∏ position, ‖directions position‖ := by
  obtain ⟨bound, bounded⟩ := compactness.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := order)
      (completedSeedTransferFamily_contDiffOn phase grade reference)
      Seed.parameterDomain_isOpen
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).mono insideCompact)
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter inCompact directions
  have operatorBound :
      ‖iteratedFDeriv ℝ order (completedSeedTransferFamily phase grade reference)
          parameter‖ ≤ max 0 bound :=
    (bounded parameter inCompact).trans (le_max_right 0 bound)
  have evaluationBound :=
    (iteratedFDeriv ℝ order (completedSeedTransferFamily phase grade reference)
      parameter).le_opNorm directions
  exact evaluationBound.trans (mul_le_mul_of_nonneg_right operatorBound
    (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end Grad.NonlinearQuotientBounds
