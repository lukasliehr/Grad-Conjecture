import AKL4ExactOriginalExhaustionSolve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularExhaustionEstimate
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.AnnularCoupledInverse
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule





private theorem uniformTameBound {value weighted base budget constant topWeighted topBase topBudget : ℝ}
    (estimate : value ≤ constant * (weighted + budget * base))
    (nonnegative : 0 ≤ constant) (baseNonnegative : 0 ≤ base)
    (budgetNonnegative : 0 ≤ topBudget)
    (weightedBound : weighted ≤ topWeighted) (baseBound : base ≤ topBase)
    (budgetBound : budget ≤ topBudget) :
    value ≤ constant * (topWeighted + topBudget * topBase) :=
  estimate.trans (mul_le_mul_of_nonneg_left
    (add_le_add weightedBound
      ((mul_le_mul_of_nonneg_right budgetBound baseNonnegative).trans
        (mul_le_mul_of_nonneg_left baseBound budgetNonnegative))) nonnegative)

variable (parameters : PhaseParameters) (length compact : ℝ)

/-- A single radius-independent constant controls every actual annular solve
in a sequence. Each witness belongs to the SAME solution at that radius and
the SAME inserted grade; no separate higher-grade inverse is selected. -/
theorem originalExhaustionSequence_uniform (lengthPositive : 0 < length) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (context : ℕ → CoupledCoordinateContext parameters length compact)
        (data : ∀ index : ℕ, OriginalStrongCarrier parameters (context index).lower 0 0)
        (weighted : ∀ index : ℕ, StrongDataCarrier parameters (context index).lower
          (context index).positive ((context index).lowerHalf.trans (by norm_num)) 0 0)
        (_inserted : ∀ index : ℕ, ExhaustionDataInserted parameters length compact
          (context index) grade (data index) (weighted index))
        (sourceBound baseBound stateBound : ℝ)
        (_stateNonnegative : 0 ≤ stateBound)
        (_weightedBound : ∀ index : ℕ, ‖weighted index‖ ≤ sourceBound)
        (_baseBound : ∀ index : ℕ, exhaustionDatumNorm parameters length compact
          (context index) (data index) ≤ baseBound)
        (_stateBound : ∀ index : ℕ, (context index).budget grade ≤ stateBound),
        ∃ retained : ∀ index : ℕ, CoupledSpace (context index).lower length
            (context index).positive (context index).lengthPositive,
          ∀ index : ℕ,
            ExhaustionRetainedInserted parameters length compact (context index) grade
              (data index) (retained index) ∧
            ‖retained index‖ ≤ constant * (sourceBound + stateBound * baseBound) := by
  let certificate := originalExhaustionSolve_uniform parameters length compact lengthPositive grade
  refine ⟨certificate.choose, certificate.choose_spec.1, ?_⟩
  intro context data weighted inserted sourceBound baseBound stateBound stateNonnegative weightedBound baseEstimate stateEstimate
  let selected := fun index => certificate.choose_spec.2 (context index) (data index) (weighted index) (inserted index)
  refine ⟨fun index => (selected index).choose, ?_⟩
  intro index
  refine ⟨(selected index).choose_spec.1, ?_⟩
  exact uniformTameBound (selected index).choose_spec.2 certificate.choose_spec.1
    (norm_nonneg _) stateNonnegative (weightedBound index) (baseEstimate index) (stateEstimate index)

end Grad.AnnularExhaustionEstimate
