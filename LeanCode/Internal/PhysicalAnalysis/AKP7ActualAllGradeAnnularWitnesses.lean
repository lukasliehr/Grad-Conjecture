import AKP6ActualCofinalInsertedWitnesses

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.ActualAnnularExhaustion
open Grad.AnnularExhaustionEstimate
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





/-- A single radius-independent constant controls every actual annular solve
in a sequence. Each witness belongs to the SAME solution at that radius and
the SAME inserted grade; no separate higher-grade inverse is selected. -/
theorem actualAnnularSolves_allGradeWitnesses
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ constant : ℕ → ℝ, (∀ grade, 0 ≤ constant grade) ∧
      ∀ (grade : ℕ) (context : ℕ → CoupledCoordinateContext parameters length compact)
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
            ‖retained index‖ ≤ constant grade * (sourceBound + stateBound * baseBound) := by
  let certificate := fun grade => originalExhaustionSequence_uniform parameters length compact lengthPositive grade
  exact ⟨fun grade => (certificate grade).choose, fun grade => (certificate grade).choose_spec.1,
    fun grade => (certificate grade).choose_spec.2⟩

end Grad.ActualAnnularExhaustion
