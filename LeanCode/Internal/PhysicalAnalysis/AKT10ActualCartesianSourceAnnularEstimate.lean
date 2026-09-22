import AKT9OneOriginalSourceAndInverseBall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 250000
namespace Grad.ActualPuncturedFamily
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.AnnularCoupledInverse Grad.AnnularStrongData Grad.AnnularStrongOrbit
open Grad.AnnularExhaustionEstimate Grad.AnnularHighGenerators Grad.AnnularCrossOrbit
open Grad.ExhaustionSourceAllocation Grad.SourceCollarFullSource
open Grad.QuotientProjection Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Allocation
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






/-- The literal Cartesian source supplies every actual annular solution
with a uniform retained bound. The constant is chosen before the source,
state and collar; its only fixed high-state condition is B14≤M. -/
theorem actualCartesianSource_annularEstimate
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (grade : ℕ) (M : ℝ) (Mnonnegative : 0 ≤ M) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (context : CoupledCoordinateContext parameters length compact)
        (sourceSmall : physicalBudget parameters context.state.val.val.field context.state.val.val.rho
          context.state.val.val.epsilon 6 ≤ originalCoefficientLowRadius parameters length)
        (_stateBound : physicalBudget parameters context.state.val.val.field context.state.val.val.rho
          context.state.val.val.epsilon 14 ≤ M)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source),
        ∃ retained : CoupledSpace context.lower length context.positive context.lengthPositive,
          ExhaustionRetainedInserted parameters length compact context grade
            (actualExhaustionContextDatum parameters length compact context sourceSmall source flat 0) retained ∧
          ‖retained‖ ≤ constant * (‖quotientEta parameters (grade + 8) source‖ +
            physicalBudget parameters context.state.val.val.field context.state.val.val.rho
              context.state.val.val.epsilon (grade + 14) * ‖quotientEta parameters 8 source‖) := by
  let inverse := originalExhaustionSolve_uniform parameters length compact lengthPositive grade
  have inverseNonnegative : 0 ≤ inverse.choose := inverse.choose_spec.1
  let sourceConstant := originalSourceAllocationConstant parameters length grade
  let baseConstant := originalSourceAllocationConstant parameters length 0
  have sourcePositive : 0 ≤ sourceConstant := (originalSourceAllocationConstant_positive parameters length grade).le
  have basePositive : 0 ≤ baseConstant := (originalSourceAllocationConstant_positive parameters length 0).le
  refine ⟨inverse.choose * (sourceConstant + baseConstant * (1 + M)), by positivity, ?_⟩
  intro context sourceSmall stateBound source flat vanishing
  let weighted := originalWeightedDatum parameters context.lower length context.positive
    (context.lowerHalf.trans (by norm_num)) context.lengthPositive
    (actualExhaustionContextDatum parameters length compact context sourceSmall source flat grade)
  have inserted := actualOriginalSourceDatum_exhaustion_inserted parameters length compact
    context.state.val.val.rho context.state.val.val.epsilon context.state.val.val.field sourceSmall context grade source flat
  let solved := inverse.choose_spec.2 context
    (actualExhaustionContextDatum parameters length compact context sourceSmall source flat 0) weighted inserted
  refine ⟨solved.choose, solved.choose_spec.1, solved.choose_spec.2.trans ?_⟩
  have weightedBound := actualOriginalSourceDatum_EX_bound parameters length context.state.val.val.rho
    context.state.val.val.epsilon context.lengthPositive context.state.val.val.field sourceSmall grade
    context.lower context.positive (context.lowerHalf.trans_lt (by norm_num)) source flat vanishing
  have baseBound := actualOriginalSourceDatum_base_bound parameters length context.state.val.val.rho
    context.state.val.val.epsilon context.lengthPositive context.state.val.val.field sourceSmall M stateBound
    context.lower context.positive (context.lowerHalf.trans_lt (by norm_num)) source flat vanishing
  change ‖weighted‖ ≤ sourceConstant * _ at weightedBound
  change originalWeightedDatumNorm parameters context.lower length context.positive
    (context.lowerHalf.trans (by norm_num)) context.lengthPositive
    (actualExhaustionContextDatum parameters length compact context sourceSmall source flat 0) ≤
      baseConstant * (1 + M) * ‖quotientEta parameters 8 source‖ at baseBound
  rw [← actualExhaustionContextDatum_zeroBoundary parameters length compact context sourceSmall source flat 0] at baseBound
  change exhaustionDatumNorm parameters length compact context
    (actualExhaustionContextDatum parameters length compact context sourceSmall source flat 0) ≤ _ at baseBound
  have budgetBound : context.budget grade ≤ physicalBudget parameters context.state.val.val.field
      context.state.val.val.rho context.state.val.val.epsilon (grade + 14) :=
    physicalBudget_monotone _ _ _ _ (by omega : 8 + grade ≤ grade + 14)
  have baseNonnegative : 0 ≤ baseConstant * (1 + M) * ‖quotientEta parameters 8 source‖ := by positivity
  have product := (mul_le_mul_of_nonneg_left baseBound (context.budget_nonnegative grade)).trans
    (mul_le_mul_of_nonneg_right budgetBound baseNonnegative)
  have step := mul_le_mul_of_nonneg_left (add_le_add weightedBound product) inverse.choose_spec.1
  have extra : 0 ≤ inverse.choose * (baseConstant * (1 + M)) * ‖quotientEta parameters (grade + 8) source‖ :=
    mul_nonneg (mul_nonneg inverse.choose_spec.1 (mul_nonneg basePositive (by positivity))) (norm_nonneg _)
  nlinarith only [step,extra]

end Grad.ActualPuncturedFamily
