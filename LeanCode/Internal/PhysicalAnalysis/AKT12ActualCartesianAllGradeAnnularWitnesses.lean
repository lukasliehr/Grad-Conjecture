import AKT11ActualCartesianCofinalData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
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



/-- One all-grade constant family, chosen before the state and source,
controls the SAME actual cofinal annular solves of the actual Cartesian data. -/
theorem actualCartesianSource_cofinalWitnesses
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (M : ℝ) (Mnonnegative : 0 ≤ M) :
    ∃ constant : ℕ → ℝ, (∀ grade, 0 ≤ constant grade) ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (state : RetainedInverseState parameters length compact)
        (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          originalExhaustionPrimitiveRadius parameters length compact)
        (_stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source),
        let contexts := cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small
        ∃ retained : ∀ (_grade : ℕ) index, CoupledSpace (contexts index).lower length
            (contexts index).positive (contexts index).lengthPositive,
          ∀ grade index,
            ExhaustionRetainedInserted parameters length compact (contexts index) grade
              (actualExhaustionContextDatum parameters length compact (contexts index)
                (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
                source flat 0) (retained grade index) ∧
            ‖retained grade index‖ ≤ constant grade * (‖quotientEta parameters (grade + 8) source‖ +
              physicalBudget parameters (contexts index).state.val.val.field (contexts index).state.val.val.rho
                (contexts index).state.val.val.epsilon (grade + 14) * ‖quotientEta parameters 8 source‖) := by
  let estimate := fun grade => actualCartesianSource_annularEstimate parameters length compact lengthPositive grade M Mnonnegative
  refine ⟨fun grade => (estimate grade).choose, fun grade => (estimate grade).choose_spec.1, ?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing
  dsimp only
  let lane := fun grade index => (estimate grade).choose_spec.2
    (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small index)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    stateBound source flat vanishing
  exact ⟨fun grade index => (lane grade index).choose, fun grade index => (lane grade index).choose_spec⟩

end Grad.ActualPuncturedFamily
