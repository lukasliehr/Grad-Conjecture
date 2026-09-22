import AKZ12ActualSourcePhysicalEnergies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPhysicalField
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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

open Grad.ActualPuncturedFamily

/-- Actual higher-vanishing source data produce the SAME full equation
family and physical U/S-over-radius weighted energies, at original width. -/
theorem actualCartesianSource_physicalEnergyFamily
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (M : ℝ) (Mnonnegative : 0 ≤ M) :
    ∃ constant : ℕ → ℝ, (∀ grade, 0 ≤ constant grade) ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (state : RetainedInverseState parameters length compact)
        (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          originalExhaustionPrimitiveRadius parameters length compact)
        (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source),
        let lower := originalExhaustionRadius length
        let positive := originalExhaustionRadius_positive length lengthPositive
        let half := originalExhaustionRadius_half length lengthPositive
        let data := cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat
        ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
          (graded : ∀ k (_t : ℕ), CoupledSpace (lower k) length (positive k) lengthPositive),
          (∀ k, limit k ∈ OriginalObservedEquationGraph parameters length compact (lower k) (positive k)
            (half k) lengthPositive widthHalf widthLength state ∧
            (limit k).ofLp.2 = (data k 0).val.ofLp.1 ∧
            originalOuterBoundaryTrace parameters length compact (lower k) (positive k) (half k) lengthPositive state
              ((limit k).ofLp.1,(limit k).ofLp.2.ofLp.1) = 0 ∧
            originalWeightedRetainedNorm parameters (lower k) length (positive k) ((half k).trans (by norm_num)) lengthPositive
              (limit k).ofLp.1 ≤ 2 * independentCoupledDataConstant parameters length compact *
                (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖)) ∧
          (∀ k l (included : lower k ≤ lower l),
            originalFiveBlockRestriction parameters (lower k) (lower l) length (positive k) (positive l)
              ((half l).trans_lt (by norm_num)) lengthPositive included (limit k) = limit l) ∧
          (∀ k t, CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
            (originalWeightedRetainedObservation parameters (lower k) length (positive k) ((half k).trans (by norm_num)) lengthPositive (limit k))
            (graded k t) ∧ ‖graded k t‖ ≤ constant t * (‖quotientEta parameters (t + 8) source‖ +
              physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t + 14) *
                ‖quotientEta parameters 8 source‖)) ∧
          globalPhysicalBulkEnergy 3 lower
            (originalCovariantFamily parameters length compact lower positive half lengthPositive state (fun k => data k 0) limit) ≤
            ENNReal.ofReal ((cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖) ^ 2) ∧
          globalPhysicalBulkEnergy 3 lower
            (originalRotatedCovariantFamily parameters length compact lower positive half lengthPositive state (fun k => data k 0) limit) ≤
            ENNReal.ofReal ((cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖) ^ 2) ∧
          globalPhysicalBulkEnergy 3 lower
            (cartesianOriginalPhysicalVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat limit) ≤
            ENNReal.ofReal ((physicalUActionConstant parameters length 0 * (1 + M) *
              (cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖)) ^ 2) ∧
          globalPhysicalBulkEnergy 1 lower
            (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat limit) ≤
            ENNReal.ofReal ((cartesianScalarBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖) ^ 2) := by
  let full := actualCartesianSource_globalCovariantFamily parameters length compact lengthPositive M Mnonnegative
  refine ⟨full.choose,full.choose_spec.1,?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing
  dsimp only
  let solved := full.choose_spec.2 widthHalf widthLength state small stateBound source flat vanishing
  refine Exists.elim solved ?_
  intro limit remainder
  refine Exists.elim remainder ?_
  intro graded laws
  refine ⟨limit,graded,laws.1,laws.2.1,laws.2.2.1,laws.2.2.2.1,laws.2.2.2.2,?_,?_⟩
  · exact cartesianOriginalPhysicalVectorFamily_globalBound parameters length compact lengthPositive widthHalf widthLength state small
      source flat limit M Mnonnegative stateBound vanishing (fun index => (laws.1 index).2.2.2) laws.2.1
  · exact cartesianOriginalScalarOverRadiusFamily_globalBound parameters length compact lengthPositive widthHalf widthLength state small
      source flat limit M stateBound vanishing (fun index => (laws.1 index).2.2.2) laws.2.1

end Grad.ActualPhysicalField
