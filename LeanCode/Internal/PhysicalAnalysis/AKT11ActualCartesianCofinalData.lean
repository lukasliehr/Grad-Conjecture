import AKT10ActualCartesianSourceAnnularEstimate

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


variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)

def cartesianExhaustionContext (index : ℕ) : CoupledCoordinateContext parameters length compact :=
  fixedExhaustionContext parameters length compact lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    (originalExhaustionRadius_half length lengthPositive index)

def cartesianExhaustionDatum (source : SmoothQuotient parameters) (flat : IsFlat source)
    (index grade : ℕ) : OriginalStrongCarrier parameters (originalExhaustionRadius length index) 0 0 :=
  actualExhaustionContextDatum parameters length compact
    (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small index)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat grade

/-- The cofinal data preserve the actual full four original source graphs. -/
theorem cartesianExhaustionDatum_restrict (source : SmoothQuotient parameters) (flat : IsFlat source)
    (first second grade : ℕ) (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second) :
    originalFullSourceRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) included
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat first grade).val.ofLp.1 =
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat second grade).val.ofLp.1 :=
  actualOriginalSourceDatum_restrict parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    _ _ included (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
    ((originalExhaustionRadius_half length lengthPositive first).trans_lt (by norm_num))
    ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) grade source flat

theorem cartesianExhaustionDatum_base_bound (M : ℝ)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source) (index : ℕ) :
    exhaustionDatumNorm parameters length compact
      (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small index)
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) ≤
      originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖ := by
  change originalWeightedDatumNorm parameters (originalExhaustionRadius length index) length
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) ≤ _
  exact actualOriginalSourceDatum_base_bound parameters length state.val.val.rho state.val.val.epsilon lengthPositive
    state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    M stateBound _ (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) source flat vanishing

end Grad.ActualPuncturedFamily
