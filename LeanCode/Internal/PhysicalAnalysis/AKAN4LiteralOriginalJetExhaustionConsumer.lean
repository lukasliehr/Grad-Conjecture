import AKAN3ActualJetExhaustionTwenty

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.FinitePhysicalJetLift
open Grad.ActualPuncturedFamily Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates
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




/-- Exact original real-flat-source consumer: the very same EX family is
fed by F minus the literal physical derivative of the accepted real linear
finite lift. This is the native estimate, not the remaining physical weak sum. -/
theorem actualFiniteJet_exhaustion_literal_consumer
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ constant : ℕ → ℝ, (∀ t, 0 ≤ constant t) ∧
      ∃ baseConstant : ℝ, 0 ≤ baseConstant ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
        (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR)
        (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |seed 1| ≤ compact)
        (deltaSmall : |seed 2| ≤ compact) (parameterSmall : |seed 3| ≤ compact)
        (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 8 ≤ actualJetExhaustionRadius parameters length compact)
        (_bounded : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 20 ≤ 1)
        (source : OriginalFlatSource parameters length),
        let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
        let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
          compactNonnegative alphaSmall deltaSmall parameterSmall
        let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
        let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
        let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
        ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat,
          residual = (source.val - literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis
            (actualFiniteFlatLiftLinear parameters length (seed 0) lengthPositive reference insideR seed insideS base low source).val).val ∧
          (∀ k t, family.nativeNorm k t ≤ constant t *
            (‖quotientEta parameters (t + 20) source.val.val‖ +
              physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
                (seed 0) base.1 (t + 20) * ‖quotientEta parameters 20 source.val.val‖)) ∧
          (∀ k, family.nativeNorm k 0 ≤ baseConstant * ‖quotientEta parameters 20 source.val.val‖) := by
  obtain ⟨constant,nonnegative,baseConstant,baseNonnegative,solve⟩ :=
    actualFiniteJet_exhaustion_twenty parameters length compact lengthPositive
  refine ⟨constant,nonnegative,baseConstant,baseNonnegative,?_⟩
  intro widthHalf widthLength reference insideR seed insideS base axis compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
  dsimp only
  obtain ⟨family,high,baseBound⟩ := solve widthHalf widthLength reference insideR seed insideS base axis
    compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
  refine ⟨family,?_,high,baseBound⟩
  rw [actualFiniteFlatLiftLinear_apply]
  exact actualFiniteSourceResidual_literal parameters length (seed 0) lengthPositive reference insideR seed insideS base
    (actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small) axis source

end Grad.FinitePhysicalJetLift
