import AKX8UniformPhysicalFamilyBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedReconstruction
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


variable (parameters : PhaseParameters) (length compact : ℝ)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index)
    (half : ∀ index, collars index ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : ∀ index, OriginalStrongCarrier parameters (collars index) 0 0)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (collars index) length (positive index))

variable (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (sameSources : ∀ first second (included : collars first ≤ collars second),
      (data second).val.ofLp.1 = originalFullSourceRestriction parameters (collars first) (collars second) included (data first).val.ofLp.1)
    (compatible : ∀ first second (included : collars first ≤ collars second),
      originalFiveBlockRestriction parameters (collars first) (collars second) length (positive first) (positive second)
        ((half second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)
    (constant : ℝ)
    (estimate : ∀ index,
      ‖originalCovariantFamily parameters length compact collars positive half lengthPositive state data fields index‖ +
        ‖originalRotatedCovariantFamily parameters length compact collars positive half lengthPositive state data fields index‖ ≤ constant)
include compatible sameSources cofinal estimate decreasing

/-- Both reconstructed fields have genuine finite global weighted bulk
energy, with the identical uniform collar constant. -/
theorem originalCovariantFamilies_globalBound :
    globalPhysicalBulkEnergy 3 collars
      (originalCovariantFamily parameters length compact collars positive half lengthPositive state data fields) ≤ ENNReal.ofReal (constant ^ 2) ∧
    globalPhysicalBulkEnergy 3 collars
      (originalRotatedCovariantFamily parameters length compact collars positive half lengthPositive state data fields) ≤ ENNReal.ofReal (constant ^ 2) := by
  have actual := originalCovariantFamilies_compatible parameters length compact collars positive half lengthPositive
    state data fields decreasing sameSources compatible
  constructor
  · apply globalPhysicalBulkEnergy_bound 3 collars _ decreasing (fun first second ordered => (actual first second ordered).1) positive cofinal constant
    intro index
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (estimate index)
  · apply globalPhysicalBulkEnergy_bound 3 collars _ decreasing (fun first second ordered => (actual first second ordered).2) positive cofinal constant
    intro index
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (estimate index)

end Grad.ActualPuncturedReconstruction
