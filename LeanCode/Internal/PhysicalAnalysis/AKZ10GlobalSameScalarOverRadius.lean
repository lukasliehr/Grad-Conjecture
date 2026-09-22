import AKZ8OriginalScalarWeightedEnergy

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

variable (parameters : PhaseParameters) (length : ℝ)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index)
    (half : ∀ index, collars index ≤ 1 / 2) (lengthPositive : 0 < length)
    (data : ∀ index, OriginalStrongCarrier parameters (collars index) 0 0)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (collars index) length (positive index))

def originalScalarOverRadiusFamily (index : ℕ) : DivisionRow 1 (collars index) :=
  originalScalarOverRadius parameters length (collars index) (positive index)
    ((half index).trans (by norm_num)) lengthPositive (data index) (fields index)

variable (decreasing : Antitone collars)
    (sameSources : ∀ first second (included : collars first ≤ collars second),
      (data second).val.ofLp.1 = originalFullSourceRestriction parameters (collars first) (collars second) included (data first).val.ofLp.1)
    (compatible : ∀ first second (included : collars first ≤ collars second),
      originalFiveBlockRestriction parameters (collars first) (collars second) length (positive first) (positive second)
        ((half second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)
include compatible sameSources

theorem originalScalarOverRadiusFamily_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 1 (collars second) (collars first) (decreasing ordered)
      (originalScalarOverRadiusFamily parameters length collars positive half lengthPositive data fields second) =
      originalScalarOverRadiusFamily parameters length collars positive half lengthPositive data fields first := by
  have packet := originalSevenPacket_family_restriction parameters length (collars second) (collars first)
    (positive second) (positive first) ((half first).trans_lt (by norm_num)) lengthPositive (decreasing ordered)
    (data second) (data first) (sameSources second first (decreasing ordered))
    (fields second) (fields first) (compatible second first (decreasing ordered))
  exact (bulkMatrixUnit_restriction (collars second) (collars first) (decreasing ordered) (0 : Fin 1) (3 : Fin 7) _).trans
    (congrArg (bulkMatrixUnit (collars first) (0 : Fin 1) (3 : Fin 7)) packet)

include decreasing in
theorem originalScalarOverRadiusFamily_globalBound (cofinal : Tendsto collars atTop (𝓝 0)) (constant : ℝ)
    (estimate : ∀ index, ‖originalScalarOverRadiusFamily parameters length collars positive half lengthPositive data fields index‖ ≤ constant) :
    globalPhysicalBulkEnergy 1 collars (originalScalarOverRadiusFamily parameters length collars positive half lengthPositive data fields) ≤
      ENNReal.ofReal (constant ^ 2) :=
  globalPhysicalBulkEnergy_bound 1 collars _ decreasing
    (originalScalarOverRadiusFamily_compatible parameters length collars positive half lengthPositive data fields decreasing sameSources compatible)
    positive cofinal constant estimate

end Grad.ActualPhysicalField
