import AKX2UniformOriginalGraphReconstruction
import AKX3SamePhysicalReconstructionLocality
import AKX6GlobalCompatiblePhysicalBulk

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

/-- The actual same full-source reconstructed covariant family. -/
def originalCovariantFamily (index : ℕ) : DivisionRow 3 (collars index) :=
  originalGraphCovariant parameters length compact (collars index) (positive index)
    ((half index).trans (by norm_num)) lengthPositive state (data index) (fields index)

def originalRotatedCovariantFamily (index : ℕ) : DivisionRow 3 (collars index) :=
  originalGraphRotatedCovariant parameters length compact (collars index) (positive index)
    ((half index).trans (by norm_num)) lengthPositive state (data index) (fields index)

variable (decreasing : Antitone collars)
    (sameSources : ∀ first second (included : collars first ≤ collars second),
      (data second).val.ofLp.1 = originalFullSourceRestriction parameters (collars first) (collars second) included (data first).val.ofLp.1)
    (compatible : ∀ first second (included : collars first ≤ collars second),
      originalFiveBlockRestriction parameters (collars first) (collars second) length (positive first) (positive second)
        ((half second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)
include compatible sameSources

theorem originalCovariantFamilies_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (collars second) (collars first) (decreasing ordered)
      (originalCovariantFamily parameters length compact collars positive half lengthPositive state data fields second) =
      originalCovariantFamily parameters length compact collars positive half lengthPositive state data fields first ∧
    originalBulkRestriction 3 (collars second) (collars first) (decreasing ordered)
      (originalRotatedCovariantFamily parameters length compact collars positive half lengthPositive state data fields second) =
      originalRotatedCovariantFamily parameters length compact collars positive half lengthPositive state data fields first :=
  originalGraphCovariants_restriction parameters length compact (collars second) (collars first)
    (positive second) (positive first) ((half first).trans_lt (by norm_num)) lengthPositive (decreasing ordered)
    state (data second) (data first) (sameSources second first (decreasing ordered))
    (fields second) (fields first) (compatible second first (decreasing ordered))

end Grad.ActualPuncturedReconstruction
