import AJN4SameHighFluxWeakDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularHighRadial
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.CircularHighWeak Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularCurrentGreen Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularFullSource
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

theorem sharedStrongResponse_sameFlux :
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1.ofLp.2.val 0 =
      highPhysicalOutput lower 0
        (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) := by
  rw [← sharedStrongPhysicalOutput_sameFull parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data]
  exact coupledPhysicalOutput_sameFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)

def sharedRawHighXRHS (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  rawHighXPacketRHS parameters lower L positive
    (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) mode

/-- Genuine derivative of the SAME solved X section from the original weak
flux equation. Only the continuous full-row representative is supplied. -/
theorem sharedRawHighX_hasDerivWithinAt (mode : HighAnnularMode) (rhs : C(ℝ, ComplexEuclidean 1))
    (same : sharedRawHighXRHS parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode
      =ᵐ[volume.restrict (Icc lower 1)] rhs)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
      (rawHighXSection parameters lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1.ofLp.2 mode))
      (rhs radius) (Icc lower 1) radius :=
  rawHighX_hasDerivWithinAt parameters lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive _ _ mode
    (sharedStrongResponse_sameFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (sharedStrongResponse_fullOrdinaryWeak parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode)
    rhs same radius inside

end Grad.AnnularHighRadial
