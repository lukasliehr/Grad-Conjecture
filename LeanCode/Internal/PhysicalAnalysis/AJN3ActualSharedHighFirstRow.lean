import AJN2SameHighXiWeakDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularHighRadial
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.CircularHighWeak Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularCurrentGreen Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

/-- The actual raw first-row forcing, retaining the full original seven input and f. -/
def sharedRawHighXiRHS (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive
      ((lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) +
        highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)) mode.val))

theorem sharedRawHighXiRHS_same (mode : HighAnnularMode) :
    sharedRawHighXiRHS parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode =
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive
          (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength
            (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1.ofLp.1 mode)) := by
  have row := congrArg (fun field : DivisionRow 1 lower => field mode.val)
    (sharedStrongResponse_fullHighFirstRow parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
  dsimp only at row
  rw [highBulkIntoFull_high, highRowProjection_high] at row
  unfold sharedRawHighXiRHS
  rw [row]

/-- Genuine derivative of the SAME solved Xi section from the full physical row.
Only the identification of its continuous right-hand side is supplied. -/
theorem sharedRawHighXi_hasDerivWithinAt (mode : HighAnnularMode) (rhs : C(ℝ, ComplexEuclidean 1))
    (same : sharedRawHighXiRHS parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode
      =ᵐ[volume.restrict (Icc lower 1)] rhs)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
      (rawHighXiSection parameters lower L positive (lowerHalf.trans_lt (by norm_num))
        (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1.ofLp.1 mode))
      (rhs radius) (Icc lower 1) radius := by
  apply rawHighXi_hasDerivWithinAt parameters lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength
  rw [← sharedRawHighXiRHS_same parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data]
  exact same
  exact inside

end Grad.AnnularHighRadial
