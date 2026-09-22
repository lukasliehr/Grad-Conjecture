import AIT11ActualCoupledResidualCorrespondence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational Grad.AnnularCurrentSource
open Grad.AnnularCurrentGreen Grad.AnnularCurrentBoundary Grad.AnnularKernelL2 Grad.CircularHighRegularity
open Grad.AnnularSourceGraph Grad.AnnularTiltedReference

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
  (state : RetainedInverseState parameters length compact)
  (highSmall : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters length compact)

/-- Literal three-output packet of the actual high cross response. -/
def actualHighOffDiagonalOutput (field : lowEnergyGraph lower length positive) : DivisionRow 3 lower :=
  actualFullHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.1
    (crossKnownWeighted parameters lower (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field))
    (crossKnownAuxiliary parameters lower (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field))

theorem actualHighOffDiagonalOutput_same (field : lowEnergyGraph lower length positive) :
    actualHighOffDiagonalOutput parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field =
      graphDataPhysicalOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
        ((lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).toGraphKnown parameters lower) := by
  unfold actualHighOffDiagonalOutput
  rw [actualHighOffDiagonal_energy]
  rfl

theorem actualHighOffDiagonal_compact (field : lowEnergyGraph lower length positive) :
    CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength
      (actualHighOffDiagonalOutput parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field) := by
  rw [actualHighOffDiagonalOutput_same]
  exact graphDataPhysicalOutput_compact parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall _

/-- The actual second row is a distributional identity on every retained
high mode, with its original ordinary physical slope. -/
theorem actualHighOffDiagonal_ordinaryWeak (field : lowEnergyGraph lower length positive) (mode : HighAnnularMode) :
    Grad.GaugeCoefficients.Physical.WeightedTrace.CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0
        (actualHighOffDiagonalOutput parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field) mode))
      (physicalFluxOrdinarySlope parameters lower length positive
        (actualHighOffDiagonalOutput parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field) mode) :=
  (compactPhysicalPacketEquation_iff_ordinaryWeak parameters lower length positive (lowerHalf.trans_lt (by norm_num))
    lengthPositive widthHalf widthLength _).mp
      (actualHighOffDiagonal_compact parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field) mode

/-- The full original zero-inner test law includes the actual affine outer
flux, so no free trace has been introduced by the coupled iteration. -/
theorem actualHighOffDiagonal_packet (field : lowEnergyGraph lower length positive)
    (test : annularInnerZero lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    inner ℂ (highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength test.val)
      (actualHighOffDiagonalOutput parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 test.val)
      (graphDataPhysicalOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
        ((lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).toGraphKnown parameters lower)).val := by
  rw [actualHighOffDiagonalOutput_same]
  exact graphDataPhysicalOutput_packet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall _ test

theorem actualHighOffDiagonal_inner (field : lowEnergyGraph lower length positive) :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive
        (actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.1) = 0 :=
  actualHighCrossResponse_physical_inner parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall _

/-- The literal physical outer covector equals the genuine minus-beta cross datum. -/
theorem actualHighOffDiagonal_boundary (field : lowEnergyGraph lower length positive) :
    graphNativePhysicalBoundary state.outerInverseState 0 0
      (graphDataPhysicalOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall
        ((lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).toGraphKnown parameters lower))
      (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0
        (actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state highSmall field).ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 (0 : HighRadialSourceGraphs parameters lower 0)) =
      lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state field :=
  actualHighCrossResponse_physical_boundary parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state highSmall _

end Grad.AnnularCoupledInverse
