import AKI34ArbitraryHighFluxPhysicalRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularHighRadial
open Grad.AnnularVariational Grad.CircularHighRegularity Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy
open Grad.AnnularRestriction Grad.AnnularPhysicalSolution
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev compactCandidate := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate
private abbrev compactDatum := originalToStrong parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
private abbrev compactPacket := fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state
  (compactDatum parameters length lower positive lowerHalf lengthPositive data)
  (compactCandidate parameters length lower positive lowerHalf lengthPositive candidate)

include represented

/-- The literal AH24 residual yields the full compact test equation on an
arbitrary represented candidate, through its genuine classical derivative. -/
theorem OriginalTupleObservation.highCompactEquation :
    CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength
      (compactPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate) := by
  apply compactPhysicalPacketEquation_of_ordinaryWeak parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength
  intro mode
  apply (rawHighXPacket_weak_iff parameters lower length positive _ mode).mp
  let physicalSection := rawHighXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (compactCandidate parameters length lower positive lowerHalf lengthPositive candidate).ofLp.1.ofLp.2 mode
  let rhs : C(ℝ,ComplexEuclidean 1) := frequencyNumerator (some false) mode.val •
    originalTupleSlopeCurve parameters lower (lowerHalf.trans_lt (by norm_num)) tuple 0 mode.val
  apply collarWeakDerivative_of_representatives lower (lowerHalf.trans (by norm_num)) _ _
    (radialSectionExtension 1 lower (lowerHalf.trans (by norm_num)) physicalSection) rhs
  · have value := rawHighXSection_bulk parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      (compactCandidate parameters length lower positive lowerHalf lengthPositive candidate).ofLp.1.ofLp.2 mode
    have same := fullStrongHighPacket_fluxValue parameters length compact lower positive lowerHalf lengthPositive state
      (compactDatum parameters length lower positive lowerHalf lengthPositive data)
      (compactCandidate parameters length lower positive lowerHalf lengthPositive candidate)
    rw [same] at value
    rw [← value]
    filter_upwards [radialSectionL2_ae 1 lower positive (lowerHalf.trans (by norm_num)) physicalSection] with radius actual
    exact actual.symm
  · exact represented.highFluxRHS parameters length compact lower positive lowerHalf lengthPositive state data candidate tuple mode
  · exact represented.highX_derivative parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state data candidate tuple mode

end Grad.AnnularOriginalSmoothCore
