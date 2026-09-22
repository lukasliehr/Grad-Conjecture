import AKI29ReversibleHighPhysicalWeakRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularHighRadial
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularLowEnergy
open Grad.AnnularVariational Grad.CircularHighRegularity Grad.BoundaryKernelAction Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6*length))
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev firstCandidate := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate
private abbrev firstDatum := originalToStrong parameters lower length positive bounded.le lengthPositive 0 0 data
private abbrev firstPacket := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
  (firstDatum parameters length lower positive bounded lengthPositive data)
  (firstCandidate parameters length lower positive bounded lengthPositive candidate)
private abbrev firstFullRow := lowPhysicalRowAction parameters length compact lower positive bounded.le state 0
    (firstPacket parameters length lower positive bounded lengthPositive data candidate) +
  highSourceF lower (strongKnownBulk parameters lower positive bounded.le
    (firstDatum parameters length lower positive bounded lengthPositive data))

include represented

/-- The original raw xi derivative equals the SAME full stored first RHS. -/
theorem OriginalTupleObservation.highFirstRHS (mode : HighAnnularMode) :
    collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
      (radialOrdinary 1 lower positive
        (firstFullRow parameters length compact lower positive bounded lengthPositive state data candidate mode.val)) =ᵐ[volume.restrict (Icc lower 1)]
      originalTupleSlopeCurve parameters lower bounded tuple 1 mode.val := by
  filter_upwards [rawHighPhase_radialOrdinary_ae parameters lower positive
      (firstFullRow parameters length compact lower positive bounded lengthPositive state data candidate) mode.val,
    lowRhoPhysicalCoefficient_add_ae parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state 0
        (firstPacket parameters length lower positive bounded lengthPositive data candidate))
      (highSourceF lower (strongKnownBulk parameters lower positive bounded.le
        (firstDatum parameters length lower positive bounded lengthPositive data))),
    represented.rawFirst parameters length compact lower positive bounded lengthPositive state data candidate tuple,
    ae_restrict_mem measurableSet_Icc] with radius decoded added original inside
  have nonzero : mode.val.1 ≠ 0 := by have large := mode.property; intro zero; simp [zero] at large
  rw [decoded,added mode.val,originalTupleSlopeCurve_same parameters lower bounded tuple 1 mode.val radius inside,
    original inside mode.val]
  simp only [angularMeanFreeMultiplier,if_neg nonzero,one_smul]
  rfl

/-- Genuine high weak derivative uniqueness turns the tuple's first AH24
residual into the actual completed stored derivative equality. -/
theorem OriginalTupleObservation.highStoredFirst :
    highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
      (firstCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.1 =
      highFullRestriction lower
        (firstFullRow parameters length compact lower positive bounded lengthPositive state data candidate) := by
  apply lp.ext
  funext mode
  apply collarScalar_injective_of_pos lower
    ⟨reciprocalRadialWeight lower (fun _ => 1),reciprocalRadialWeight_continuous lower positive _ continuous_const⟩
    (fun radius => by
      change 0 < 1 / Real.sqrt (max lower radius)
      exact div_pos zero_lt_one (Real.sqrt_pos.mpr (positive.trans_le (le_max_left _ _))))
  apply collarScalar_injective_of_pos lower (rawHighPhase parameters lower positive mode.val.2)
    (rawHighPhase_positive parameters lower positive mode.val.2)
  apply collarWeakDerivative_unique lower
    (rawHighXi_weak parameters lower length positive bounded lengthPositive widthHalf widthLength
      (firstCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.1 mode)
  apply collarWeakDerivative_of_representatives lower bounded.le _ _
    (radialSectionExtension 1 lower bounded.le
      (rawHighXiSection parameters lower length positive bounded
        (firstCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.1 mode))
    (originalTupleSlopeCurve parameters lower bounded tuple 1 mode.val)
  · filter_upwards [radialSectionL2_ae 1 lower positive bounded.le
      (rawHighXiSection parameters lower length positive bounded
        (firstCandidate parameters length lower positive bounded lengthPositive candidate).ofLp.1.ofLp.1 mode)] with radius same
    exact same.symm
  · exact represented.highFirstRHS parameters length compact lower positive bounded lengthPositive state data candidate tuple mode
  · exact represented.highXi_derivative parameters length compact lower positive bounded lengthPositive state data candidate tuple mode

end Grad.AnnularOriginalSmoothCore
