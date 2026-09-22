import AKG9SameHomogeneousPacketRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentSource Grad.AnnularHighTilt
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularForwardDatum Grad.AnnularKnownLow
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
attribute [local instance] originalAmbientRealNormed restrictionStrongRealNormed restrictionStrongRealModule
  forwardSourcesRealNormed forwardSourcesRealModule

/-- Literal BF5 four stored source/residual rows, from the four ORIGINAL
copied blocks; F0/RF0 use the same genuine graph. -/
def originalStoredKnownRows (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (sources : ForwardSourceBlocks parameters lower) : HighKnownSourceBulk lower :=
  WithLp.toLp 2 ![
    divisionHighWeight lower positive bounded (unweightedSourceF0Bulk parameters lower sources.ofLp.1.ofLp.1),
    divisionHighWeight lower positive bounded (unweightedSourceRF0Bulk parameters lower sources.ofLp.1.ofLp.1),
    divisionHighWeight lower positive bounded (unweightedSourceF2Bulk parameters lower sources.ofLp.1.ofLp.2),
    divisionHighWeight lower positive bounded sources.ofLp.2.ofLp.1]

theorem originalStrongWeight_knownRows (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    strongKnownBulk parameters lower positive bounded
      (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0 data) =
      originalStoredKnownRows parameters lower positive bounded data.val.ofLp.1 := by
  rw [originalStrongWeightEquivalence_eq_reconstruction]
  rfl

theorem originalStrongWeight_g (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    (strongToLow parameters lower positive bounded 0 0
      (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0 data)).ofLp.1.ofLp.2 =
    divisionHighWeight lower positive bounded (originalAngularDecode lower data.val.ofLp.1.ofLp.2.ofLp.2) := by
  exact congrArg (fun value : StrongDataCarrier parameters lower positive bounded 0 0 =>
    (strongToLow parameters lower positive bounded 0 0 value).ofLp.1.ofLp.2)
    (originalStrongWeightEquivalence_eq_reconstruction parameters lower length positive bounded lengthPositive 0 0 data)

/-- All four original source rows restrict with the same actual high tilt. -/
theorem originalStoredKnownRows_restriction (parameters : PhaseParameters) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (bounded : upper ≤ 1) (included : lower ≤ upper)
    (sources : ForwardSourceBlocks parameters lower) (slot : Fin 4) :
    originalStoredKnownRows parameters upper upperPositive bounded
      (originalFullSourceRestriction parameters lower upper included sources) slot =
    originalBulkRestriction 1 lower upper included
      (originalStoredKnownRows parameters lower lowerPositive (included.trans bounded) sources slot) := by
  fin_cases slot
  · change divisionHighWeight upper upperPositive bounded
      (unweightedSourceF0Bulk parameters upper (sourceGraphRestriction parameters 1 lower upper included 1 0 0 sources.ofLp.1.ofLp.1)) =
      originalBulkRestriction 1 lower upper included
        (divisionHighWeight lower lowerPositive (included.trans bounded) (unweightedSourceF0Bulk parameters lower sources.ofLp.1.ofLp.1))
    rw [originalBulkRestriction_highWeight,originalBulkRestriction_F0]
  · change divisionHighWeight upper upperPositive bounded
      (unweightedSourceRF0Bulk parameters upper (sourceGraphRestriction parameters 1 lower upper included 1 0 0 sources.ofLp.1.ofLp.1)) =
      originalBulkRestriction 1 lower upper included
        (divisionHighWeight lower lowerPositive (included.trans bounded) (unweightedSourceRF0Bulk parameters lower sources.ofLp.1.ofLp.1))
    rw [originalBulkRestriction_highWeight,originalBulkRestriction_RF0]
  · change divisionHighWeight upper upperPositive bounded
      (unweightedSourceF2Bulk parameters upper (sourceGraphRestriction parameters 1 lower upper included 0 0 0 sources.ofLp.1.ofLp.2)) =
      originalBulkRestriction 1 lower upper included
        (divisionHighWeight lower lowerPositive (included.trans bounded) (unweightedSourceF2Bulk parameters lower sources.ofLp.1.ofLp.2))
    rw [originalBulkRestriction_highWeight,originalBulkRestriction_F2]
  · exact (originalBulkRestriction_highWeight lower upper included lowerPositive upperPositive bounded sources.ofLp.2.ofLp.1).symm

/-- Literal restriction of the four normalized rows as a finite Hilbert family. -/
def knownRowsRestriction (lower upper : ℝ) (included : lower ≤ upper)
    (source : HighKnownSourceBulk lower) : HighKnownSourceBulk upper :=
  WithLp.toLp 2 (fun slot => originalBulkRestriction 1 lower upper included (source slot))

theorem knownLowSevenPacket_restriction (lower upper : ℝ) (included : lower ≤ upper)
    (source : HighKnownSourceBulk lower) :
    originalBulkRestriction 7 lower upper included (knownLowSevenPacket lower source) =
      knownLowSevenPacket upper (knownRowsRestriction lower upper included source) := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae 7 lower upper included (knownLowSevenPacket lower source),
    (knownLowSevenPacket_ae lower source).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    knownLowSevenPacket_ae upper (knownRowsRestriction lower upper included source),
    originalBulkRestriction_ae 1 lower upper included (source 0),
    originalBulkRestriction_ae 1 lower upper included (source 1),
    originalBulkRestriction_ae 1 lower upper included (source 2)]
    with radius restricted sourceLaw targetLaw first second third
  rw [restricted mode,sourceLaw mode,targetLaw mode]
  change _ = ((originalBulkRestriction 1 lower upper included (source 0) mode radius) 0) • _ +
    ((originalBulkRestriction 1 lower upper included (source 1) mode radius) 0) • _ +
    ((originalBulkRestriction 1 lower upper included (source 2) mode radius) 0) • _
  rw [first mode,second mode,third mode]

end Grad.AnnularRestriction
