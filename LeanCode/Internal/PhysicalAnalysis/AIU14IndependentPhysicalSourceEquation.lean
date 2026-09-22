import AIU9OriginalCoupledWeakRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularFullSource
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.AnnularTiltedReference Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

open Grad.AnnularPhysicalSolution Grad.AnnularCrossMaps Grad.AnnularOmegaGraph

/-- The actual independently supplied first-row flux, ordinary weak rows,
physical incoming and genuine moment boundary trace imply the exact sourced
equation on the original closed high graph. -/
theorem independentHighPhysicalSource_equation
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : annularEnergySpace lower L positive) (x : DivisionRow 1 lower)
    (flux : annularOmegaGraph lower L positive lengthPositive)
    (fluxValue : flux.val 0 = highFullRestriction lower x)
    (high : ∀ mode : ℤ × ℤ, |mode.1| < 3 → x mode = 0)
    (incoming : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive field) = data.innerValue)
    (first : retainedAAction parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state x =
      eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, data.weighted)))
    (weak : ∀ mode : HighAnnularMode,
      CollarWeakDerivative lower
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x) mode))
        (physicalFluxOrdinarySlope parameters lower L positive
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x) mode))
    (outerX : HighBoundaryPrimitive parameters 0 0)
    (physicalBoundary : graphNativePhysicalBoundary state.outerInverseState 0 0 outerX
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 field)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) = data.datum)
    (outer : ∀ mode : HighAnnularMode,
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num))
          (independentPhysicalBulk parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field x)
          (compactPhysicalPacketEquation_of_ordinaryWeak parameters lower L positive (lowerHalf.trans_lt (by norm_num))
            lengthPositive widthHalf widthLength _ weak) mode) =
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • outerX.val mode.val) :
    HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data
      (WithLp.toLp 2 (field, flux)) := by
  obtain ⟨energy, value⟩ := independentPhysicalWeak_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    small data field x high incoming first weak outerX physicalBoundary outer
  have fluxSame : flux = graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
    apply annularOmegaGraph_value_injective lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    change flux.val 0 = highPhysicalOutput lower 0
      (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    rw [fluxValue, value]
    rfl
  have same : WithLp.toLp 2 (field, flux) =
      fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
    rw [energy, fluxSame]
    rfl
  exact (highSourceEquation_iff_response parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data _).mpr same

end Grad.AnnularFullSource
