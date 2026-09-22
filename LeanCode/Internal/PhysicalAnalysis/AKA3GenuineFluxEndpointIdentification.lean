import AKA1BoundedOriginalBoundaryTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularForwardTraces
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentBoundary Grad.AnnularLowEnergy Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.CircularHighRegularity Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCurrentGreen Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularFullSource

private theorem inverseRealComplexSmul (radius : ℝ) (nonzero : radius ≠ 0)
    (vector : ComplexEuclidean 1) : radius⁻¹ • ((radius : ℂ) • vector) = vector := by
  rw [← smul_assoc]
  have scalar : radius⁻¹ • (radius : ℂ) = (1 : ℂ) := by
    change ((radius⁻¹ : ℝ) : ℂ) * (radius : ℂ) = 1
    rw [← Complex.ofReal_mul,inv_mul_cancel₀ nonzero,Complex.ofReal_one]
  rw [scalar,one_smul]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The physical moment graph has the SAME flux representative multiplied
by the literal radius. This follows from the existing L2 coordinates. -/
theorem physicalFluxMomentSection_same (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength field)
    (flux : annularOmegaGraph lower length positive lengthPositive)
    (sameValue : flux.val 0 = highPhysicalOutput lower 0 field) (mode : HighAnnularMode) :
    weightedRadialSection 1 lower positive bounded
      (physicalFluxMomentGraph parameters lower length positive lengthPositive widthHalf widthLength bounded field equation mode) =
      radialSectionScalar lower annularRadiusCurve
        (annularFluxSection lower positive bounded
          (annularOmegaIntoNu lower length positive lengthPositive flux) mode) := by
  apply radialSectionL2_injective lower positive bounded
  rw [weightedRadialSection_bulk,physicalFluxMomentGraph_value,radialSectionL2_scalar,annularFluxSection_bulk]
  change collarScalar 1 lower annularRadiusCurve
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) =
    collarScalar 1 lower annularRadiusCurve (radialOrdinary 1 lower positive (flux.val 0 mode))
  rw [sameValue]

theorem physicalFluxMoment_outer_same (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength field)
    (flux : annularOmegaGraph lower length positive lengthPositive)
    (sameValue : flux.val 0 = highPhysicalOutput lower 0 field) (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive bounded 1
      (physicalFluxMomentGraph parameters lower length positive lengthPositive widthHalf widthLength bounded field equation mode) =
      annularFluxSection lower positive bounded
        (annularOmegaIntoNu lower length positive lengthPositive flux) mode
        ⟨radialEndpointRadius lower 1,radialEndpointRadius_mem lower bounded.le 1⟩ := by
  have same := congrArg (fun representative : RadialContinuousSection 1 lower =>
      representative ⟨radialEndpointRadius lower 1,radialEndpointRadius_mem lower bounded.le 1⟩)
    (physicalFluxMomentSection_same parameters lower length positive bounded lengthPositive widthHalf widthLength field equation flux sameValue mode)
  rw [weightedRadialSection_endpoint] at same
  simpa [radialSectionScalar,annularRadiusCurve,radialEndpointRadius] using same

/-- Exact negative-half outer trace recovered from the literal physical
moment endpoint, including the high angular support. -/
theorem coupledHighFluxOuter_eq (lowerHalf : lower ≤ 1 / 2)
    (candidate : CoupledSpace lower length positive lengthPositive) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength field)
    (sameValue : candidate.ofLp.1.ofLp.2.val 0 = highPhysicalOutput lower 0 field)
    (datum : HighBoundaryPrimitive parameters 0 0)
    (moment : ∀ mode : HighAnnularMode,
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower length positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num)) field equation mode) =
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • datum.val mode.val) :
    coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate = datum := by
  apply Subtype.ext
  apply lp.ext
  funext query
  by_cases high : 3 ≤ |query.1|
  · let mode : HighAnnularMode := ⟨query,high⟩
    change (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).val mode.val = datum.val mode.val
    rw [coupledHighFluxOuter_coefficient,annularFluxTrace_apply,
      ← physicalFluxMoment_outer_same parameters lower length positive (lowerHalf.trans_lt (by norm_num))
        lengthPositive widthHalf widthLength field equation candidate.ofLp.1.ofLp.2 sameValue mode,moment mode]
    exact inverseRealComplexSmul _
      (Real.sqrt_pos.mpr (Grad.AnnularFluxTrace.annularFrequency_pos mode)).ne' _
  · change highBoundaryExtensionValue _ query = datum.val query
    rw [highBoundaryExtensionValue_low _ query high]
    symm
    calc
      datum.val query = (negativeTraceWeight parameters 0 0 query : ℂ) •
          negativeTraceCoefficient parameters 0 0 datum.val query := (negativeTrace_weighted parameters 0 0 datum.val query).symm
      _ = 0 := by rw [datum.property query (lt_of_not_ge high),smul_zero]

end Grad.AnnularForwardTraces
