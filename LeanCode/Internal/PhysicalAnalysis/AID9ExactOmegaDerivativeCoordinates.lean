import AID8ActualOmegaNormalizedOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularOmegaGraph Grad.AnnularFluxTrace

theorem physicalOmegaFactor_cancel (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (slot : Fin 4) (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularOmegaCurve lower L positive mode)
      (collarScalar 1 lower (physicalOmegaFactor parameters lower L positive mode slot) field) =
    collarScalar 1 lower (physicalRawFactor parameters lower L positive mode slot) field := by
  rw [collarScalar_mul_apply]
  apply congrArg (fun coefficient : C(ℝ, ℝ) => collarScalar 1 lower coefficient field)
  ext radius
  change annularOmegaCurve lower L positive mode radius *
    (physicalRawFactor parameters lower L positive mode slot radius / annularOmegaCurve lower L positive mode radius) = _
  exact mul_div_cancel₀ _ (annularOmegaCurve_pos lower L positive mode radius).ne'

theorem collarScalar_real_multiple (lower coefficient : ℝ) (curve : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (coefficient • curve) field = coefficient • collarScalar 1 lower curve field := by
  change collarScalar 1 lower (ContinuousMap.const ℝ coefficient * curve) field = _
  rw [← collarScalar_mul_apply, collarScalar_const]

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

theorem physicalOmegaOperator_ordinary (slot : Fin 4) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    collarScalar 1 lower (annularOmegaCurve lower L positive mode)
      (radialOrdinary 1 lower positive
        (physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength slot field mode)) =
      collarScalar 1 lower (physicalRawFactor parameters lower L positive mode slot)
        (radialOrdinary 1 lower positive (field mode)) := by
  rw [physicalOmegaOperator, annularScalarFamily_ordinary, physicalOmegaFactor_cancel]

/-- Omega times the normalized derivative is exactly the already-forced ordinary derivative of X. -/
theorem physicalOmegaSlope_ordinary (field : DivisionRow 3 lower) (mode : HighAnnularMode) :
    collarScalar 1 lower (annularOmegaCurve lower L positive mode)
      (radialOrdinary 1 lower positive
        (physicalOmegaSlope parameters lower L positive lengthPositive widthHalf widthLength field mode)) =
      physicalFluxOrdinarySlope parameters lower L positive field mode := by
  change collarScalar 1 lower (annularOmegaCurve lower L positive mode)
    (radialOrdinary 1 lower positive
      (physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 0 (highPhysicalOutput lower 0 field) mode -
       physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 1 (highPhysicalOutput lower 0 field) mode -
       Complex.I • physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 2 (highPhysicalOutput lower 1 field) mode -
       Complex.I • physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 3 (highPhysicalOutput lower 2 field) mode)) = _
  simp only [map_sub, map_smul]
  rw [physicalOmegaOperator_ordinary, physicalOmegaOperator_ordinary,
    physicalOmegaOperator_ordinary, physicalOmegaOperator_ordinary, physicalFluxOrdinarySlope_literal]
  change collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) -
    collarScalar 1 lower (highReciprocalRadius lower positive)
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) -
    Complex.I • collarScalar 1 lower (ContinuousMap.const ℝ ((mode.val.2 : ℝ) / L))
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 1 field mode)) -
    Complex.I • collarScalar 1 lower ((mode.val.1 : ℝ) • highReciprocalRadius lower positive)
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 field mode)) = _
  rw [collarScalar_const, collarScalar_real_multiple]
  have cell : Complex.I • (((mode.val.2 : ℝ) / L) • radialOrdinary 1 lower positive (highPhysicalOutput lower 1 field mode)) =
      (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) • radialOrdinary 1 lower positive (highPhysicalOutput lower 1 field mode) := by
    change Complex.I • (((((mode.val.2 : ℝ) / L) : ℝ) : ℂ) • radialOrdinary 1 lower positive (highPhysicalOutput lower 1 field mode)) = _
    rw [smul_smul]
  have angular : Complex.I • ((mode.val.1 : ℝ) • collarScalar 1 lower (highReciprocalRadius lower positive)
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 field mode))) =
      (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 field mode)) := by
    change Complex.I • ((mode.val.1 : ℂ) • collarScalar 1 lower (highReciprocalRadius lower positive)
      (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 field mode))) = _
    rw [smul_smul]
  rw [cell, angular]

end Grad.AnnularCurrentGreen
