import AID7UniformPhysicalOmegaBounds

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

/-- The four real output factors in the literal BF14 equation. -/
def physicalRawFactor (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (slot : Fin 4) : C(ℝ, ℝ) :=
  ![annularTiltCurve parameters lower positive mode.val.2,
    highReciprocalRadius lower positive,
    ContinuousMap.const ℝ ((mode.val.2 : ℝ) / L),
    (mode.val.1 : ℝ) • highReciprocalRadius lower positive] slot

def physicalOmegaFactor (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (slot : Fin 4) : C(ℝ, ℝ) :=
  ⟨fun radius => physicalRawFactor parameters lower L positive mode slot radius /
      annularOmegaCurve lower L positive mode radius,
    (physicalRawFactor parameters lower L positive mode slot).continuous.div
      (annularOmegaCurve lower L positive mode).continuous
      (fun radius => (annularOmegaCurve_pos lower L positive mode radius).ne')⟩

def physicalOmegaFactorBound (slot : Fin 4) : ℝ := ![1, 1 / 3, 1, 1] slot

theorem physicalOmegaFactorBound_nonnegative (slot : Fin 4) : 0 ≤ physicalOmegaFactorBound slot := by
  fin_cases slot <;> norm_num [physicalOmegaFactorBound]

theorem physicalOmegaFactor_bound (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (slot : Fin 4) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |physicalOmegaFactor parameters lower L positive mode slot radius| ≤ physicalOmegaFactorBound slot := by
  obtain ⟨phase, inverse, cell, angular⟩ := physicalOmega_factors parameters lower L positive lengthPositive widthHalf widthLength mode radius inside
  fin_cases slot
  · exact phase
  · exact inverse
  · exact cell
  · change |((mode.val.1 : ℝ) * (max lower radius)⁻¹) / annularOmegaCurve lower L positive mode radius| ≤ 1
    simpa only [div_eq_mul_inv] using angular

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

def physicalOmegaOperator (slot : Fin 4) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (fun mode => physicalOmegaFactor parameters lower L positive mode slot)
    (physicalOmegaFactorBound slot) (physicalOmegaFactorBound_nonnegative slot)
    (physicalOmegaFactor_bound parameters lower L positive lengthPositive widthHalf widthLength slot)

theorem physicalOmegaOperator_bound (slot : Fin 4) (field : AnnularBulk lower) :
    ‖physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength slot field‖ ≤
      physicalOmegaFactorBound slot * ‖field‖ :=
  annularScalarFamily_bound _ _ _ _ _ field

/-- The normalized radial derivative is constructed from the SAME three completed physical outputs. -/
def physicalOmegaSlope : DivisionRow 3 lower →L[ℂ] AnnularBulk lower :=
  (physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 0).comp (highPhysicalOutput lower 0) -
  (physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 1).comp (highPhysicalOutput lower 0) -
  Complex.I • (physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 2).comp (highPhysicalOutput lower 1) -
  Complex.I • (physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 3).comp (highPhysicalOutput lower 2)

theorem physicalOmegaSlope_bound (field : DivisionRow 3 lower) :
    ‖physicalOmegaSlope parameters lower L positive lengthPositive widthHalf widthLength field‖ ≤ (10 / 3 : ℝ) * ‖field‖ := by
  have bounds (slot : Fin 4) (coordinate : Fin 3) :=
    (physicalOmegaOperator_bound parameters lower L positive lengthPositive widthHalf widthLength slot
      (highPhysicalOutput lower coordinate field)).trans
      (mul_le_mul_of_nonneg_left (highPhysicalOutput_bound lower coordinate field) (physicalOmegaFactorBound_nonnegative slot))
  have first := bounds 0 0
  have second := bounds 1 0
  have third := bounds 2 1
  have fourth := bounds 3 2
  norm_num [physicalOmegaFactorBound] at first second third fourth
  change ‖physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 0 (highPhysicalOutput lower 0 field) -
    physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 1 (highPhysicalOutput lower 0 field) -
    Complex.I • physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 2 (highPhysicalOutput lower 1 field) -
    Complex.I • physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 3 (highPhysicalOutput lower 2 field)‖ ≤ _
  let a := physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 0 (highPhysicalOutput lower 0 field)
  let b := physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 1 (highPhysicalOutput lower 0 field)
  let c := physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 2 (highPhysicalOutput lower 1 field)
  let d := physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength 3 (highPhysicalOutput lower 2 field)
  have triangle : ‖a - b - Complex.I • c - Complex.I • d‖ ≤ ‖a‖ + ‖b‖ + ‖Complex.I • c‖ + ‖Complex.I • d‖ :=
    (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  simp only [norm_smul, Complex.norm_I, one_mul] at triangle
  change ‖a‖ ≤ _ at first
  change ‖b‖ ≤ _ at second
  change ‖c‖ ≤ 1 * ‖field‖ at third
  change ‖d‖ ≤ 1 * ‖field‖ at fourth
  change ‖a - b - Complex.I • c - Complex.I • d‖ ≤ _
  linarith

end Grad.AnnularCurrentGreen
