import AID2LiteralPhysicalPacketPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity

/-- Exact physical testing removes the stored sqrt(b) factor. -/
theorem physicalTestPacket_normalized_pairing (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (test : annularEnergySpace lower L positive) (field : DivisionRow 3 lower) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive test)) field =
      inner ℂ (annularEnergyDerivative lower L positive test +
        annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test)
        (highPhysicalOutput lower 0 field) +
      inner ℂ (highEnergyCell lower L positive test) (highPhysicalOutput lower 1 field) +
      inner ℂ (highEnergyAngularRadius lower L positive test) (highPhysicalOutput lower 2 field) := by
  have derivative : highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive test) = annularEnergyDerivative lower L positive test +
        annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test := by
    change annularEnergyDerivative lower L positive (bEnergyDecode lower L positive (bEnergyNormalize lower L positive test)) +
      annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength
        (bEnergyDecode lower L positive (bEnergyNormalize lower L positive test)) = _
    rw [bEnergyDecode_normalize]
  rw [physicalTestPacket_pairing, bEnergyDecode_normalize, derivative]

/-- Normalization preserves the actual zero inner trace. -/
theorem bEnergyNormalize_inner_zero (lower L : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < L) (test : annularEnergySpace lower L positive)
    (zero : annularEnergyTrace lower L positive bounded lengthPositive 0 test = 0) :
    annularEnergyTrace lower L positive bounded lengthPositive 0 (bEnergyNormalize lower L positive test) = 0 := by
  rw [bEnergyNormalize, annularEnergyTrace_diagonal, zero, map_zero]

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

theorem actualTiltPhase_single (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength
      (annularEnergyCoreInto lower L positive (Finsupp.single mode core)) =
    lp.single 2 mode (collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
      (weightedCurveComplex 1 lower core.val.1)) := by
  classical
  apply lp.ext
  funext index
  rw [annularTiltEnergyPhase_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, map_zero]

theorem actualCell_single (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    highEnergyCell lower L positive (annularEnergyCoreInto lower L positive (Finsupp.single mode core)) =
    lp.single 2 mode ((Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) • weightedCurveComplex 1 lower core.val.1) := by
  classical
  apply lp.ext
  funext index
  rw [highEnergyCell_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, smul_zero]

theorem actualAngularRadius_single (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    highEnergyAngularRadius lower L positive (annularEnergyCoreInto lower L positive (Finsupp.single mode core)) =
    lp.single 2 mode ((Complex.I * (mode.val.1 : ℂ)) •
      collarScalar 1 lower (highReciprocalRadius lower positive) (weightedCurveComplex 1 lower core.val.1)) := by
  classical
  apply lp.ext
  funext index
  rw [highEnergyAngularRadius_mode, highEnergyRadius_mode, annularEnergyValue_single]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, map_zero, smul_zero]

end Grad.AnnularCurrentGreen
