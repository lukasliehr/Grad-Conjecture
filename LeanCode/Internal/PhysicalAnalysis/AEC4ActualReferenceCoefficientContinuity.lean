import AEC3GlobalLinearCauchyExistence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

/-- Continuity is proved for the literal BE10 entries, not supplied as a
hypothesis about an unspecified matrix generator. -/
theorem lowReferenceEntry_continuousAt (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (row column : Fin 2) :
    ContinuousAt (fun point => lowReferenceMatrix parameters length point mode row column) radius := by
  have muContinuous := (lowMu_hasDerivAt length radius mode.val.2 positive).continuousAt
  have muNonzero := (lowMu_pos length radius mode.val.2 positive).ne'
  have inverseContinuous : ContinuousAt (fun point : ℝ => point⁻¹) radius :=
    continuousAt_id.inv₀ positive.ne'
  have logContinuous : ContinuousAt (fun point => lowMuLogSlope length point mode.val.2) radius :=
    (inverseContinuous.pow 3).neg.div (muContinuous.pow 2) (pow_ne_zero 2 muNonzero)
  have phaseContinuous := (annularPhaseSlope_continuous parameters mode.val.2).continuousAt (x := radius)
  have upperContinuous : ContinuousAt (fun point => lowReferenceUpper length point mode) radius := by
    by_cases center : |mode.val.1| = 1
    · simp only [lowReferenceUpper, if_pos center]
      exact continuousAt_const.mul muContinuous
    · simp only [lowReferenceUpper, if_neg center]
      exact continuousAt_const
  have lowerContinuous : ContinuousAt (fun point => lowReferenceLower length parameters.gamma point mode) radius := by
    by_cases center : |mode.val.1| = 1
    · simp only [lowReferenceLower, if_pos center]
      exact (continuousAt_const.mul muContinuous).neg
    · simp only [lowReferenceLower, if_neg center]
      have balancePositive : 0 < lowBalanceConstant length parameters.gamma := by
        unfold lowBalanceConstant
        exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      exact ((muContinuous.pow 2).add (continuousAt_const.mul (inverseContinuous.pow 2))).neg.div
        (continuousAt_const.mul muContinuous) (mul_ne_zero balancePositive.ne' muNonzero)
  fin_cases row <;> fin_cases column
  · exact (logContinuous.sub (continuousAt_const.div continuousAt_id positive.ne')).add phaseContinuous
  · exact upperContinuous
  · exact lowerContinuous
  · exact (continuousAt_const.div continuousAt_id positive.ne').add phaseContinuous

abbrev LowReferencePair := Fin 2 → ℂ

/-- Actual two-row coefficient as a real continuous linear map on the
finite-dimensional physical complex Fourier pair. -/
def lowReferencePairOperator (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) : LowReferencePair →L[ℝ] LowReferencePair :=
  ∑ row : Fin 2, ∑ column : Fin 2,
    lowReferenceMatrix parameters length radius mode row column •
      ((ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℂ) row).comp (ContinuousLinearMap.proj column))

theorem lowReferencePairOperator_apply (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (field : LowReferencePair) (row : Fin 2) :
    lowReferencePairOperator parameters length radius mode field row =
      lowReferenceMatrix parameters length radius mode row 0 • field 0 +
        lowReferenceMatrix parameters length radius mode row 1 • field 1 := by
  fin_cases row <;> simp [lowReferencePairOperator, Fin.sum_univ_two]

theorem lowReferencePairOperator_continuousAt (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) :
    ContinuousAt (fun point => lowReferencePairOperator parameters length point mode) radius := by
  simp only [lowReferencePairOperator, Fin.sum_univ_two]
  exact (((lowReferenceEntry_continuousAt parameters length radius mode positive 0 0).smul continuousAt_const).add
    ((lowReferenceEntry_continuousAt parameters length radius mode positive 0 1).smul continuousAt_const)).add
    (((lowReferenceEntry_continuousAt parameters length radius mode positive 1 0).smul continuousAt_const).add
      ((lowReferenceEntry_continuousAt parameters length radius mode positive 1 1).smul continuousAt_const))

def lowReferencePairCoefficient (parameters : PhaseParameters) (length lower upper : ℝ)
    (mode : LowAnnularMode) (positive : 0 < lower) :
    C(Icc lower upper, LowReferencePair →L[ℝ] LowReferencePair) where
  toFun point := lowReferencePairOperator parameters length point.val mode
  continuous_toFun := continuous_iff_continuousAt.mpr (fun point =>
    (lowReferencePairOperator_continuousAt parameters length point.val mode
      (positive.trans_le point.property.1)).comp continuous_subtype_val.continuousAt)

end Grad.AnnularLowVolterra
