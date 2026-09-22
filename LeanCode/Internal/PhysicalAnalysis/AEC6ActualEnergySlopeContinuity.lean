import AEC5ActualLowReferenceCauchySolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lowPairEnergySlope_continuousAt (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius)
    (first second forcingFirst forcingSecond : ℝ → E)
    (firstContinuous : ContinuousAt first radius) (secondContinuous : ContinuousAt second radius)
    (forceFirstContinuous : ContinuousAt forcingFirst radius) (forceSecondContinuous : ContinuousAt forcingSecond radius) :
    ContinuousAt (fun point => lowPairEnergySlope parameters length point mode
      (first point) (second point) (forcingFirst point) (forcingSecond point)) radius := by
  have muContinuous := (lowMu_hasDerivAt length radius mode.val.2 positive).continuousAt
  have muNonzero := (lowMu_pos length radius mode.val.2 positive).ne'
  have logContinuous : ContinuousAt (fun point => lowMuLogSlope length point mode.val.2) radius :=
    ((continuousAt_id.inv₀ positive.ne').pow 3).neg.div (muContinuous.pow 2) (pow_ne_zero 2 muNonzero)
  have densityContinuous := (lowEnergyDensity_hasDerivAt length radius mode.val.2 positive).continuousAt
  have firstRow := ((lowReferenceEntry_continuousAt parameters length radius mode positive 0 0).smul firstContinuous).add
    ((lowReferenceEntry_continuousAt parameters length radius mode positive 0 1).smul secondContinuous)
  have secondRow := ((lowReferenceEntry_continuousAt parameters length radius mode positive 1 0).smul firstContinuous).add
    ((lowReferenceEntry_continuousAt parameters length radius mode positive 1 1).smul secondContinuous)
  simp only [lowPairEnergySlope, lowReferenceFirst_matrix, lowReferenceSecond_matrix]
  exact densityContinuous.mul
    (((((continuousAt_const.div continuousAt_id positive.ne').sub logContinuous).mul
      ((firstContinuous.norm.pow 2).add (secondContinuous.norm.pow 2))).add
        (continuousAt_const.mul (firstContinuous.inner (firstRow.add (muContinuous.smul forceFirstContinuous))))).add
      (continuousAt_const.mul (secondContinuous.inner (secondRow.add (muContinuous.smul forceSecondContinuous)))))

omit [InnerProductSpace ℝ E] in
theorem lowWeightedSquare_continuousAt (radius : ℝ) (positive : 0 < radius)
    (first second : ℝ → E) (firstContinuous : ContinuousAt first radius) (secondContinuous : ContinuousAt second radius) :
    ContinuousAt (fun point => point ^ (-(7 / 2 : ℝ)) * (‖first point‖ ^ 2 + ‖second point‖ ^ 2)) radius :=
  (Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ)) (Or.inl positive.ne')).continuousAt.mul
    ((firstContinuous.norm.pow 2).add (secondContinuous.norm.pow 2))

end Hilbert
end Grad.AnnularLowVolterra
