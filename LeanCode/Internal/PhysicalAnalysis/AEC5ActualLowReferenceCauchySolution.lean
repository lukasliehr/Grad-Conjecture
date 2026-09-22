import AEC4ActualReferenceCoefficientContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

def lowReferencePairSource (length lower upper : ℝ) (mode : LowAnnularMode)
    (positive : 0 < lower) (forcing : C(Icc lower upper, LowReferencePair)) :
    C(Icc lower upper, LowReferencePair) where
  toFun point := lowMu length point.val mode.val.2 • forcing point
  continuous_toFun := continuous_iff_continuousAt.mpr (fun point =>
    (((lowMu_hasDerivAt length point.val mode.val.2 (positive.trans_le point.property.1)).continuousAt.comp
      continuous_subtype_val.continuousAt).smul forcing.continuous.continuousAt))

/-- The global reference Cauchy problem is solved for each original low mode
and each axial cell. The actual BE10 matrix and actual mu-normalized source
are inserted into the constructive Volterra theorem. -/
theorem lowReferenceModeCauchy_exists (parameters : PhaseParameters) (length lower upper : ℝ)
    (mode : LowAnnularMode) (positive : 0 < lower) (ordered : lower ≤ upper)
    (forcing : C(Icc lower upper, LowReferencePair)) (initial : LowReferencePair) :
    ∃ first second : ℝ → ℂ, first lower = initial 0 ∧ second lower = initial 1 ∧
      ∀ point : Icc lower upper,
        HasDerivAt first (lowReferenceFirst parameters length point.val mode (first point.val) (second point.val) +
          lowMu length point.val mode.val.2 • forcing point 0) point.val ∧
        HasDerivAt second (lowReferenceSecond parameters length point.val mode (first point.val) (second point.val) +
          lowMu length point.val mode.val.2 • forcing point 1) point.val := by
  let coefficient := lowReferencePairCoefficient parameters length lower upper mode positive
  let source := lowReferencePairSource length lower upper mode positive forcing
  obtain ⟨solution, initialValue, derivative⟩ := globalLinearCauchy_exists lower upper ordered
    coefficient source initial ‖coefficient‖₊ (fun point => coefficient.norm_coe_le_norm point)
  refine ⟨fun point => solution point 0, fun point => solution point 1,
    congrArg (fun field : LowReferencePair => field 0) initialValue,
    congrArg (fun field : LowReferencePair => field 1) initialValue, ?_⟩
  intro point
  have first := hasDerivAt_pi.mp (derivative point) 0
  have second := hasDerivAt_pi.mp (derivative point) 1
  change HasDerivAt (fun radius => solution radius 0)
    (lowReferencePairOperator parameters length point.val mode (solution point.val) 0 +
      lowMu length point.val mode.val.2 • forcing point 0) point.val at first
  change HasDerivAt (fun radius => solution radius 1)
    (lowReferencePairOperator parameters length point.val mode (solution point.val) 1 +
      lowMu length point.val mode.val.2 • forcing point 1) point.val at second
  rw [lowReferencePairOperator_apply, ← lowReferenceFirst_matrix] at first
  rw [lowReferencePairOperator_apply, ← lowReferenceSecond_matrix] at second
  exact ⟨first, second⟩

end Grad.AnnularLowVolterra
