import AEE9ActualSmoothReferenceResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem row_residual_cancel {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mu a b : ℝ) (nonzero : mu ≠ 0) (first second slope : E) :
    a • first + b • second + mu • (mu⁻¹ • slope - ((a / mu) • first + (b / mu) • second)) = slope := by
  have firstCancel : mu * (a / mu) = a := by field_simp
  have secondCancel : mu * (b / mu) = b := by field_simp
  rw [smul_sub, smul_smul, mul_inv_cancel₀ nonzero, one_smul, smul_add,
    smul_smul, smul_smul, firstCancel, secondCancel]
  abel

theorem lowCore_reference_row (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) (radius : ℝ) (inside : lower ≤ radius) :
    HasDerivAt (core index).val.val.1
      (lowReferenceMatrix parameters length radius index.2 index.1 0 • (core (0, index.2)).val.val.1 radius +
        lowReferenceMatrix parameters length radius index.2 index.1 1 • (core (1, index.2)).val.val.1 radius +
        lowMu length radius index.2.val.2 • lowCoreResidualCurve parameters length lower positive core index radius) radius := by
  rw [lowCoreResidualCurve_actual parameters length lower positive core index radius inside,
    row_residual_cancel _ _ _ (lowMu_pos length radius index.2.val.2 (positive.trans_le inside)).ne']
  exact (core index).val.property radius

theorem lowCore_reference_first (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    HasDerivAt (core (0, mode)).val.val.1
      (lowReferenceFirst parameters length radius mode ((core (0, mode)).val.val.1 radius)
        ((core (1, mode)).val.val.1 radius) +
        lowMu length radius mode.val.2 • lowCoreResidualCurve parameters length lower positive core (0, mode) radius) radius := by
  rw [lowReferenceFirst_matrix]
  exact lowCore_reference_row parameters length lower positive core (0, mode) radius inside

theorem lowCore_reference_second (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    HasDerivAt (core (1, mode)).val.val.1
      (lowReferenceSecond parameters length radius mode ((core (0, mode)).val.val.1 radius)
        ((core (1, mode)).val.val.1 radius) +
        lowMu length radius mode.val.2 • lowCoreResidualCurve parameters length lower positive core (1, mode) radius) radius := by
  rw [lowReferenceSecond_matrix]
  exact lowCore_reference_row parameters length lower positive core (1, mode) radius inside

end Grad.AnnularLowCompletion
