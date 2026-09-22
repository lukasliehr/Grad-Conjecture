import AKDP69ActualEndpointLowerGraphTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.BoundaryTrace
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization

/-- The actual natural cell endpoint is a stored zero spatial coordinate
of the original mixed norm. -/
theorem startupOriginalCellNorm_le_full {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (core : ACore parameters dimension) :
    originalCellNorm parameters grade core≤originalGradeNorm grade core := by
  rw [←startupOriginalNaturalMomentLinear_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (originalGradeNorm_nonnegative grade core)).mp
  rw [Grad.CellEnergy.field_norm_sq_eq_tsum,originalGradeNorm,originalGrade_norm_sq_eq_rows]
  have coordinate (cell : ℤ) :
      ‖fieldCellProjection dimension openUnitDisk cell (startupOriginalNaturalMomentLinear parameters grade core)‖≤
        ‖rawCartesianGradeCoordinates parameters grade core.val cell‖ := by
    change ‖fieldCellProjection dimension openUnitDisk cell (originalSourceJointField parameters core grade)‖≤_
    rw [startupOriginalJoint_projection]
    exact PiLp.norm_apply_le (rawCartesianGradeCoordinates parameters grade core.val cell) (zeroGradeIndex grade)
  exact (Grad.CellEnergy.cellEnergy_summable dimension openUnitDisk (startupOriginalNaturalMomentLinear parameters grade core)).tsum_le_tsum
    (fun cell => pow_le_pow_left₀ (norm_nonneg _) (coordinate cell) 2) (original_rows_summable parameters core)

namespace StartupAdjustableSpatialGraph
variable {State : Type*} {order : ℕ} {field : State → StartupL2 3} {high low larger : State → ℝ}

theorem enlargeLow (estimate : StartupAdjustableSpatialGraph order field high low)
    (bound : ∀ state,low state≤larger state) : StartupAdjustableSpatialGraph order field high larger := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := estimate epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  obtain ⟨graph,same,paid⟩ := bounded state
  exact ⟨graph,same,paid.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (bound state) nonnegative))⟩

/-- Known source terms use their own original norm. Turning a source
phase bound into the common remainder does not multiply two unknown or
high coefficient norms. -/
theorem sourcePaid (parameters : PhaseParameters) (grade : ℕ) (cores : State → ACore parameters 3)
    (estimate : StartupAdjustableSpatialGraph order field (fun state => originalGradeNorm grade (cores state))
      (fun state => originalCellNorm parameters grade (cores state)))
    (highNonnegative : ∀ state,0≤high state) (payment : ∀ state,originalGradeNorm grade (cores state)≤low state) :
    StartupAdjustableSpatialGraph order field high low := by
  obtain ⟨constant,nonnegative,bounded⟩ := estimate 1 zero_lt_one
  intro epsilon positive
  refine ⟨1+constant,add_nonneg zero_le_one nonnegative,?_⟩
  intro state
  obtain ⟨graph,same,paid⟩ := bounded state
  refine ⟨graph,same,?_⟩
  have cellPaid := mul_le_mul_of_nonneg_left ((startupOriginalCellNorm_le_full parameters grade (cores state)).trans (payment state)) nonnegative
  have first := payment state
  have highPaid := mul_nonneg positive.le (highNonnegative state)
  nlinarith only [paid,cellPaid,first,highPaid]

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup
