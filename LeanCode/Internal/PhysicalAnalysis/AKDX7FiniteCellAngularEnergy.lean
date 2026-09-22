import AKDX6PolarWordFourier
import AKAB16AngularL1FromActualCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.AnnularIncomingIntegrability

/-- Parseval is summed over a finite axial support before the full Hilbert
norm is taken, so no infinite repetition of a global bound is introduced. -/
theorem finiteCell_angular_energy_bound {dimension : ℕ} (cells : Finset ℤ)
    (coefficients : CellL2 dimension) (field : ℤ→ℝ→ComplexEuclidean dimension)
    (continuousField : ∀ cell,Continuous (field cell))
    (dominated : ∀ cell mode,‖angularCoefficient (field cell) mode‖≤‖coefficients (mode,cell)‖) :
    (∑ cell∈cells,∫ angle in -Real.pi..Real.pi,‖field cell angle‖^2)≤(2*Real.pi)*‖coefficients‖^2 := by
  have summed := hasSum_sum (s:=cells) (fun cell _ => angular_hasSum_sq (field cell) (continuousField cell))
  have wholeSum := lp_summable_sq coefficients
  have normSum : ‖coefficients‖^2=∑' mode : ℤ×ℤ,‖coefficients mode‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p:=2) (by norm_num) coefficients)
  have finiteBound (modes : Finset ℤ) :
      (∑ mode∈modes,∑ cell∈cells,‖angularCoefficient (field cell) mode‖^2)≤‖coefficients‖^2 := by
    have estimate := wholeSum.sum_le_tsum (modes ×ˢ cells) (fun _ _ => sq_nonneg _)
    rw [Finset.sum_product] at estimate
    exact (Finset.sum_le_sum (fun mode _ => Finset.sum_le_sum (fun cell _ =>
      pow_le_pow_left₀ (norm_nonneg _) (dominated cell mode) 2))).trans (estimate.trans_eq normSum.symm)
  have bound : (∑ cell∈cells,(2*Real.pi)⁻¹*(∫ angle in -Real.pi..Real.pi,‖field cell angle‖^2))≤‖coefficients‖^2 :=
    le_of_tendsto summed (Eventually.of_forall finiteBound)
  rw [←Finset.mul_sum] at bound
  exact (inv_mul_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp bound

end Grad.OriginalCollarNorm
