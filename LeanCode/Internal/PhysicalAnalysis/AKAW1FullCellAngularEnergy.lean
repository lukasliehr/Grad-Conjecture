import AKAV6SameLiteralG3PointwiseConsumer
import AKAA14OriginalFixedOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.SourceCollarCoefficients Grad.BoundaryTrace Grad.AnnularIncomingIntegrability

/-- Parseval summed over a finite set of axial cells, with one bound from the
actual joint angular/cell Hilbert vector. No cell-count factor is introduced. -/
theorem finiteCell_angular_energy {dimension : ℕ}
    (coefficients : CellL2 dimension) (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell))
    (coefficientBound : ∀ mode cell, ‖angularCoefficient (field cell) mode‖ ≤ ‖coefficients (mode,cell)‖)
    (cells : Finset ℤ) :
    (∫ angle in -Real.pi..Real.pi, ∑ cell ∈ cells, ‖field cell angle‖ ^ 2) ≤
      (2 * Real.pi) * ‖coefficients‖ ^ 2 := by
  have summation := tendsto_finsetSum cells (fun cell _ => angular_hasSum_sq (field cell) (continuousField cell))
  have wholeSum := lp_summable_sq coefficients
  have normSum : ‖coefficients‖ ^ 2 = ∑' mode : ℤ × ℤ, ‖coefficients mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) coefficients)
  have finiteBound (support : Finset ℤ) :
      (∑ cell ∈ cells, ∑ mode ∈ support, ‖angularCoefficient (field cell) mode‖ ^ 2) ≤ ‖coefficients‖ ^ 2 := by
    calc
      _ ≤ ∑ cell ∈ cells, ∑ mode ∈ support, ‖coefficients (mode,cell)‖ ^ 2 :=
        Finset.sum_le_sum (fun cell _ => Finset.sum_le_sum (fun mode _ =>
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (coefficientBound mode cell)))
      _ = ∑ mode ∈ support ×ˢ cells, ‖coefficients mode‖ ^ 2 := by
        rw [Finset.sum_product,Finset.sum_comm]
      _ ≤ _ := (wholeSum.sum_le_tsum _ (fun _ _ => sq_nonneg _)).trans_eq normSum.symm
  have bound := le_of_tendsto summation (Eventually.of_forall finiteBound)
  have integrable (cell : ℤ) : IntervalIntegrable (fun angle => ‖field cell angle‖ ^ 2) volume (-Real.pi) Real.pi :=
    ((continuousField cell).norm.pow 2).intervalIntegrable _ _
  rw [← Finset.mul_sum,← intervalIntegral.integral_finsetSum (fun cell _ => integrable cell)] at bound
  exact (inv_mul_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp bound

end Grad.ActualNativeCellMoments
