import ADY8OriginalLowCarrierConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

/-- Literal mu' and mu'/mu from BE3. -/
def lowMuSlope (length radius : ℝ) (cell : ℤ) : ℝ :=
  -(radius⁻¹ ^ 3) / lowMu length radius cell

def lowMuLogSlope (length radius : ℝ) (cell : ℤ) : ℝ :=
  -(radius⁻¹ ^ 3) / lowMu length radius cell ^ 2

theorem lowMu_hasDerivAt (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    HasDerivAt (fun point => lowMu length point cell) (lowMuSlope length radius cell) radius := by
  have inverse := (hasDerivAt_id radius).inv positive.ne'
  have polynomial := (inverse.pow 2).const_add (((cell : ℝ) / length) ^ 2)
  have strictlyPositive : 0 < ((cell : ℝ) / length) ^ 2 + radius⁻¹ ^ 2 := by positivity
  have root := polynomial.sqrt strictlyPositive.ne'
  convert root using 1 <;> dsimp [lowMuSlope, lowMu]
  field_simp

theorem lowMuSlope_div (length radius : ℝ) (cell : ℤ) :
    lowMuSlope length radius cell / lowMu length radius cell = lowMuLogSlope length radius cell := by
  unfold lowMuSlope lowMuLogSlope
  ring

theorem lowMuLogSlope_nonpos (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    lowMuLogSlope length radius cell ≤ 0 := by
  unfold lowMuLogSlope
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)

theorem lowMuLogSlope_abs_bound (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    |lowMuLogSlope length radius cell| ≤ radius⁻¹ := by
  have square := lowMu_sq length radius cell
  have inverseNonnegative : 0 ≤ radius⁻¹ := inv_nonneg.mpr positive.le
  have muPositive := lowMu_pos length radius cell positive
  rw [abs_of_nonpos (lowMuLogSlope_nonpos length radius cell positive)]
  unfold lowMuLogSlope
  rw [neg_div, neg_neg]
  apply (div_le_iff₀ (sq_pos_of_pos muPositive)).mpr
  nlinarith [mul_nonneg inverseNonnegative (sq_nonneg ((cell : ℝ) / length))]

theorem lowMuInverse_hasDerivAt (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    HasDerivAt (fun point => (lowMu length point cell)⁻¹)
      (-(lowMuLogSlope length radius cell) / lowMu length radius cell) radius := by
  have derivative := (lowMu_hasDerivAt length radius cell positive).inv (lowMu_pos length radius cell positive).ne'
  have equality : -(lowMuLogSlope length radius cell) / lowMu length radius cell =
      -(lowMuSlope length radius cell) / lowMu length radius cell ^ 2 := by
    unfold lowMuLogSlope lowMuSlope
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [equality]
  exact derivative

/-- The reference radial diagonal is controlled by mu even at n=0. -/
theorem lowMuLogSlope_normalized_bound (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    |lowMuLogSlope length radius cell| / lowMu length radius cell ≤ 1 := by
  exact (div_le_one (lowMu_pos length radius cell positive)).mpr
    ((lowMuLogSlope_abs_bound length radius cell positive).trans (lowMu_radial length radius cell positive))

end Grad.AnnularLowReference
