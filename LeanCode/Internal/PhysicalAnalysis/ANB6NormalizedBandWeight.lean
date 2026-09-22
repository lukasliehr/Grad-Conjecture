import ANB5OriginalScalarGain
import RadialWeightedDerivative

noncomputable section
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def InCellBand (length scale ceiling : ℝ) (cell : ℤ) : Prop := |(cell : ℝ) * scale / length| ≤ ceiling

def bandFrequencySize (ceiling : ℝ) : ℝ := Real.sqrt (1 + ceiling ^ 2)

def bandPhaseSize (length ceiling : ℝ) : ℝ := max 1 length * bandFrequencySize ceiling

theorem bandFrequencySize_one_le (ceiling : ℝ) : 1 ≤ bandFrequencySize ceiling := by
  have base : (1 : ℝ) ≤ 1 + ceiling ^ 2 := by nlinarith [sq_nonneg ceiling]
  simpa only [bandFrequencySize, Real.sqrt_one] using Real.sqrt_le_sqrt base

theorem bandPhaseSize_nonnegative (length ceiling : ℝ) : 0 ≤ bandPhaseSize length ceiling :=
  mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.sqrt_nonneg _)

theorem band_scaled_frequency (length scale ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) :
    scaledCellWeight length scale cell ≤ bandFrequencySize ceiling := by
  have square := pow_le_pow_left₀ (abs_nonneg ((cell : ℝ) * scale / length)) band 2
  rw [sq_abs] at square
  exact Real.sqrt_le_sqrt (add_le_add le_rfl square)

theorem band_original_frequency {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) :
    scale * Grad.CellWeights.cellWeight cell ≤ bandPhaseSize length ceiling :=
  (originalWidth_le_scaled length scale cell admissible.1 (admissible_ell_nonnegative admissible)
    (admissible_ell_le_one admissible)).trans
      (mul_le_mul_of_nonneg_left (band_scaled_frequency length scale ceiling cell band) (zero_le_one.trans (le_max_left _ _)))

def normalizedBandWeight (gamma scale : ℝ) (cell : ℤ) : SpatialPlane → ℝ := physicalWeight 0 gamma scale cell

def inverseBandWeight (gamma scale : ℝ) (cell : ℤ) : SpatialPlane → ℝ := inverseWeight 0 gamma scale cell

theorem normalizedBandWeight_smooth (gamma scale : ℝ) (cell : ℤ) : ContDiff ℝ ∞ (normalizedBandWeight gamma scale cell) :=
  (smoothGoal 0 gamma scale cell).2.1

theorem inverseBandWeight_smooth (gamma scale : ℝ) (cell : ℤ) : ContDiff ℝ ∞ (inverseBandWeight gamma scale cell) :=
  (smoothGoal 0 gamma scale cell).2.2

theorem normalizedBandWeight_formula (gamma scale : ℝ) (cell : ℤ) (point : SpatialPlane) :
    normalizedBandWeight gamma scale cell point =
      Real.exp (-gamma * (Real.sqrt (radicand scale cell point) - 1)) := by
  rw [normalizedBandWeight, physicalWeight_exp, physicalPhase_formula]
  simp only [zero_mul, zero_sub, neg_mul]

theorem originalWeight_normalized (sigma gamma scale : ℝ) (cell : ℤ) (point : SpatialPlane) :
    physicalWeight sigma gamma scale cell point =
      Real.exp (sigma * Grad.CellWeights.cellWeight cell) * normalizedBandWeight gamma scale cell point := by
  rw [physicalWeight_exp, physicalPhase_formula, normalizedBandWeight_formula, ← Real.exp_add]
  congr 1
  ring

theorem normalizedBandWeight_inverse (gamma scale : ℝ) (cell : ℤ) (point : SpatialPlane) :
    normalizedBandWeight gamma scale cell point * inverseBandWeight gamma scale cell point = 1 :=
  (formulaGoal 0 gamma scale cell point).2.2.2.2

def bandWeightCeiling (length gamma ceiling : ℝ) : ℝ := Real.exp (gamma * bandPhaseSize length ceiling)

theorem bandWeightCeiling_one_le (length gamma ceiling : ℝ) (nonnegative : 0 ≤ gamma) :
    1 ≤ bandWeightCeiling length gamma ceiling := Real.one_le_exp (mul_nonneg nonnegative (bandPhaseSize_nonnegative _ _))

theorem normalizedPhase_nonpositive (gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (cell : ℤ) (point : SpatialPlane) :
    physicalPhase 0 gamma scale cell point ≤ 0 := by
  have root : 1 ≤ Real.sqrt (radicand scale cell point) := by
    apply (Real.le_sqrt (by norm_num) (le_of_lt (radicand_pos scale cell point))).2
    unfold radicand
    nlinarith [sq_nonneg scale, sq_nonneg ‖point‖, sq_nonneg (Grad.CellWeights.cellWeight cell),
      mul_nonneg (mul_nonneg (sq_nonneg scale) (sq_nonneg ‖point‖)) (sq_nonneg (Grad.CellWeights.cellWeight cell))]
  rw [physicalPhase_formula]
  simp only [zero_mul, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg nonnegative (sub_nonneg.mpr root))

theorem inverseBandWeight_le {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (point : ClosedDisk) :
    inverseBandWeight gamma scale cell point.val ≤ bandWeightCeiling length gamma ceiling := by
  have frequency := band_original_frequency admissible ceiling cell band
  have frequencyNonnegative := mul_nonneg (admissible_ell_nonnegative admissible) (Grad.CellWeights.cellWeight_pos cell).le
  have square := pow_le_pow_left₀ frequencyNonnegative frequency 2
  have radius : ‖point.val‖ ^ 2 ≤ 1 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) point.property 2).trans_eq (by norm_num)
  have sizeNonnegative := bandPhaseSize_nonnegative length ceiling
  have radicandBound : radicand scale cell point.val ≤ (1 + bandPhaseSize length ceiling) ^ 2 := by
    have boundedProduct := mul_le_mul_of_nonneg_left radius (sq_nonneg (scale * Grad.CellWeights.cellWeight cell))
    unfold radicand
    nlinarith [boundedProduct]
  have root : Real.sqrt (radicand scale cell point.val) ≤ 1 + bandPhaseSize length ceiling :=
    Real.sqrt_le_iff.mpr ⟨by positivity, radicandBound⟩
  rw [inverseBandWeight, inverseWeight_exp]
  change Real.exp (-physicalPhase 0 gamma scale cell point.val) ≤ Real.exp (gamma * bandPhaseSize length ceiling)
  apply Real.exp_le_exp.mpr
  rw [physicalPhase_formula]
  simp only [zero_mul, zero_sub, neg_neg]
  exact mul_le_mul_of_nonneg_left (by linarith) (admissible_gamma_nonnegative admissible)

theorem normalizedBandWeight_le {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (point : SpatialPlane) :
    normalizedBandWeight gamma scale cell point ≤ bandWeightCeiling length gamma ceiling := by
  have first : normalizedBandWeight gamma scale cell point ≤ 1 :=
    Real.exp_le_one_iff.mpr (normalizedPhase_nonpositive gamma scale (admissible_gamma_nonnegative admissible) cell point)
  exact first.trans (bandWeightCeiling_one_le length gamma ceiling (admissible_gamma_nonnegative admissible))

end Grad.BoundedScalarInverse
