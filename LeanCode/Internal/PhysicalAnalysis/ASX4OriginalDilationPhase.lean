import ASX3SpinUniqueness
import RadialWeightedDerivative

noncomputable section
open scoped BigOperators ContDiff
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope

/-- The defect of the unchanged original AP phase under literal disk dilation. -/
def originalDilationDefect (sigma gamma ell : ℝ) (cell : ℤ) (scale : ℝ) (point : SpatialPlane) : ℝ :=
  physicalPhase sigma gamma ell cell point - physicalPhase sigma gamma ell cell (scale • point)

def originalDilationMultiplier (sigma gamma ell : ℝ) (cell : ℤ) (scale : ℝ) (point : SpatialPlane) : ℝ :=
  Real.exp (originalDilationDefect sigma gamma ell cell scale point)

theorem originalDilationDefect_smooth (sigma gamma ell : ℝ) (cell : ℤ) (scale : ℝ) :
    ContDiff ℝ ∞ (originalDilationDefect sigma gamma ell cell scale) :=
  (physicalPhase_contDiff sigma gamma ell cell).sub
    ((physicalPhase_contDiff sigma gamma ell cell).comp (dilationLinear scale).contDiff)

theorem originalDilationMultiplier_smooth (sigma gamma ell : ℝ) (cell : ℤ) (scale : ℝ) :
    ContDiff ℝ ∞ (originalDilationMultiplier sigma gamma ell cell scale) :=
  (originalDilationDefect_smooth sigma gamma ell cell scale).exp

theorem originalDilationDefect_nonpositive {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (point : SpatialPlane) :
    originalDilationDefect sigma gamma ell cell scale point ≤ 0 := by
  have radius : ‖scale • point‖ ≤ ‖point‖ := by
    rw [norm_smul, Real.norm_of_nonneg nonnegative]
    exact mul_le_of_le_one_left (norm_nonneg point) bounded
  have square := pow_le_pow_left₀ (norm_nonneg (scale • point)) radius 2
  have radicandBound : radicand ell cell (scale • point) ≤ radicand ell cell point := by
    unfold radicand
    nlinarith [sq_nonneg ell, sq_nonneg (Grad.CellWeights.cellWeight cell),
      mul_nonneg (sq_nonneg ell) (sq_nonneg (Grad.CellWeights.cellWeight cell))]
  have root := Real.sqrt_le_sqrt radicandBound
  unfold originalDilationDefect
  rw [physicalPhase_formula, physicalPhase_formula]
  nlinarith [admissible_gamma_nonnegative admissible]

theorem originalDilationMultiplier_le_one {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (point : SpatialPlane) :
    originalDilationMultiplier sigma gamma ell cell scale point ≤ 1 :=
  Real.exp_le_one_iff.mpr (originalDilationDefect_nonpositive admissible cell nonnegative bounded point)

def originalPhaseConstant (L gamma : ℝ) (order : ℕ) : ℝ :=
  profileConstant order * gamma * (max 1 L) ^ order

theorem originalPhaseConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (order : ℕ) : 0 ≤ originalPhaseConstant L gamma order := by
  unfold originalPhaseConstant
  exact mul_nonneg (mul_nonneg (profileConstant_nonnegative _) (admissible_gamma_nonnegative admissible))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

theorem originalPhase_scaled_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) (order : ℕ) (positive : 1 ≤ order) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (physicalPhase sigma gamma ell cell) point‖ ≤
      originalPhaseConstant L gamma order * scaledCellWeight L ell cell ^ order := by
  have frequency := originalWidth_le_scaled L ell cell admissible.1
    (admissible_ell_nonnegative admissible) (admissible_ell_le_one admissible)
  calc
    _ ≤ profileConstant order * gamma * ell ^ order * Grad.CellWeights.cellWeight cell ^ order :=
      physicalPhase_iterated_norm_bound sigma gamma ell cell (admissible_gamma_nonnegative admissible)
        (admissible_ell_nonnegative admissible) order positive point
    _ = (profileConstant order * gamma) * (ell * Grad.CellWeights.cellWeight cell) ^ order := by ring
    _ ≤ (profileConstant order * gamma) * (max 1 L * scaledCellWeight L ell cell) ^ order :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (admissible_ell_nonnegative admissible)
        (Grad.CellWeights.cellWeight_pos cell).le) frequency _) (mul_nonneg (profileConstant_nonnegative _)
          (admissible_gamma_nonnegative admissible))
    _ = _ := by unfold originalPhaseConstant; rw [mul_pow]; ring

theorem originalDilationDefect_iterated_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (order : ℕ) (positive : 1 ≤ order) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (originalDilationDefect sigma gamma ell cell scale) point‖ ≤
      (2 * originalPhaseConstant L gamma order) * scaledCellWeight L ell cell ^ order := by
  have smooth := physicalPhase_contDiff sigma gamma ell cell
  have dilatedSmooth := smooth.comp (dilationLinear scale).contDiff
  change ‖iteratedFDeriv ℝ order ((physicalPhase sigma gamma ell cell) -
    (physicalPhase sigma gamma ell cell) ∘ dilationLinear scale) point‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    (smooth.of_le (by exact_mod_cast le_top)).contDiffAt
    (dilatedSmooth.of_le (by exact_mod_cast le_top)).contDiffAt,
    (dilationLinear scale).iteratedFDeriv_comp_right smooth point (by exact_mod_cast le_top)]
  apply (norm_sub_le _ _).trans
  have composed := (iteratedFDeriv ℝ order (physicalPhase sigma gamma ell cell)
    (dilationLinear scale point)).norm_compContinuousLinearMap_le (fun _ => dilationLinear scale)
  have contraction : ∏ _ : Fin order, ‖dilationLinear scale‖ ≤ 1 := by
    simp only [dilationLinear_norm, abs_of_nonneg nonnegative, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ nonnegative bounded
  have second := composed.trans (mul_le_of_le_one_right (norm_nonneg _) contraction)
  have first := originalPhase_scaled_bound admissible cell order positive point
  have last := originalPhase_scaled_bound admissible cell order positive (dilationLinear scale point)
  linarith

def originalDilationConstant (L gamma : ℝ) (order : ℕ) : ℝ :=
  ∑ partition : OrderedFinpartition order, ∏ block, 2 * originalPhaseConstant L gamma (partition.partSize block)

theorem originalDilationConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (order : ℕ) : 0 ≤ originalDilationConstant L gamma order :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg
    (fun _ _ => mul_nonneg (by norm_num) (originalPhaseConstant_nonnegative admissible _)))

theorem originalDilationMultiplier_iterated_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (cell : ℤ) {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (order : ℕ) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (originalDilationMultiplier sigma gamma ell cell scale) point‖ ≤
      originalDilationConstant L gamma order * scaledCellWeight L ell cell ^ order := by
  change ‖iteratedFDeriv ℝ order (fun source => Real.exp (originalDilationDefect sigma gamma ell cell scale source)) point‖ ≤ _
  rw [exp_comp_expansion _ (originalDilationDefect_smooth sigma gamma ell cell scale)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ partition : OrderedFinpartition order,
        (∏ block, 2 * originalPhaseConstant L gamma (partition.partSize block)) * scaledCellWeight L ell cell ^ order := by
      apply Finset.sum_le_sum
      intro partition _
      apply (partition.norm_compAlongOrderedFinpartition_le _ _).trans
      rw [LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ 1 * ∏ block, (2 * originalPhaseConstant L gamma (partition.partSize block)) *
            scaledCellWeight L ell cell ^ partition.partSize block := by
          apply mul_le_mul
          · exact originalDilationMultiplier_le_one admissible cell nonnegative bounded point
          · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun block _ => originalDilationDefect_iterated_bound admissible cell nonnegative bounded
                (partition.partSize block) (partition.partSize_pos block) point)
          · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          · norm_num
        _ = _ := by
          rw [one_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, partition_size_sum]
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Grad.ActualExceptionalInverse
