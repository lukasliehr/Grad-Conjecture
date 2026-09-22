import RadialDilationJet

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.AnalyticWeights.Higher

def dilationPhaseDefect (parameters : PhaseParameters) (cell : ℤ) (scale : ℝ)
    (point : SpatialPlane) : ℝ :=
  cartesianPhase parameters cell point - cartesianPhase parameters cell (scale • point)

def dilationMultiplier (parameters : PhaseParameters) (cell : ℤ) (scale : ℝ)
    (point : SpatialPlane) : ℝ := Real.exp (dilationPhaseDefect parameters cell scale point)

theorem dilationPhaseDefect_smooth (parameters : PhaseParameters) (cell : ℤ) (scale : ℝ) :
    ContDiff ℝ ∞ (dilationPhaseDefect parameters cell scale) :=
  (cartesianPhase_contDiff parameters cell).sub
    ((cartesianPhase_contDiff parameters cell).comp (dilationLinear scale).contDiff)

theorem dilationMultiplier_smooth (parameters : PhaseParameters) (cell : ℤ) (scale : ℝ) :
    ContDiff ℝ ∞ (dilationMultiplier parameters cell scale) :=
  (dilationPhaseDefect_smooth parameters cell scale).exp

theorem dilationPhaseDefect_nonpositive (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (point : SpatialPlane) :
    dilationPhaseDefect parameters cell scale point ≤ 0 := by
  have radius : ‖scale • point‖ ≤ ‖point‖ := by
    rw [norm_smul, Real.norm_of_nonneg nonnegative]
    exact mul_le_of_le_one_left (norm_nonneg point) bounded
  have square := pow_le_pow_left₀ (norm_nonneg (scale • point)) radius 2
  have root : Real.sqrt (1 + cellFrequency cell ^ 2 * ‖scale • point‖ ^ 2) ≤
      Real.sqrt (1 + cellFrequency cell ^ 2 * ‖point‖ ^ 2) := by
    apply Real.sqrt_le_sqrt
    exact add_le_add_right (mul_le_mul_of_nonneg_left square (sq_nonneg (cellFrequency cell))) 1
  unfold dilationPhaseDefect
  rw [cartesianPhase_formula, cartesianPhase_formula]
  nlinarith [parameters.gamma_pos]

theorem dilationMultiplier_le_one (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (point : SpatialPlane) :
    dilationMultiplier parameters cell scale point ≤ 1 :=
  Real.exp_le_one_iff.mpr (dilationPhaseDefect_nonpositive parameters cell nonnegative bounded point)

theorem dilationPhaseDefect_iterated_bound (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (order : ℕ) (positive : 1 ≤ order) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (dilationPhaseDefect parameters cell scale) point‖ ≤
      (2 * profileConstant order) * cellFrequency cell ^ order := by
  have smooth := cartesianPhase_contDiff parameters cell
  have dilatedSmooth := smooth.comp (dilationLinear scale).contDiff
  change ‖iteratedFDeriv ℝ order ((cartesianPhase parameters cell) -
    (cartesianPhase parameters cell) ∘ dilationLinear scale) point‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    (smooth.of_le (by exact_mod_cast le_top)).contDiffAt
    (dilatedSmooth.of_le (by exact_mod_cast le_top)).contDiffAt,
    (dilationLinear scale).iteratedFDeriv_comp_right smooth point (by exact_mod_cast le_top)]
  apply (norm_sub_le _ _).trans
  have composed := (iteratedFDeriv ℝ order (cartesianPhase parameters cell)
    (dilationLinear scale point)).norm_compContinuousLinearMap_le (fun _ => dilationLinear scale)
  have contraction : ∏ _ : Fin order, ‖dilationLinear scale‖ ≤ 1 := by
    simp only [dilationLinear_norm, abs_of_nonneg nonnegative, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ nonnegative bounded
  have second := composed.trans (mul_le_of_le_one_right (norm_nonneg _) contraction)
  have first := cartesianPhase_iterated_bound parameters cell order positive point
  have last := cartesianPhase_iterated_bound parameters cell order positive (dilationLinear scale point)
  linarith

def dilationDerivativeConstant (order : ℕ) : ℝ :=
  ∑ partition : OrderedFinpartition order, ∏ block, 2 * profileConstant (partition.partSize block)

theorem dilationDerivativeConstant_nonnegative (order : ℕ) :
    0 ≤ dilationDerivativeConstant order :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg
    (fun _ _ => mul_nonneg (by norm_num) (profileConstant_nonnegative _)))

theorem dilationMultiplier_iterated_bound (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (order : ℕ) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (dilationMultiplier parameters cell scale) point‖ ≤
      dilationDerivativeConstant order * cellFrequency cell ^ order := by
  change ‖iteratedFDeriv ℝ order (fun source => Real.exp (dilationPhaseDefect parameters cell scale source)) point‖ ≤ _
  rw [exp_comp_expansion _ (dilationPhaseDefect_smooth parameters cell scale)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ partition : OrderedFinpartition order,
        (∏ block, 2 * profileConstant (partition.partSize block)) * cellFrequency cell ^ order := by
      apply Finset.sum_le_sum
      intro partition _
      apply (partition.norm_compAlongOrderedFinpartition_le _ _).trans
      rw [LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ 1 * ∏ block, (2 * profileConstant (partition.partSize block)) *
            cellFrequency cell ^ partition.partSize block := by
          apply mul_le_mul
          · exact dilationMultiplier_le_one parameters cell nonnegative bounded point
          · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun block _ => dilationPhaseDefect_iterated_bound parameters cell nonnegative bounded
                (partition.partSize block) (partition.partSize_pos block) point)
          · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          · norm_num
        _ = _ := by
          rw [one_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, partition_size_sum]
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Grad.NonlinearRadial
