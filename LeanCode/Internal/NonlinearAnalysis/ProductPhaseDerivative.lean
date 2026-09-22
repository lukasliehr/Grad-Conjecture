import ProductPhaseDefect

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.AnalyticWeights.Higher

theorem cartesianPhase_iterated_bound (parameters : PhaseParameters) (cell : ℤ)
    (order : ℕ) (orderPositive : 1 ≤ order) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (cartesianPhase parameters cell) point‖ ≤
      profileConstant order * cellFrequency cell ^ order := by
  have bound : ‖iteratedFDeriv ℝ order (cartesianPhase parameters cell) point‖ ≤
      profileConstant order * parameters.gamma * cellFrequency cell ^ order := by
    change ‖iteratedFDeriv ℝ order
      (Grad.AnalyticWeights.Calculus.physicalPhase parameters.sigma0 parameters.gamma 1 cell) point‖ ≤ _
    simpa only [cellFrequency, one_pow, mul_one] using
      physicalPhase_iterated_norm_bound parameters.sigma0 parameters.gamma 1 cell
        parameters.gamma_pos.le zero_le_one order orderPositive point
  refine bound.trans ?_
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (parameters_gamma_lt_one parameters).le
      (profileConstant_nonnegative order)) (pow_nonneg (cellFrequency_pos cell).le order)

def phaseDefectDerivativeConstant (arity order : ℕ) : ℝ :=
  (arity + 1 : ℕ) * profileConstant order

theorem phaseDefectDerivativeConstant_nonnegative (arity order : ℕ) :
    0 ≤ phaseDefectDerivativeConstant arity order :=
  mul_nonneg (Nat.cast_nonneg _) (profileConstant_nonnegative _)

theorem productPhaseDefect_iterated_bound {arity : ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (order : ℕ) (orderPositive : 1 ≤ order) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (productPhaseDefect parameters cells) point‖ ≤
      phaseDefectDerivativeConstant arity order * productFrequency cells ^ order := by
  have inputFrequencyBound (index : Fin arity) : cellFrequency (cells index) ≤ productFrequency cells :=
    Finset.single_le_sum (fun _ _ => (cellFrequency_pos _).le) (Finset.mem_univ index)
  have cellBound (cell : ℤ) (frequencyBound : cellFrequency cell ≤ productFrequency cells) :
      ‖iteratedFDeriv ℝ order (cartesianPhase parameters cell) point‖ ≤
        profileConstant order * productFrequency cells ^ order :=
    (cartesianPhase_iterated_bound parameters cell order orderPositive point).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (cellFrequency_pos _).le frequencyBound order)
        (profileConstant_nonnegative order))
  have eachSmooth : ∀ index, ContDiff ℝ ∞ (cartesianPhase parameters (cells index)) :=
    fun _ => cartesianPhase_contDiff _ _
  have sumSmooth : ContDiff ℝ ∞ (fun source => ∑ index, cartesianPhase parameters (cells index) source) := by
    fun_prop
  change ‖iteratedFDeriv ℝ order
    ((fun source => cartesianPhase parameters (∑ index, cells index) source) -
      fun source => ∑ index, cartesianPhase parameters (cells index) source) point‖ ≤ _
  rw [iteratedFDeriv_sub_apply
    ((cartesianPhase_contDiff parameters _).of_le (by exact_mod_cast le_top)).contDiffAt
    (sumSmooth.of_le (by exact_mod_cast le_top)).contDiffAt,
    iteratedFDeriv_fun_sum_apply (fun index _ =>
      ((eachSmooth index).of_le (by exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ order (cartesianPhase parameters (∑ index, cells index)) point‖ +
        ∑ index, ‖iteratedFDeriv ℝ order (cartesianPhase parameters (cells index)) point‖ :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ profileConstant order * productFrequency cells ^ order +
        ∑ _index : Fin arity, profileConstant order * productFrequency cells ^ order :=
      add_le_add (cellBound _ (cellFrequency_sum_le positiveArity cells))
        (Finset.sum_le_sum (fun index _ => cellBound _ (inputFrequencyBound index)))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        phaseDefectDerivativeConstant, Nat.cast_add, Nat.cast_one]
      ring

def productDefectDerivativeConstant (arity order : ℕ) : ℝ :=
  ∑ partition : OrderedFinpartition order,
    ∏ block, phaseDefectDerivativeConstant arity (partition.partSize block)

theorem productDefectDerivativeConstant_nonnegative (arity order : ℕ) :
    0 ≤ productDefectDerivativeConstant arity order :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg
    (fun _ _ => phaseDefectDerivativeConstant_nonnegative _ _))

theorem productDefectMultiplier_iterated_bound {arity : ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (order : ℕ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (productDefectMultiplier parameters cells) point.val‖ ≤
      productDefectDerivativeConstant arity order * productFrequency cells ^ order := by
  change ‖iteratedFDeriv ℝ order (fun source => Real.exp (productPhaseDefect parameters cells source)) point.val‖ ≤ _
  rw [exp_comp_expansion _ (productPhaseDefect_smooth parameters cells)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ partition : OrderedFinpartition order,
        (∏ block, phaseDefectDerivativeConstant arity (partition.partSize block)) *
          productFrequency cells ^ order := by
      apply Finset.sum_le_sum
      intro partition _
      apply (partition.norm_compAlongOrderedFinpartition_le _ _).trans
      rw [LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ 1 * ∏ block, phaseDefectDerivativeConstant arity (partition.partSize block) *
            productFrequency cells ^ partition.partSize block := by
          apply mul_le_mul
          · exact productDefectMultiplier_le_one positiveArity parameters cells point
          · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun block _ => productPhaseDefect_iterated_bound positiveArity parameters cells
                (partition.partSize block) (partition.partSize_pos block) point.val)
          · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          · norm_num
        _ = _ := by
          rw [one_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, partition_size_sum]
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Grad.NonlinearProduct
