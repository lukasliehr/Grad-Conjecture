import AAG6ActualCoerciveForm

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.SourceCollarDivision Grad.CircularHighWeak

def annularSymbolRatio (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (symbol : ℝ) : C(ℝ, ℝ) :=
  ⟨fun radius => symbol / annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius,
    continuous_const.div (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

theorem annularSymbolRatio_bound (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (symbol : ℝ) (dominated : ∀ radius ∈ Icc lower 1, symbol ^ 2 ≤ annularPotential length radius mode.val.1 mode.val.2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularSymbolRatio lower length positive mode symbol radius| ≤ 1 := by
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSq := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have bound := dominated radius inside
  change |symbol / annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ 1
  rw [abs_div, abs_of_pos rootPositive]
  apply (div_le_one rootPositive).2
  nlinarith [sq_abs symbol, abs_nonneg symbol]

theorem annularDSymbol_dominated (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ((mode.val.1 : ℝ) * highMultiplier mode.val.1) ^ 2 ≤
      annularPotential length radius mode.val.1 mode.val.2 := by
  have radiusPositive := positive.trans_le inside.1
  have bNonnegative := highMultiplier_nonnegative mode.val.1
  have bUpper := highMultiplier_one_le mode.val.1
  have bSq : highMultiplier mode.val.1 ^ 2 ≤ 1 := by nlinarith
  have modeBound : (mode.val.1 : ℝ) ^ 2 ≤ (mode.val.1 : ℝ) ^ 2 / radius ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos radiusPositive)).2
    have radiusSq : radius ^ 2 ≤ 1 := by nlinarith [inside.2]
    nlinarith [mul_nonneg (sq_nonneg (mode.val.1 : ℝ)) (sub_nonneg.mpr radiusSq)]
  have symbolBound := mul_le_mul_of_nonneg_left bSq (sq_nonneg (mode.val.1 : ℝ))
  have cellNonnegative := div_nonneg (mul_nonneg bNonnegative (sq_nonneg (mode.val.2 : ℝ))) (sq_nonneg length)
  unfold annularPotential
  nlinarith only [symbolBound, modeBound, cellNonnegative]

theorem annularCellSymbol_dominated (lower length : ℝ) (_positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (_inside : radius ∈ Icc lower 1) :
    (highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length) ^ 2 ≤
      annularPotential length radius mode.val.1 mode.val.2 := by
  have bNonnegative := highMultiplier_nonnegative mode.val.1
  have bUpper := highMultiplier_one_le mode.val.1
  have bSq : highMultiplier mode.val.1 ^ 2 ≤ highMultiplier mode.val.1 := by nlinarith
  have cellBound := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right bSq (sq_nonneg (mode.val.2 : ℝ))) (sq_nonneg length)
  have angularNonnegative := div_nonneg (sq_nonneg (mode.val.1 : ℝ)) (sq_nonneg radius)
  rw [div_pow, mul_pow]
  unfold annularPotential
  linarith

def annularImaginarySymbolMap (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (symbol : ℝ) (dominated : ∀ radius ∈ Icc lower 1, symbol ^ 2 ≤ annularPotential length radius mode.val.1 mode.val.2) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  Complex.I • scalarRadialMap lower (annularSymbolRatio lower length positive mode symbol) 1
    (annularSymbolRatio_bound lower length positive mode symbol dominated)

theorem annularImaginarySymbolMap_bound (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (symbol : ℝ) (dominated : ∀ radius ∈ Icc lower 1, symbol ^ 2 ≤ annularPotential length radius mode.val.1 mode.val.2)
    (field : RadialL2 1 lower) :
    ‖annularImaginarySymbolMap lower length positive mode symbol dominated field‖ ≤ 1 * ‖field‖ := by
  change ‖Complex.I • scalarRadialMap lower (annularSymbolRatio lower length positive mode symbol) 1
    (annularSymbolRatio_bound lower length positive mode symbol dominated) field‖ ≤ _
  rw [norm_smul, Complex.norm_I, one_mul]
  exact scalarRadialMap_bound _ _ _ _ field

def annularEnergyD (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (complexLpTwoMap (fun mode : HighAnnularMode => annularImaginarySymbolMap lower length positive mode
      ((mode.val.1 : ℝ) * highMultiplier mode.val.1) (annularDSymbol_dominated lower length positive mode))
    1 (by norm_num) (fun mode => annularImaginarySymbolMap_bound lower length positive mode _ _)).comp
      (annularEnergyMass lower length positive)

def annularEnergyCell (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (complexLpTwoMap (fun mode : HighAnnularMode => annularImaginarySymbolMap lower length positive mode
      (highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length) (annularCellSymbol_dominated lower length positive mode))
    1 (by norm_num) (fun mode => annularImaginarySymbolMap_bound lower length positive mode _ _)).comp
      (annularEnergyMass lower length positive)

end Grad.AnnularVariational
