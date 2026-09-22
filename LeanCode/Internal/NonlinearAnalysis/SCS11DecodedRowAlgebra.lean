import SCS10OriginalCoefficientDecoding

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients

theorem originalRowCoefficient_add_ae {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (first second : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (first + second) radius mode =
        originalRowCoefficient parameters power lower first radius mode +
          originalRowCoefficient parameters power lower second radius mode := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [Lp.coeFn_add (first mode) (second mode)] with radius same
  change _ • (first mode + second mode) radius = _
  rw [same]
  exact smul_add _ _ _

theorem originalRowCoefficient_sub_ae {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (first second : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (first - second) radius mode =
        originalRowCoefficient parameters power lower first radius mode -
          originalRowCoefficient parameters power lower second radius mode := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [Lp.coeFn_sub (first mode) (second mode)] with radius same
  change _ • (first mode - second mode) radius = _
  rw [same]
  exact smul_sub _ _ _

theorem originalRowCoefficient_smul_ae {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (scalar : ℂ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (scalar • field) radius mode =
        scalar • originalRowCoefficient parameters power lower field radius mode := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [Lp.coeFn_smul scalar (field mode)] with radius same
  change _ • (scalar • field mode) radius = _
  rw [same]
  exact smul_comm ((originalRowWeight parameters power radius mode : ℂ)⁻¹) scalar (field mode radius)

theorem originalRowCoefficient_meanFree_ae {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (meanFreeRow lower field) radius mode =
        if mode.1 = 0 then 0 else originalRowCoefficient parameters power lower field radius mode := by
  filter_upwards [Lp.coeFn_zero (ComplexEuclidean dimension) 2 (volume.restrict (Icc lower 1))] with radius zeroValue
  intro mode
  unfold originalRowCoefficient
  rw [meanFreeRow_apply]
  split_ifs
  · rw [zeroValue]
    exact smul_zero _
  · rfl

end Grad.SourceCollarFullSource
