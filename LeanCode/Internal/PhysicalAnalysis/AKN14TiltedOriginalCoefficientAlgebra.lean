import AKN13OriginalTiltedPrimitiveBounds

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.AnnularCurrentSource

theorem RadialScaleRelated.originalCoefficient {dimension : ℕ} {lower : ℝ} {scale : ℝ → ℂ}
    {a b : DivisionRow dimension lower} (same : RadialScaleRelated lower scale a b)
    (parameters : PhaseParameters) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower a radius mode =
        scale radius • originalRowCoefficient parameters power lower b radius mode := by
  filter_upwards [same] with radius same
  intro mode
  rw [originalRowCoefficient, same]
  exact smul_comm _ _ _

theorem radialScaleRelated_of_originalCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (scale : ℝ → ℂ)
    (a b : DivisionRow dimension lower)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower a radius mode =
        scale radius • originalRowCoefficient parameters power lower b radius mode) :
    RadialScaleRelated lower scale a b := by
  filter_upwards [same, ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  have equality := same mode
  have nonzero : (originalRowWeight parameters power radius mode : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (originalRowWeight_pos parameters power radius (positive.trans_le inside.1) mode).ne')
  unfold originalRowCoefficient at equality
  rw [smul_comm (scale radius)] at equality
  exact (smul_right_injective _ nonzero) equality

theorem divisionHighWeight_compatible {lower : ℝ} (positive : 0 < lower) (bounded : lower ≤ 1)
    (power : ℕ) (high low : DivisionRow 1 lower) (same : RadialRowsCompatible lower power high low) :
    RadialRowsCompatible lower power (divisionHighWeight lower positive bounded high)
      (divisionHighWeight lower positive bounded low) := by
  intro mode
  rw [divisionHighWeight_mode, divisionHighWeight_mode, same, map_smul]

theorem divisionHighWeight_originalCoefficient (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (divisionHighWeight lower positive bounded field) radius mode =
        ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • originalRowCoefficient parameters power lower field radius mode :=
  RadialScaleRelated.originalCoefficient (divisionHighWeight_ae lower positive bounded field) parameters power

end Grad.ExhaustionSourceAllocation
