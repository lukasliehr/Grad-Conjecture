import SCD25LiteralDivision

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

/-- The bounded actual derivative graph map; the radial coordinate norm is
the original sum of individual full Fourier/radial L2 norms. -/
def completedDivision {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) :
    AGrade parameters dimension (power + radial + 3) →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  (completedDivisionArray lower positive bounded parameters power radial).codRestrict
    (annularDerivativeGraph dimension lower positive radial)
    (completedDivisionArray_graph lower positive bounded parameters power radial)

theorem completedDivision_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3)) :
    ‖completedDivision lower positive bounded parameters power radial field‖ ≤
      divisionGraphConstant power radial * ‖field‖ :=
  completedDivisionArray_bound lower positive bounded parameters power radial field

theorem completedDivision_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3)) :
    ‖completedDivision lower positive bounded parameters power radial field‖ =
      ∑ index : Fin (radial + 1),
        ‖(completedDivision lower positive bounded parameters power radial field).val index‖ := by
  exact completedDivisionArray_norm lower positive bounded parameters power radial field

theorem continuousDifferenceQuotient_flat {dimension grade : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (flat : OriginalValueFlat parameters large field)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angle : ℝ) :
    continuousDifferenceQuotient lower positive bounded
      (completedWeightedCell parameters large cell field) (radius, angle) =
      cartesianWeight parameters cell (polarPlane (radius, angle)) •
        (radius⁻¹ • completedOriginalCell parameters large cell field
          (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) := by
  have pointLaw : annularClosedPoint lower positive bounded (radius, angle) =
      polarClosedPoint radius angle (positive.le.trans inside.1) inside.2 := by
    apply Subtype.ext
    change polarPlane (annularClamp lower radius, angle) = polarPlane (radius, angle)
    rw [annularClamp_eq lower radius inside]
  rw [continuousDifferenceQuotient, originalValueFlat_weighted parameters large field flat,
    sub_zero, annularClamp_eq lower radius inside, pointLaw,
    completedWeightedCell, ContinuousLinearMap.comp_apply, originalWeightAction_apply]
  exact smul_comm _ _ _

/-- Exact literal zeroth coordinate, including nu^p and the sqrt(r) radial
isometry. On the actual annulus the field is W_n(r e_r) u_n(r e_r)/r. -/
theorem completedDivision_flat_literal {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3))
    (flat : OriginalValueFlat parameters (by omega) field) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      (completedDivision lower positive bounded parameters power radial field).val 0 mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
          angularCoefficient (fun angle =>
            cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
              (radius⁻¹ • completedOriginalCell parameters (by omega) mode.2 field
                (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2))) mode.1) := by
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
    completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters
      (by omega) field mode radius = _
  rw [completedDivisionRow_literal]
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (continuousDifferenceLp lower positive bounded mode.1
        (completedWeightedCell parameters (by omega) mode.2 field)),
    radialToLp_ae lower
      (continuousDifferenceCoefficient lower positive bounded mode.1
        (completedWeightedCell parameters (by omega) mode.2 field))
      (continuousDifferenceCoefficient_continuous lower positive bounded mode.1
        (completedWeightedCell parameters (by omega) mode.2 field))]
    with radius scaling representative
  intro inside
  change continuousDifferenceLp lower positive bounded mode.1
    (completedWeightedCell parameters (by omega) mode.2 field) radius = _ at representative
  rw [scaling, Pi.smul_apply, representative]
  congr 2
  unfold continuousDifferenceCoefficient
  congr 1
  funext angle
  exact continuousDifferenceQuotient_flat lower positive bounded parameters (by omega) field flat
    mode.2 radius inside angle

end Grad.SourceCollarDivision
