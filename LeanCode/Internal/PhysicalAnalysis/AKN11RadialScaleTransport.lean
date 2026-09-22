import AKN10WeightedRowRealization
import AIS1HighKnownHilbertAmbient

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.SourceCollarAngular Grad.AnnularCurrentSource

def RadialScaleRelated {dimension : ℕ} (lower : ℝ) (scale : ℝ → ℂ)
    (weighted original : DivisionRow dimension lower) : Prop :=
  ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
    weighted mode radius = scale radius • original mode radius

namespace RadialScaleRelated

theorem add {dimension : ℕ} {lower : ℝ} {scale : ℝ → ℂ}
    {a b c d : DivisionRow dimension lower} (first : RadialScaleRelated lower scale a b)
    (second : RadialScaleRelated lower scale c d) : RadialScaleRelated lower scale (a + c) (b + d) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [first, second, Lp.coeFn_add (a mode) (c mode), Lp.coeFn_add (b mode) (d mode)]
    with radius first second left right
  change (a mode + c mode) radius = _ • (b mode + d mode) radius
  rw [left, right, Pi.add_apply, Pi.add_apply, first, second, smul_add]

theorem sub {dimension : ℕ} {lower : ℝ} {scale : ℝ → ℂ}
    {a b c d : DivisionRow dimension lower} (first : RadialScaleRelated lower scale a b)
    (second : RadialScaleRelated lower scale c d) : RadialScaleRelated lower scale (a - c) (b - d) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [first, second, Lp.coeFn_sub (a mode) (c mode), Lp.coeFn_sub (b mode) (d mode)]
    with radius first second left right
  change (a mode - c mode) radius = _ • (b mode - d mode) radius
  rw [left, right, Pi.sub_apply, Pi.sub_apply, first, second, smul_sub]

theorem smul {dimension : ℕ} {lower : ℝ} {scale : ℝ → ℂ}
    {a b : DivisionRow dimension lower} (same : RadialScaleRelated lower scale a b) (scalar : ℂ) :
    RadialScaleRelated lower scale (scalar • a) (scalar • b) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [same, Lp.coeFn_smul scalar (a mode), Lp.coeFn_smul scalar (b mode)] with radius same left right
  change (scalar • a mode) radius = _ • (scalar • b mode) radius
  rw [left, right, Pi.smul_apply, Pi.smul_apply, same, smul_comm]

theorem shift {dimension : ℕ} {lower : ℝ} {scale : ℝ → ℂ}
    {a b : DivisionRow dimension lower} (same : RadialScaleRelated lower scale a b) (power : ℕ) (shift : ℤ) :
    RadialScaleRelated lower scale (annularRowShift lower power shift a) (annularRowShift lower power shift b) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [same, Lp.coeFn_smul (annularShiftScalar power shift mode) (a (mode.1 - shift, mode.2)),
    Lp.coeFn_smul (annularShiftScalar power shift mode) (b (mode.1 - shift, mode.2))] with radius same left right
  rw [annularRowShift_apply, annularRowShift_apply, left, right, Pi.smul_apply, Pi.smul_apply, same, smul_comm]

theorem valueMap {sourceDimension targetDimension : ℕ} {lower : ℝ} {scale : ℝ → ℂ}
    {a b : DivisionRow sourceDimension lower} (same : RadialScaleRelated lower scale a b)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    RadialScaleRelated lower scale (divisionRowValueMap lower mapping a) (divisionRowValueMap lower mapping b) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [same, mapping.coeFn_compLpL (a mode), mapping.coeFn_compLpL (b mode)] with radius same left right
  change (mapping.compLpL 2 (volume.restrict (Icc lower 1)) (a mode)) radius =
    scale radius • (mapping.compLpL 2 (volume.restrict (Icc lower 1)) (b mode)) radius
  rw [left, right, same, map_smul]

theorem radial {lower : ℝ} {scale : ℝ → ℂ} {a b : DivisionRow 2 lower}
    (same : RadialScaleRelated lower scale a b) (positive : 0 < lower) (power : ℕ) :
    RadialScaleRelated lower scale (radialRowContraction lower positive power a) (radialRowContraction lower positive power b) := by
  rw [radialRowContraction_formula, radialRowContraction_formula]
  exact ((((same.shift power 1).add (same.shift power (-1))).smul _).valueMap _).add
    ((((same.shift power 1).sub (same.shift power (-1))).smul _).valueMap _)

theorem tangential {lower : ℝ} {scale : ℝ → ℂ} {a b : DivisionRow 2 lower}
    (same : RadialScaleRelated lower scale a b) (positive : 0 < lower) (power : ℕ) :
    RadialScaleRelated lower scale (tangentialRowContraction lower positive power a) (tangentialRowContraction lower positive power b) := by
  rw [tangentialRowContraction_formula, tangentialRowContraction_formula]
  exact ((((same.shift power 1).add (same.shift power (-1))).smul _).valueMap _).sub
    ((((same.shift power 1).sub (same.shift power (-1))).smul _).valueMap _)

theorem eq_actualHighWeight {lower : ℝ} {a b : DivisionRow 1 lower}
    (same : RadialScaleRelated lower (fun radius => ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ)) a b)
    (positive : 0 < lower) (bounded : lower ≤ 1) : a = divisionHighWeight lower positive bounded b := by
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [same, divisionHighWeight_ae lower positive bounded b] with radius same literal
  rw [same, literal]

end RadialScaleRelated
end Grad.ExhaustionSourceAllocation
