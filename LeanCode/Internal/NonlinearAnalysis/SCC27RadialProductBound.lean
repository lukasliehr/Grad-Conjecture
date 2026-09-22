import SCC26RadialProductMeasurable

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

def cellNormLp {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) : Lp ℝ 2 (volume.restrict (Icc lower 1)) :=
  (Lp.memLp field).norm.toLp (fun radius => ‖field radius‖)

theorem cellNormLp_ae {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), cellNormLp lower field radius = ‖field radius‖ :=
  (Lp.memLp field).norm.coeFn_toLp

theorem cellNormLp_norm {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) : ‖cellNormLp lower field‖ ≤ ‖field‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cellNormLp_ae lower field] with radius literal
  rw [literal, Real.norm_of_nonneg (norm_nonneg _)]

def twoRowMajorant {dimension : ℕ} (lower : ℝ) (firstBound secondBound : ℝ)
    (first second : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    Lp ℝ 2 (volume.restrict (Icc lower 1)) :=
  firstBound • cellNormLp lower first + secondBound • cellNormLp lower second

theorem twoRowMajorant_ae {dimension : ℕ} (lower : ℝ) (firstBound secondBound : ℝ)
    (first second : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      twoRowMajorant lower firstBound secondBound first second radius =
        firstBound * ‖first radius‖ + secondBound * ‖second radius‖ := by
  filter_upwards [Lp.coeFn_add (firstBound • cellNormLp lower first) (secondBound • cellNormLp lower second),
    Lp.coeFn_smul firstBound (cellNormLp lower first), Lp.coeFn_smul secondBound (cellNormLp lower second),
    cellNormLp_ae lower first, cellNormLp_ae lower second]
    with radius addition firstScaled secondScaled firstNorm secondNorm
  change (firstBound • cellNormLp lower first + secondBound • cellNormLp lower second) radius = _
  rw [addition, Pi.add_apply, firstScaled, secondScaled, Pi.smul_apply, Pi.smul_apply, firstNorm, secondNorm,
    smul_eq_mul, smul_eq_mul]

theorem twoRowMajorant_norm {dimension : ℕ} (lower : ℝ) (firstBound secondBound : ℝ)
    (firstNonnegative : 0 ≤ firstBound) (secondNonnegative : 0 ≤ secondBound)
    (first second : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    ‖twoRowMajorant lower firstBound secondBound first second‖ ≤ firstBound * ‖first‖ + secondBound * ‖second‖ := by
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_of_nonneg firstNonnegative, Real.norm_of_nonneg secondNonnegative]
  exact add_le_add (mul_le_mul_of_nonneg_left (cellNormLp_norm lower first) firstNonnegative)
    (mul_le_mul_of_nonneg_left (cellNormLp_norm lower second) secondNonnegative)

variable {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
  (lower : ℝ) (lowerNonnegative : 0 ≤ lower)
  (coefficient : ℝ → ℤ × ℤ → ℂ)
  (coefficientMeasurable : ∀ shift, AEStronglyMeasurable (fun radius => coefficient radius shift) (volume.restrict (Icc lower 1)))
  (lowBound highBound : ℝ) (lowNonnegative : 0 ≤ lowBound) (highNonnegative : 0 ≤ highBound)
  (moments : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    Summable (productMoment parameters 0 radius (coefficient radius)) ∧
    Summable (productMoment parameters power radius (coefficient radius)) ∧
    (∑' shift, productMoment parameters 0 radius (coefficient radius) shift) ≤ lowBound ∧
    (∑' shift, productMoment parameters power radius (coefficient radius) shift) ≤ highBound)

include lowerNonnegative lowNonnegative highNonnegative moments in
theorem radialProductValue_majorant
    (high low : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      ‖radialProductValue parameters power coefficient high low radius‖ ≤
        productPhaseConstant parameters power * ‖twoRowMajorant lower lowBound highBound high low radius‖ := by
  filter_upwards [moments, ae_restrict_mem measurableSet_Icc, twoRowMajorant_ae lower lowBound highBound high low]
    with radius moment inside majorant
  have disk : radius ∈ Icc (0 : ℝ) 1 := ⟨lowerNonnegative.trans inside.1, inside.2⟩
  rw [majorant, Real.norm_of_nonneg
    (add_nonneg (mul_nonneg lowNonnegative (norm_nonneg _)) (mul_nonneg highNonnegative (norm_nonneg _))),
    radialProductValue_inside parameters power coefficient high low radius disk]
  exact (pointwiseProduct_norm parameters power radius disk.1 disk.2 (coefficient radius) moment.1 moment.2.1
    (high radius) (low radius)).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right moment.2.2.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right moment.2.2.2 (norm_nonneg _))) (productPhaseConstant_pos _ _).le)

include lowerNonnegative coefficientMeasurable lowNonnegative highNonnegative moments in
theorem radialProductValue_memLp
    (high low : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    MemLp (radialProductValue parameters power coefficient high low) 2 (volume.restrict (Icc lower 1)) := by
  apply (Lp.memLp (twoRowMajorant lower lowBound highBound high low)).of_le_mul
    (c := productPhaseConstant parameters power)
  · exact radialProductValue_measurable parameters power _ coefficient coefficientMeasurable
      (moments.mono (fun _ moment _ => ⟨moment.1, moment.2.1⟩)) high low
      (Lp.aestronglyMeasurable high) (Lp.aestronglyMeasurable low)
  · exact radialProductValue_majorant parameters power lower lowerNonnegative coefficient lowBound highBound
      lowNonnegative highNonnegative moments high low

def radialProductLp (high low : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1)) :=
  (radialProductValue_memLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
    lowBound highBound lowNonnegative highNonnegative moments high low).toLp
    (radialProductValue parameters power coefficient high low)

theorem radialProductLp_ae (high low : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialProductLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
        lowBound highBound lowNonnegative highNonnegative moments high low radius =
          radialProductValue parameters power coefficient high low radius :=
  (radialProductValue_memLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
    lowBound highBound lowNonnegative highNonnegative moments high low).coeFn_toLp

theorem radialProductLp_norm (high low : Lp (CellL2 dimension) 2 (volume.restrict (Icc lower 1))) :
    ‖radialProductLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low‖ ≤
      productPhaseConstant parameters power * (lowBound * ‖high‖ + highBound * ‖low‖) := by
  have bound : ‖radialProductLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low‖ ≤
      productPhaseConstant parameters power * ‖twoRowMajorant lower lowBound highBound high low‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(radialProductValue_memLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low).coeFn_toLp,
      radialProductValue_majorant parameters power lower lowerNonnegative coefficient lowBound highBound
        lowNonnegative highNonnegative moments high low] with radius literal estimate
    change radialProductLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low radius = _ at literal
    rw [literal]
    exact estimate
  exact bound.trans (mul_le_mul_of_nonneg_left
    (twoRowMajorant_norm lower lowBound highBound lowNonnegative highNonnegative high low)
    (productPhaseConstant_pos _ _).le)

end Grad.SourceCollarCoefficients
