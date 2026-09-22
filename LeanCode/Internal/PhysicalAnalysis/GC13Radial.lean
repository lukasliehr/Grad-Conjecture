import GC13RadialSmooth

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ENNReal Interval Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

theorem continuous_unitClamp : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

theorem continuous_radialPoint_joint :
    Continuous (fun pair : ℝ × ClosedDisk => radialPoint pair.1 pair.2) := by
  apply continuous_induced_rng.mpr
  exact (continuous_unitClamp.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

theorem integral_negMulLog_Icc :
    ∫ time in Icc (0 : ℝ) 1, Real.negMulLog time = (1 : ℝ) / 4 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun time : ℝ =>
      -(time * (time * Real.log time) / 2) + time ^ 2 / 4)
    (fa := 0) (fb := (1 : ℝ) / 4)
    (hint := Real.continuous_negMulLog.intervalIntegrable 0 1)]
  · ring
  · norm_num
  · intro time membership
    have nonzero : time ≠ 0 := membership.1.ne'
    have derivative := (((hasDerivAt_id time).mul
        (Real.hasDerivAt_mul_log nonzero)).div_const 2).neg.add
          (((hasDerivAt_id time).pow 2).div_const 4)
    convert derivative using 1
    · ext x
      change -(x * (x * Real.log x) / 2) + x ^ 2 / 4 =
        -(x * (x * Real.log x) / 2) + x ^ 2 / 4
      rfl
    · dsimp [Real.negMulLog]
      ring
  · have primitiveContinuous : Continuous (fun time : ℝ =>
        -(time * (time * Real.log time) / 2) + time ^ 2 / 4) := by
      apply Continuous.add
      · apply Continuous.neg
        exact (continuous_id.mul Real.continuous_mul_log).div_const 2
      · exact (continuous_id.pow 2).div_const 4
    convert tendsto_nhdsWithin_of_tendsto_nhds
      primitiveContinuous.continuousAt using 1
    norm_num
  · have primitiveContinuous : Continuous (fun time : ℝ =>
        -(time * (time * Real.log time) / 2) + time ^ 2 / 4) := by
      apply Continuous.add
      · apply Continuous.neg
        exact (continuous_id.mul Real.continuous_mul_log).div_const 2
      · exact (continuous_id.pow 2).div_const 4
    convert tendsto_nhdsWithin_of_tendsto_nhds
      primitiveContinuous.continuousAt using 1
    norm_num

theorem radialPoint_norm {time : ℝ} (membership : time ∈ Icc (0 : ℝ) 1)
    (point : ClosedDisk) :
    ‖(radialPoint time point).val‖ = time * ‖point.val‖ := by
  change ‖unitClamp time • point.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, unitClamp_of_mem membership,
    abs_of_nonneg membership.1]

theorem coefficientScale_radial_le
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (cell : ℤ) (index : DerivativeIndex grade)
    {time : ℝ} (membership : time ∈ Icc (0 : ℝ) 1)
    (point : ClosedDisk) :
    coefficientScale L sigma gamma ell grade cell index point ≤
      coefficientScale L sigma gamma ell grade cell index
        (radialPoint time point) := by
  unfold coefficientScale originalEnvelope
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right
    · have gammaEll : 0 ≤ gamma * ell :=
        mul_nonneg (admissible_gamma_nonnegative admissible)
          (admissible_ell_nonnegative admissible)
      have radialNorm := radialPoint_norm membership point
      rw [radialNorm]
      have contractedRadius : time * ‖point.val‖ ≤ ‖point.val‖ := by
        calc
          time * ‖point.val‖ ≤ 1 * ‖point.val‖ :=
            mul_le_mul_of_nonneg_right membership.2 (norm_nonneg point.val)
          _ = ‖point.val‖ := one_mul _
      have scaled : gamma * ell * (time * ‖point.val‖) ≤
          gamma * ell * ‖point.val‖ := by
        exact mul_le_mul_of_nonneg_left contractedRadius gammaEll
      linarith
    · exact abs_nonneg (cell : ℝ)
  · exact pow_nonneg (Real.sqrt_nonneg _) _

def radialScaleRatio (L sigma gamma ell : ℝ) (grade : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ)
    (point : ClosedDisk) : ℝ :=
  coefficientScale L sigma gamma ell grade cell index point /
    coefficientScale L sigma gamma ell grade cell index (radialPoint time point)

theorem radialScaleRatio_nonnegative
    (L sigma gamma ell : ℝ) (grade : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ)
    (point : ClosedDisk) :
    0 ≤ radialScaleRatio L sigma gamma ell grade cell index time point := by
  exact div_nonneg
    (coefficientScale_pos L sigma gamma ell grade cell index point).le
    (coefficientScale_pos L sigma gamma ell grade cell index
      (radialPoint time point)).le

theorem radialScaleRatio_le_one
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (cell : ℤ) (index : DerivativeIndex grade)
    {time : ℝ} (membership : time ∈ Icc (0 : ℝ) 1)
    (point : ClosedDisk) :
    radialScaleRatio L sigma gamma ell grade cell index time point ≤ 1 := by
  exact (div_le_one
    (coefficientScale_pos L sigma gamma ell grade cell index
      (radialPoint time point))).mpr
        (coefficientScale_radial_le admissible grade cell index membership point)

def radialScaleRatioJoint (L sigma gamma ell : ℝ) (grade : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade) : C(ℝ × ClosedDisk, ℝ) where
  toFun pair := radialScaleRatio L sigma gamma ell grade cell index pair.1 pair.2
  continuous_toFun := by
    unfold radialScaleRatio
    exact ((continuous_coefficientScale L sigma gamma ell grade cell index).comp
      continuous_snd).div
        ((continuous_coefficientScale L sigma gamma ell grade cell index).comp
          continuous_radialPoint_joint)
        (fun pair => (coefficientScale_pos L sigma gamma ell grade cell index
          (radialPoint pair.1 pair.2)).ne')

def rawRadialCoordinateJoint
    {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    C(ℝ × ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun pair := (Real.negMulLog pair.1 : ℂ) •
    ((radialScaleRatio L sigma gamma ell grade cell index pair.1 pair.2 *
      unitClamp pair.1 ^ derivativeOrder index : ℝ) : ℂ) •
      coefficient (cell, index) (radialPoint pair.1 pair.2)
  continuous_toFun := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_negMulLog.comp continuous_fst)).smul
      ((Complex.continuous_ofReal.comp
        ((radialScaleRatioJoint L sigma gamma ell grade cell index).continuous.mul
          ((continuous_unitClamp.comp continuous_fst).pow _))).smul
        ((coefficient (cell, index)).continuous.comp
          continuous_radialPoint_joint))

def rawRadialCoordinate
    {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := ∫ time in Icc (0 : ℝ) 1,
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) coefficient cell index (time, point)
  continuous_toFun := by
    apply continuous_parametric_integral_of_continuous
    exact (rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) coefficient cell index).continuous.comp
        (continuous_snd.prodMk continuous_fst)
    exact isCompact_Icc

theorem rawRadialCoordinateJoint_norm_le
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade)
    {time : ℝ} (membership : time ∈ Icc (0 : ℝ) 1)
    (point : ClosedDisk) :
    ‖rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient cell index (time, point)‖ ≤
      Real.negMulLog time * ‖coefficient (cell, index)‖ := by
  have negNonnegative : 0 ≤ Real.negMulLog time :=
    Real.negMulLog_nonneg membership.1 membership.2
  have powerNonnegative : 0 ≤ unitClamp time ^ derivativeOrder index :=
    pow_nonneg (unitClamp_nonnegative time) _
  have powerBound : unitClamp time ^ derivativeOrder index ≤ 1 := by
    exact pow_le_one₀ (unitClamp_nonnegative time) (unitClamp_le_one time)
  have ratioNonnegative := radialScaleRatio_nonnegative L sigma gamma ell grade
    cell index time point
  have ratioBound := radialScaleRatio_le_one admissible grade cell index membership point
  have factorBound : radialScaleRatio L sigma gamma ell grade cell index time point *
      unitClamp time ^ derivativeOrder index ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul ratioBound powerBound powerNonnegative zero_le_one
      _ = 1 := one_mul 1
  have factorNonnegative : 0 ≤
      radialScaleRatio L sigma gamma ell grade cell index time point *
        unitClamp time ^ derivativeOrder index :=
    mul_nonneg ratioNonnegative powerNonnegative
  have evaluationBound :
      ‖coefficient (cell, index) (radialPoint time point)‖ ≤
        ‖coefficient (cell, index)‖ :=
    ContinuousMap.norm_coe_le_norm _ _
  change ‖(Real.negMulLog time : ℂ) •
      ((radialScaleRatio L sigma gamma ell grade cell index time point *
        unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
        coefficient (cell, index) (radialPoint time point)‖ ≤ _
  simp only [norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg negNonnegative,
    abs_of_nonneg (mul_nonneg ratioNonnegative powerNonnegative)]
  calc
    Real.negMulLog time *
        ((radialScaleRatio L sigma gamma ell grade cell index time point *
          unitClamp time ^ derivativeOrder index) *
          ‖coefficient (cell, index) (radialPoint time point)‖) ≤
      Real.negMulLog time * (1 * ‖coefficient (cell, index)‖) := by
        apply mul_le_mul_of_nonneg_left _ negNonnegative
        exact mul_le_mul factorBound evaluationBound
          (norm_nonneg _) zero_le_one
    _ = Real.negMulLog time * ‖coefficient (cell, index)‖ := by ring

theorem rawRadialCoordinate_norm_le
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ‖rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient cell index‖ ≤
      (1 : ℝ) / 4 * ‖coefficient (cell, index)‖ := by
  let joint := rawRadialCoordinateJoint (L := L) (sigma := sigma)
    (gamma := gamma) (ell := ell) coefficient cell index
  have jointIntegrable (point : ClosedDisk) :
      IntegrableOn (fun time : ℝ => joint (time, point)) (Icc 0 1) :=
    (joint.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have majorantIntegrable : IntegrableOn
      (fun time : ℝ => Real.negMulLog time * ‖coefficient (cell, index)‖)
      (Icc 0 1) :=
    (Real.continuous_negMulLog.mul continuous_const).continuousOn
      |>.integrableOn_compact isCompact_Icc
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num)
    (norm_nonneg (coefficient (cell, index))))).2
  intro point
  change ‖∫ time in Icc (0 : ℝ) 1, joint (time, point)‖ ≤ _
  calc
    _ ≤ ∫ time in Icc (0 : ℝ) 1, ‖joint (time, point)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ time in Icc (0 : ℝ) 1,
        Real.negMulLog time * ‖coefficient (cell, index)‖ := by
      apply integral_mono_ae (μ := volume.restrict (Icc (0 : ℝ) 1))
      · exact (jointIntegrable point).norm
      · exact majorantIntegrable
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with time membership
        exact rawRadialCoordinateJoint_norm_le admissible coefficient cell index
          membership point
    _ = (1 : ℝ) / 4 * ‖coefficient (cell, index)‖ := by
      rw [integral_mul_const, integral_negMulLog_Icc]

def rawRadial
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    WeightedAmbient grade inputDimension outputDimension := by
  refine ⟨fun pair => rawRadialCoordinate (L := L) (sigma := sigma)
    (gamma := gamma) (ell := ell) coefficient pair.1 pair.2, ?_⟩
  apply memℓp_gen
  have each (index : DerivativeIndex grade) : Summable (fun cell : ℤ =>
      ‖rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient cell index‖) :=
    Summable.of_nonneg_of_le
      (fun cell : ℤ => norm_nonneg (rawRadialCoordinate (L := L) (sigma := sigma)
        (gamma := gamma) (ell := ell) coefficient cell index))
      (fun cell => rawRadialCoordinate_norm_le admissible coefficient cell index)
      ((coordinate_norm_summable coefficient index).mul_left ((1 : ℝ) / 4))
  have swapped : Summable (fun pair : DerivativeIndex grade × ℤ =>
      ‖rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient pair.2 pair.1‖) := by
    apply (summable_prod_of_nonneg (fun pair : DerivativeIndex grade × ℤ =>
      norm_nonneg (rawRadialCoordinate (L := L) (sigma := sigma)
        (gamma := gamma) (ell := ell) coefficient pair.2 pair.1))).2
    exact ⟨each, (hasSum_fintype _).summable⟩
  have all : Summable (fun pair : ℤ × DerivativeIndex grade =>
      ‖rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient pair.1 pair.2‖) := by
    apply (Equiv.prodComm (DerivativeIndex grade) ℤ).summable_iff.mp
    exact swapped
  have oneToReal : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  simpa only [oneToReal, Real.rpow_one] using all

@[simp] theorem rawRadial_apply
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawRadial admissible coefficient (cell, index) =
      rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient cell index := rfl

theorem rawRadial_norm_le
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    ‖rawRadial admissible coefficient‖ ≤ (1 : ℝ) / 4 * ‖coefficient‖ := by
  rw [ambient_norm_formula, ambient_norm_formula]
  calc
    (∑ index : DerivativeIndex grade, ∑' cell : ℤ,
        ‖rawRadial admissible coefficient (cell, index)‖) ≤
      ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
        (1 : ℝ) / 4 * ‖coefficient (cell, index)‖ := by
      apply Finset.sum_le_sum
      intro index _membership
      apply Summable.tsum_le_tsum
      · intro cell
        exact rawRadialCoordinate_norm_le admissible coefficient cell index
      · exact coordinate_norm_summable (rawRadial admissible coefficient) index
      · exact (coordinate_norm_summable coefficient index).mul_left ((1 : ℝ) / 4)
    _ = (1 : ℝ) / 4 *
        ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
          ‖coefficient (cell, index)‖ := by
      simp_rw [tsum_mul_left]
      rw [Finset.mul_sum]

theorem rawRadialCoordinateJoint_add
    {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (first second : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) (first + second) cell index (time, point) =
      rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) first cell index (time, point) +
      rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) second cell index (time, point) := by
  change (Real.negMulLog time : ℂ) •
    ((radialScaleRatio L sigma gamma ell grade cell index time point *
      unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
      (first (cell, index) (radialPoint time point) +
    second (cell, index) (radialPoint time point)) = _
  simp only [smul_add]
  rfl

theorem rawRadialCoordinateJoint_smul
    {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (scalar : ℂ) (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (time : ℝ) (point : ClosedDisk) :
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) (scalar • coefficient) cell index (time, point) =
      scalar • rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient cell index (time, point) := by
  change (Real.negMulLog time : ℂ) •
    ((radialScaleRatio L sigma gamma ell grade cell index time point *
      unitClamp time ^ derivativeOrder index : ℝ) : ℂ) •
      (scalar • coefficient (cell, index) (radialPoint time point)) = _
  rw [smul_comm _ scalar, smul_comm _ scalar]
  rfl

theorem rawRadialCoordinate_add
    {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (first second : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) (first + second) cell index =
      rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) first cell index +
      rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) second cell index := by
  apply ContinuousMap.ext
  intro point
  have integrable (coefficient : WeightedAmbient grade inputDimension outputDimension) :
      IntegrableOn (fun time : ℝ => rawRadialCoordinateJoint (L := L)
        (sigma := sigma) (gamma := gamma) (ell := ell) coefficient cell index
          (time, point)) (Icc 0 1) :=
    ((rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) coefficient cell index).continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn
          |>.integrableOn_compact isCompact_Icc
  change (∫ time in Icc (0 : ℝ) 1,
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) (first + second) cell index (time, point)) =
    (∫ time in Icc (0 : ℝ) 1,
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) first cell index (time, point)) +
    ∫ time in Icc (0 : ℝ) 1,
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) second cell index (time, point)
  rw [← integral_add (integrable first) (integrable second)]
  apply integral_congr_ae
  filter_upwards with time
  exact rawRadialCoordinateJoint_add first second cell index time point

theorem rawRadialCoordinate_smul
    {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (scalar : ℂ) (coefficient : WeightedAmbient grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) (scalar • coefficient) cell index =
      scalar • rawRadialCoordinate (L := L) (sigma := sigma) (gamma := gamma)
        (ell := ell) coefficient cell index := by
  apply ContinuousMap.ext
  intro point
  change (∫ time in Icc (0 : ℝ) 1,
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) (scalar • coefficient) cell index (time, point)) =
    scalar • ∫ time in Icc (0 : ℝ) 1,
    rawRadialCoordinateJoint (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) coefficient cell index (time, point)
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with time
  exact rawRadialCoordinateJoint_smul scalar coefficient cell index time point

def rawRadialLinear
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ) :
    WeightedAmbient grade inputDimension outputDimension →ₗ[ℂ]
      WeightedAmbient grade inputDimension outputDimension where
  toFun := rawRadial admissible
  map_add' first second := by
    apply lp.ext
    funext pair
    exact rawRadialCoordinate_add first second pair.1 pair.2
  map_smul' scalar coefficient := by
    apply lp.ext
    funext pair
    exact rawRadialCoordinate_smul scalar coefficient pair.1 pair.2

def rawRadialMap
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade inputDimension outputDimension : ℕ) :
    WeightedAmbient grade inputDimension outputDimension →L[ℂ]
      WeightedAmbient grade inputDimension outputDimension :=
  (rawRadialLinear admissible grade inputDimension outputDimension).mkContinuous
    ((1 : ℝ) / 4) (rawRadial_norm_le admissible)

end Grad.GaugeCoefficients.Radial
