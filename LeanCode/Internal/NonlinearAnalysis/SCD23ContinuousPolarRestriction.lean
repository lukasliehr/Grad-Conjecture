import SCD22CompletedCellValues

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem angularCoefficient_continuous_parameter {dimension : ℕ}
    (field : ℝ × ℝ → ComplexEuclidean dimension) (continuousField : Continuous field) (mode : ℤ) :
    Continuous (fun radius => angularCoefficient (fun angle => field (radius, angle)) mode) := by
  simp only [angularCoefficient_compact]
  have continuousIntegral := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (s := Icc (-Real.pi) Real.pi)
    (f := fun radius angle : ℝ => cellExponential (-mode) angle • field (radius, angle))
    (((cellExponential_smooth (-mode)).continuous.comp continuous_snd).smul continuousField)
    isCompact_Icc
  exact continuousIntegral.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem angularCoefficient_sup_bound {dimension : ℕ}
    (field : ℝ → ComplexEuclidean dimension) (mode : ℤ) (bound : ℝ) (_nonnegative : 0 ≤ bound)
    (bounded : ∀ angle ∈ Icc (-Real.pi) Real.pi, ‖field angle‖ ≤ bound) :
    ‖angularCoefficient field mode‖ ≤ bound := by
  rw [angularCoefficient_integral, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  have integralBound : ‖∫ angle in -Real.pi..Real.pi,
      fourier (-mode) (angle : CellCircle) • field angle‖ ≤ bound * |Real.pi - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro angle inside
    have normPhase : ‖fourier (-mode) (angle : CellCircle)‖ = 1 := cellCharacter_apply_norm _ _
    rw [norm_smul, normPhase, one_mul]
    apply bounded angle
    have interval : angle ∈ Ioc (-Real.pi) Real.pi := by
      simpa only [uIoc_of_le (neg_lt_self Real.pi_pos).le] using inside
    exact ⟨interval.1.le, interval.2⟩
  apply (mul_le_mul_of_nonneg_left integralBound (by positivity)).trans_eq
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp

def annularClamp (lower : ℝ) (radius : ℝ) : ℝ := max lower (min 1 radius)

theorem annularClamp_continuous (lower : ℝ) : Continuous (annularClamp lower) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem annularClamp_mem (lower : ℝ) (bounded : lower ≤ 1) (radius : ℝ) :
    annularClamp lower radius ∈ Icc lower 1 :=
  ⟨le_max_left _ _, max_le bounded (min_le_left _ _)⟩

theorem annularClamp_eq (lower radius : ℝ) (inside : radius ∈ Icc lower 1) :
    annularClamp lower radius = radius := by
  rw [annularClamp, min_eq_right inside.2, max_eq_right inside.1]

def annularClosedPoint (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (point : ℝ × ℝ) : ClosedDisk :=
  polarClosedPoint (annularClamp lower point.1) point.2
    (positive.le.trans (annularClamp_mem lower bounded point.1).1)
    (annularClamp_mem lower bounded point.1).2

theorem annularClosedPoint_continuous (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    Continuous (annularClosedPoint lower positive bounded) := by
  apply Continuous.subtype_mk
  exact polarPlane_smooth.continuous.comp
    (((annularClamp_continuous lower).comp continuous_fst).prodMk continuous_snd)

/-- Literal difference quotient on a fixed positive annulus, continuously
extended outside that annulus only to define an ordinary radial L2 representative. -/
def continuousDifferenceQuotient {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  (annularClamp lower point.1)⁻¹ •
    (field (annularClosedPoint lower positive bounded point) - field (ambientClosedDisk 0))

theorem continuousDifferenceQuotient_continuous {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    Continuous (continuousDifferenceQuotient lower positive bounded field) := by
  have scalarContinuous : Continuous (fun point : ℝ × ℝ => (annularClamp lower point.1)⁻¹) := by
    apply Continuous.inv₀ ((annularClamp_continuous lower).comp continuous_fst)
    intro point
    exact ne_of_gt (positive.trans_le (annularClamp_mem lower bounded point.1).1)
  exact scalarContinuous.smul
    ((field.continuous.comp (annularClosedPoint_continuous lower positive bounded)).sub continuous_const)

theorem continuousDifferenceQuotient_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) (point : ℝ × ℝ) :
    ‖continuousDifferenceQuotient lower positive bounded field point‖ ≤ (2 / lower) * ‖field‖ := by
  rw [continuousDifferenceQuotient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (positive.trans_le (annularClamp_mem lower bounded point.1).1))]
  have reciprocal : (annularClamp lower point.1)⁻¹ ≤ lower⁻¹ :=
    inv_anti₀ positive (annularClamp_mem lower bounded point.1).1
  have difference : ‖field (annularClosedPoint lower positive bounded point) - field (ambientClosedDisk 0)‖ ≤
      2 * ‖field‖ := by
    exact (norm_sub_le _ _).trans ((add_le_add
      (ContinuousMap.norm_coe_le_norm field _) (ContinuousMap.norm_coe_le_norm field _)).trans_eq (by ring))
  exact (mul_le_mul reciprocal difference (norm_nonneg _) (inv_pos.2 positive).le).trans_eq (by ring)

end Grad.SourceCollarDivision
