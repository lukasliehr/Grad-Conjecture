import SM5DerivativeBounds

noncomputable section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothingFamily

open Grad.FourierGrade Grad.ClosedJets

theorem scaleMultiplier_zero_above (order : ℕ) (frequency scale : ℝ) (positive : 0 < scale)
    (above : 2 * scale < frequency) : scaleMultiplier order frequency scale = 0 := by
  rw [scaleMultiplier, scaleProfile_right order _ ((lt_div_iff₀ positive).mpr above), mul_zero]

theorem scaleMultiplier_contDiffAt (order : ℕ) (frequency scale : ℝ) (positive : 0 < scale) :
    ContDiffAt ℝ ∞ (scaleMultiplier order frequency) scale :=
  (Real.contDiffAt_rpow_const_of_ne positive.ne').mul
    ((scaleProfile_smooth order).contDiffAt.comp scale
      (contDiffAt_const.div contDiffAt_id positive.ne'))

theorem fourierScaleDerivative_grade_sum {dimension : ℕ}
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale)
    (values : JCore (ComplexEuclidean dimension)) (support : Finset FourierMode)
    (covers : ∀ mode, frequencyWeight mode ≤ 2 * scale → mode ∈ support) :
    coreToGrade grade (fourierScaleDerivative order scale values) =
      ∑ mode ∈ support, scaleMultiplier order (frequencyWeight mode) scale •
        (lp.single 2 mode (coreToGrade grade values mode) : JGrade (ComplexEuclidean dimension) grade) := by
  have sumIdentity := lp.hasSum_single (p := 2) (by norm_num)
    (coreToGrade grade (fourierScaleDerivative order scale values))
  have finiteSum : HasSum (fun mode =>
      lp.single 2 mode (coreToGrade grade (fourierScaleDerivative order scale values) mode))
      (∑ mode ∈ support, lp.single 2 mode
        (coreToGrade grade (fourierScaleDerivative order scale values) mode)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro mode outside
    have weightAbove : 2 * scale < frequencyWeight mode := lt_of_not_ge (fun below => outside (covers mode below))
    have zeroMultiplier := scaleMultiplier_zero_above order (frequencyWeight mode) scale positive weightAbove
    have coordinateZero : coreToGrade grade (fourierScaleDerivative order scale values) mode = 0 := by
      change (frequencyWeight mode : ℂ) ^ grade •
        ((scaleMultiplier order (frequencyWeight mode) scale : ℂ) • values.1 mode) = 0
      rw [zeroMultiplier, Complex.ofReal_zero, zero_smul, smul_zero]
    rw [coordinateZero, lp.single_zero]
  rw [sumIdentity.unique finiteSum]
  apply Finset.sum_congr rfl
  intro mode _
  rw [← lp.single_smul]
  congr 1
  change (frequencyWeight mode : ℂ) ^ grade •
      ((scaleMultiplier order (frequencyWeight mode) scale : ℂ) • values.1 mode) =
    scaleMultiplier order (frequencyWeight mode) scale •
      ((frequencyWeight mode : ℂ) ^ grade • values.1 mode)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_comm]
  rfl

/-- Near a positive scale one fixed finite Fourier set represents every
scale derivative. Thus support-boundary crossings cause no differentiation gap. -/
theorem fourierScaleDerivative_locally_finite {dimension : ℕ}
    (grade : ℕ) (scale : ℝ) (positive : 0 < scale) (values : JCore (ComplexEuclidean dimension)) :
    ∃ support : Finset FourierMode, ∀ order : ℕ,
      (fun parameter => coreToGrade grade (fourierScaleDerivative order parameter values))
        =ᶠ[nhds scale] fun parameter => ∑ mode ∈ support,
          scaleMultiplier order (frequencyWeight mode) parameter •
            (lp.single 2 mode (coreToGrade grade values mode) : JGrade (ComplexEuclidean dimension) grade) := by
  classical
  let support := (frequency_sublevel_finite (4 * scale)).toFinset
  refine ⟨support, fun order => ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds (show scale ∈ Ioo (scale / 2) (2 * scale) by constructor <;> linarith)]
    with parameter member
  apply fourierScaleDerivative_grade_sum order grade parameter (by linarith [member.1]) values support
  intro mode below
  apply (frequency_sublevel_finite (4 * scale)).mem_toFinset.mpr
  change frequencyWeight mode ≤ 4 * scale
  linarith [member.2]

/-- Genuine differentiation in the complete Fourier grade norm. -/
theorem fourierScaleDerivative_hasDerivAt {dimension : ℕ} (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (values : JCore (ComplexEuclidean dimension)) :
    HasDerivAt (fun parameter => coreToGrade grade (fourierScaleDerivative order parameter values))
      (coreToGrade grade (fourierScaleDerivative (order + 1) scale values)) scale := by
  obtain ⟨support, locallyFinite⟩ := fourierScaleDerivative_locally_finite grade scale positive values
  have differentiated := HasDerivAt.fun_sum (u := support) (fun mode _ =>
    (scaleMultiplier_hasDerivAt order (frequencyWeight mode) scale positive).smul_const
      (lp.single 2 mode (coreToGrade grade values mode) : JGrade (ComplexEuclidean dimension) grade))
  apply (differentiated.congr_of_eventuallyEq (locallyFinite order)).congr_deriv
  exact ((locallyFinite (order + 1)).eq_of_nhds).symm

theorem fourierScaleDerivative_contDiffAt {dimension : ℕ} (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (values : JCore (ComplexEuclidean dimension)) :
    ContDiffAt ℝ ∞ (fun parameter => coreToGrade grade (fourierScaleDerivative order parameter values)) scale := by
  obtain ⟨support, locallyFinite⟩ := fourierScaleDerivative_locally_finite grade scale positive values
  have smoothSum : ContDiffAt ℝ ∞ (fun parameter => ∑ mode ∈ support,
      scaleMultiplier order (frequencyWeight mode) parameter •
        (lp.single 2 mode (coreToGrade grade values mode) : JGrade (ComplexEuclidean dimension) grade)) scale := by
    apply ContDiffAt.sum
    intro mode _
    exact (scaleMultiplier_contDiffAt order (frequencyWeight mode) scale positive).smul contDiffAt_const
  exact smoothSum.congr_of_eventuallyEq (locallyFinite order)

theorem iteratedDeriv_fourierSmoothing {dimension : ℕ} (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (values : JCore (ComplexEuclidean dimension)) :
    iteratedDeriv order (fun parameter => coreToGrade grade (fourierSmoothing parameter values)) scale =
      coreToGrade grade (fourierScaleDerivative order scale values) := by
  induction order generalizing scale with
  | zero => simp only [iteratedDeriv_zero, fourierScaleDerivative_zero]
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => coreToGrade grade (fourierSmoothing parameter values))
        =ᶠ[nhds scale] fun parameter => coreToGrade grade (fourierScaleDerivative order parameter values) := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (fourierScaleDerivative_hasDerivAt order grade scale positive values).deriv

end Grad.SmoothingFamily
