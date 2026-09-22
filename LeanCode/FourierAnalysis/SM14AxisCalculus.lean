import SM13AxisSmoothing

noncomputable section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothingFamily

open Grad.CartesianState Grad.ClosedJets

theorem axisScaleDerivative_grade_sum {dimension : ℕ} (width : ℝ)
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale)
    (values : AxisCore width (ComplexEuclidean dimension)) (support : Finset ℤ)
    (covers : ∀ cell, cellFrequency cell ≤ 2 * scale → cell ∈ support) :
    axisToGrade width grade (axisScaleDerivative width order scale values) =
      ∑ cell ∈ support, scaleMultiplier order (cellFrequency cell) scale •
        (lp.single 2 cell (axisToGrade width grade values cell) : TGrade width (ComplexEuclidean dimension) grade) := by
  have sumIdentity := lp.hasSum_single (p := 2) (by norm_num)
    (axisToGrade width grade (axisScaleDerivative width order scale values))
  have finiteSum : HasSum (fun cell =>
      lp.single 2 cell (axisToGrade width grade (axisScaleDerivative width order scale values) cell))
      (∑ cell ∈ support, lp.single 2 cell
        (axisToGrade width grade (axisScaleDerivative width order scale values) cell)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro cell outside
    have above : 2 * scale < cellFrequency cell := lt_of_not_ge (fun below => outside (covers cell below))
    have zeroMultiplier := scaleMultiplier_zero_above order (cellFrequency cell) scale positive above
    have coordinateZero : axisToGrade width grade (axisScaleDerivative width order scale values) cell = 0 := by
      change (axisWeight width grade cell : ℂ) •
        ((scaleMultiplier order (cellFrequency cell) scale : ℂ) • values.1 cell) = 0
      rw [zeroMultiplier, Complex.ofReal_zero, zero_smul, smul_zero]
    rw [coordinateZero, lp.single_zero]
  rw [sumIdentity.unique finiteSum]
  apply Finset.sum_congr rfl
  intro cell _
  rw [← lp.single_smul]
  congr 1
  change (axisWeight width grade cell : ℂ) •
      ((scaleMultiplier order (cellFrequency cell) scale : ℂ) • values.1 cell) =
    scaleMultiplier order (cellFrequency cell) scale • ((axisWeight width grade cell : ℂ) • values.1 cell)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_comm]
  rfl

theorem axisScaleDerivative_locally_finite {dimension : ℕ} (width : ℝ)
    (grade : ℕ) (scale : ℝ) (positive : 0 < scale) (values : AxisCore width (ComplexEuclidean dimension)) :
    ∃ support : Finset ℤ, ∀ order : ℕ,
      (fun parameter => axisToGrade width grade (axisScaleDerivative width order parameter values))
        =ᶠ[nhds scale] fun parameter => ∑ cell ∈ support,
          scaleMultiplier order (cellFrequency cell) parameter •
            (lp.single 2 cell (axisToGrade width grade values cell) : TGrade width (ComplexEuclidean dimension) grade) := by
  classical
  let support := (cellFrequency_sublevel_finite (4 * scale)).toFinset
  refine ⟨support, fun order => ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds (show scale ∈ Ioo (scale / 2) (2 * scale) by constructor <;> linarith)]
    with parameter member
  apply axisScaleDerivative_grade_sum width order grade parameter (by linarith [member.1]) values support
  intro cell below
  apply (cellFrequency_sublevel_finite (4 * scale)).mem_toFinset.mpr
  change cellFrequency cell ≤ 4 * scale
  linarith [member.2]

theorem axisScaleDerivative_hasDerivAt {dimension : ℕ} (width : ℝ) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (values : AxisCore width (ComplexEuclidean dimension)) :
    HasDerivAt (fun parameter => axisToGrade width grade (axisScaleDerivative width order parameter values))
      (axisToGrade width grade (axisScaleDerivative width (order + 1) scale values)) scale := by
  obtain ⟨support, locallyFinite⟩ := axisScaleDerivative_locally_finite width grade scale positive values
  have differentiated := HasDerivAt.fun_sum (u := support) (fun cell _ =>
    (scaleMultiplier_hasDerivAt order (cellFrequency cell) scale positive).smul_const
      (lp.single 2 cell (axisToGrade width grade values cell) : TGrade width (ComplexEuclidean dimension) grade))
  apply (differentiated.congr_of_eventuallyEq (locallyFinite order)).congr_deriv
  exact ((locallyFinite (order + 1)).eq_of_nhds).symm

theorem axisScaleDerivative_contDiffAt {dimension : ℕ} (width : ℝ) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (values : AxisCore width (ComplexEuclidean dimension)) :
    ContDiffAt ℝ ∞ (fun parameter => axisToGrade width grade (axisScaleDerivative width order parameter values)) scale := by
  obtain ⟨support, locallyFinite⟩ := axisScaleDerivative_locally_finite width grade scale positive values
  have smoothSum : ContDiffAt ℝ ∞ (fun parameter => ∑ cell ∈ support,
      scaleMultiplier order (cellFrequency cell) parameter •
        (lp.single 2 cell (axisToGrade width grade values cell) : TGrade width (ComplexEuclidean dimension) grade)) scale := by
    apply ContDiffAt.sum
    intro cell _
    exact (scaleMultiplier_contDiffAt order (cellFrequency cell) scale positive).smul contDiffAt_const
  exact smoothSum.congr_of_eventuallyEq (locallyFinite order)

theorem iteratedDeriv_axisSmoothing {dimension : ℕ} (width : ℝ) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (values : AxisCore width (ComplexEuclidean dimension)) :
    iteratedDeriv order (fun parameter => axisToGrade width grade (axisSmoothing width parameter values)) scale =
      axisToGrade width grade (axisScaleDerivative width order scale values) := by
  induction order generalizing scale with
  | zero => simp only [iteratedDeriv_zero, axisScaleDerivative_zero]
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => axisToGrade width grade (axisSmoothing width parameter values))
        =ᶠ[nhds scale] fun parameter => axisToGrade width grade (axisScaleDerivative width order parameter values) := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (axisScaleDerivative_hasDerivAt width order grade scale positive values).deriv

end Grad.SmoothingFamily
