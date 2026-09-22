import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Grad.Constraints

universe u

variable {Source Value : Type u} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
  [ProperSpace Source] [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]

def integralParameterDerivative (function : Source × ℝ → Value) (argument : Source × ℝ) :
    Source →L[ℝ] Value :=
  (fderiv ℝ function argument).comp (ContinuousLinearMap.inl ℝ Source ℝ)

omit [ProperSpace Source] [CompleteSpace Value] in
theorem integralParameterDerivative_smooth {domain : Set Source} (openDomain : IsOpen domain)
    {function : Source × ℝ → Value}
    (smooth : ContDiffOn ℝ ∞ function (domain ×ˢ univ)) :
    ContDiffOn ℝ ∞ (integralParameterDerivative function) (domain ×ˢ univ) := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen (openDomain.prod isOpen_univ)).mp
    smooth).2.clm_comp contDiffOn_const

omit [ProperSpace Source] [CompleteSpace Value] in
theorem integralParameterDerivative_eq {function : Source × ℝ → Value}
    (point : Source) (angle : ℝ) (differentiable : DifferentiableAt ℝ function (point, angle)) :
    integralParameterDerivative function (point, angle) =
      fderiv ℝ (fun source => function (source, angle)) point := by
  have insertion : HasFDerivAt (fun source : Source => (source, angle))
      (ContinuousLinearMap.inl ℝ Source ℝ) point := by
    convert (hasFDerivAt_id point).prodMk (hasFDerivAt_const angle point) using 1 <;>
      ext direction <;> rfl
  exact (differentiable.hasFDerivAt.comp point insertion).fderiv.symm

omit [CompleteSpace Value] in
theorem hasFDerivAt_compactIntegral {domain : Set Source} (openDomain : IsOpen domain)
    {function : Source × ℝ → Value}
    (smooth : ContDiffOn ℝ ∞ function (domain ×ˢ univ))
    (lower upper : ℝ) (point : Source) (pointIn : point ∈ domain) :
    HasFDerivAt (fun source => ∫ angle in Icc lower upper, function (source, angle))
      (∫ angle in Icc lower upper, integralParameterDerivative function (point, angle)) point := by
  have derivativeSmooth := integralParameterDerivative_smooth openDomain smooth
  have sectionContinuous (source : Source) (sourceIn : source ∈ domain) :
      Continuous (fun angle : ℝ => function (source, angle)) :=
    smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨sourceIn, mem_univ _⟩)
  have derivativeContinuous (source : Source) (sourceIn : source ∈ domain) :
      Continuous (fun angle : ℝ => integralParameterDerivative function (source, angle)) :=
    derivativeSmooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨sourceIn, mem_univ _⟩)
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp (openDomain.mem_nhds pointIn)
  have closedInside : Metric.closedBall point (radius / 2) ⊆ domain := by
    intro source sourceIn
    apply ballInside
    exact (Metric.mem_closedBall.mp sourceIn).trans_lt (half_lt_self radiusPositive)
  obtain ⟨bound, boundProperty⟩ :=
    ((isCompact_closedBall point (radius / 2)).prod (isCompact_Icc : IsCompact (Icc lower upper))).exists_bound_of_continuousOn
      (derivativeSmooth.continuousOn.mono (fun argument inside =>
        ⟨closedInside inside.1, mem_univ _⟩))
  let : IsFiniteMeasure (volume.restrict (Icc lower upper)) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball point (radius / 2)) (bound := fun _ => bound)
    (F' := fun source angle => integralParameterDerivative function (source, angle))
    (Metric.ball_mem_nhds point (by linarith))
  · filter_upwards [openDomain.mem_nhds pointIn] with source sourceIn
    exact (sectionContinuous source sourceIn).aestronglyMeasurable
  · exact (sectionContinuous point pointIn).continuousOn.integrableOn_Icc
  · exact (derivativeContinuous point pointIn).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with angle angleIn
    intro source sourceIn
    exact boundProperty (source, angle) ⟨Metric.ball_subset_closedBall sourceIn, angleIn⟩
  · exact integrable_const bound
  · filter_upwards with angle
    intro source sourceIn
    have sourceDomain := closedInside (Metric.ball_subset_closedBall sourceIn)
    have outer := (smooth.contDiffAt ((openDomain.prod isOpen_univ).mem_nhds
      (show (source, angle) ∈ domain ×ˢ (univ : Set ℝ) from ⟨sourceDomain, mem_univ _⟩))).differentiableAt (by simp)
    have insertion : HasFDerivAt (fun value : Source => (value, angle))
        (ContinuousLinearMap.inl ℝ Source ℝ) source := by
      convert (hasFDerivAt_id source).prodMk (hasFDerivAt_const angle source) using 1 <;>
        ext direction <;> rfl
    exact outer.hasFDerivAt.comp source insertion

theorem contDiffOn_compactIntegral_nat (order : ℕ)
    {domain : Set Source} (openDomain : IsOpen domain)
    {function : Source × ℝ → Value}
    (smooth : ContDiffOn ℝ ∞ function (domain ×ˢ univ)) (lower upper : ℝ) :
    ContDiffOn ℝ order (fun source => ∫ angle in Icc lower upper, function (source, angle)) domain := by
  induction order generalizing Value with
  | zero =>
    simp only [Nat.cast_zero, contDiffOn_zero]
    intro point pointIn
    exact (hasFDerivAt_compactIntegral openDomain smooth lower upper point pointIn).continuousAt.continuousWithinAt
  | succ order inductionHypothesis =>
    rw [show ((order + 1 : ℕ) : WithTop ℕ∞) = (order : WithTop ℕ∞) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen openDomain]
    refine ⟨?_, ?_, ?_⟩
    · intro point pointIn
      exact (hasFDerivAt_compactIntegral openDomain smooth lower upper point pointIn).differentiableAt.differentiableWithinAt
    · intro impossible
      simp at impossible
    · have nextSmooth := inductionHypothesis
        (integralParameterDerivative_smooth openDomain smooth)
      exact nextSmooth.congr (fun point pointIn =>
        (hasFDerivAt_compactIntegral openDomain smooth lower upper point pointIn).fderiv)

/-- All-order differentiation under a compact real parameter integral on
an open Euclidean domain. Only local compact bounds are used. -/
theorem contDiffOn_compactIntegral {domain : Set Source} (openDomain : IsOpen domain)
    {function : Source × ℝ → Value}
    (smooth : ContDiffOn ℝ ∞ function (domain ×ˢ univ)) (lower upper : ℝ) :
    ContDiffOn ℝ ∞ (fun source => ∫ angle in Icc lower upper, function (source, angle)) domain := by
  rw [contDiffOn_infty]
  intro order
  exact contDiffOn_compactIntegral_nat order openDomain smooth lower upper

end Grad.Constraints
