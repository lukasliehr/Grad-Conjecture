import CompactIntegralDerivatives
import RadialDilationJet

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.Constraints Grad.RepresentedKernel.SpatialProduct

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]

omit [CompleteSpace Value] in
theorem parameterDerivative_smooth {field : SpatialPlane × ℝ → Value}
    (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (integralParameterDerivative field) := by
  rw [← contDiffOn_univ]
  simpa only [univ_prod_univ] using
    integralParameterDerivative_smooth (domain := (univ : Set SpatialPlane)) isOpen_univ smooth.contDiffOn

omit [CompleteSpace Value] in
/-- Compact integration with a continuous scalar kernel. Smoothness is only
required in the field, not in the logarithmic kernel at its endpoint. -/
theorem hasFDerivAt_weightedIntegral {field : SpatialPlane × ℝ → Value}
    (smooth : ContDiff ℝ ∞ field) (weight : ℝ → ℝ) (weightContinuous : Continuous weight)
    (lower upper : ℝ) (point : SpatialPlane) :
    HasFDerivAt (fun source => ∫ scale in Icc lower upper, weight scale • field (source, scale))
      (∫ scale in Icc lower upper, weight scale • integralParameterDerivative field (point, scale)) point := by
  have partialSmooth := parameterDerivative_smooth smooth
  have jointContinuous : Continuous (fun argument : SpatialPlane × ℝ =>
      weight argument.2 • integralParameterDerivative field argument) :=
    (weightContinuous.comp continuous_snd).smul partialSmooth.continuous
  obtain ⟨bound, boundProperty⟩ :=
    ((isCompact_closedBall point (1 : ℝ)).prod (isCompact_Icc : IsCompact (Icc lower upper))).exists_bound_of_continuousOn
      jointContinuous.continuousOn
  let : IsFiniteMeasure (volume.restrict (Icc lower upper)) := by
    rw [isFiniteMeasure_restrict]
    exact isCompact_Icc.measure_ne_top
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball point 1) (bound := fun _ => bound)
    (F' := fun source scale => weight scale • integralParameterDerivative field (source, scale))
    (Metric.ball_mem_nhds point zero_lt_one)
  · filter_upwards with source
    exact (weightContinuous.smul (smooth.continuous.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact (weightContinuous.smul (smooth.continuous.comp
      (continuous_const.prodMk continuous_id))).continuousOn.integrableOn_Icc
  · exact (jointContinuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with scale scaleIn
    intro source sourceIn
    exact boundProperty (source, scale) ⟨Metric.ball_subset_closedBall sourceIn, scaleIn⟩
  · exact integrable_const bound
  · filter_upwards with scale
    intro source _
    have sectionDerivative : HasFDerivAt (fun value : SpatialPlane => field (value, scale))
        (integralParameterDerivative field (source, scale)) source := by
      rw [integralParameterDerivative_eq source scale (smooth.differentiable (by simp) _)]
      exact ((smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) source).hasFDerivAt
    exact sectionDerivative.const_smul (weight scale)

theorem weightedIntegral_contDiff_nat (order : ℕ) {field : SpatialPlane × ℝ → Value}
    (smooth : ContDiff ℝ ∞ field) (weight : ℝ → ℝ) (weightContinuous : Continuous weight)
    (lower upper : ℝ) :
    ContDiff ℝ order (fun source => ∫ scale in Icc lower upper, weight scale • field (source, scale)) := by
  induction order generalizing Value with
  | zero =>
    simp only [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun point =>
      (hasFDerivAt_weightedIntegral smooth weight weightContinuous lower upper point).continuousAt)
  | succ order inductionHypothesis =>
    rw [show ((order + 1 : ℕ) : WithTop ℕ∞) = (order : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨?_, ?_, ?_⟩
    · intro point
      exact (hasFDerivAt_weightedIntegral smooth weight weightContinuous lower upper point).differentiableAt
    · intro impossible
      simp at impossible
    · have derivativeEquality :
          fderiv ℝ (fun source => ∫ scale in Icc lower upper, weight scale • field (source, scale)) =
            fun source => ∫ scale in Icc lower upper,
              weight scale • integralParameterDerivative field (source, scale) := by
        funext source
        exact (hasFDerivAt_weightedIntegral smooth weight weightContinuous lower upper source).fderiv
      rw [derivativeEquality]
      exact inductionHypothesis (parameterDerivative_smooth smooth)

theorem weightedIntegral_contDiff {field : SpatialPlane × ℝ → Value}
    (smooth : ContDiff ℝ ∞ field) (weight : ℝ → ℝ) (weightContinuous : Continuous weight)
    (lower upper : ℝ) :
    ContDiff ℝ ∞ (fun source => ∫ scale in Icc lower upper, weight scale • field (source, scale)) := by
  rw [contDiff_infty]
  intro order
  exact weightedIntegral_contDiff_nat order smooth weight weightContinuous lower upper

omit [CompleteSpace Value] in
theorem directionDerivative_weightedIntegral (direction : Fin 2)
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (weight : ℝ → ℝ) (weightContinuous : Continuous weight) (lower upper : ℝ) :
    directionDerivative direction
        (fun point => ∫ scale in Icc lower upper, weight scale • field (point, scale)) =
      fun point => ∫ scale in Icc lower upper,
        weight scale • sliceDirectionDerivative direction field (point, scale) := by
  funext point
  have partialContinuous : Continuous (fun scale =>
      weight scale • integralParameterDerivative field (point, scale)) :=
    weightContinuous.smul ((parameterDerivative_smooth smooth).continuous.comp
      (continuous_const.prodMk continuous_id))
  rw [directionDerivative,
    (hasFDerivAt_weightedIntegral smooth weight weightContinuous lower upper point).fderiv,
    ContinuousLinearMap.integral_apply partialContinuous.continuousOn.integrableOn_Icc]
  rfl

omit [CompleteSpace Value] in
theorem listDerivative_weightedIntegral (word : List (Fin 2))
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (weight : ℝ → ℝ) (weightContinuous : Continuous weight) (lower upper : ℝ) :
    listDerivative word (fun point => ∫ scale in Icc lower upper, weight scale • field (point, scale)) =
      fun point => ∫ scale in Icc lower upper, weight scale • sliceListDerivative word field (point, scale) := by
  induction word with
  | nil => rfl
  | cons direction rest inductionHypothesis =>
    change directionDerivative direction
      (listDerivative rest (fun point => ∫ scale in Icc lower upper, weight scale • field (point, scale))) = _
    rw [inductionHypothesis]
    exact directionDerivative_weightedIntegral direction (sliceListDerivative_smooth rest smooth)
      weight weightContinuous lower upper

theorem cartesianDerivative_weightedIntegral (order : ℕ) (word : CartesianWord order)
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (weight : ℝ → ℝ) (weightContinuous : Continuous weight)
    (lower upper : ℝ) (point : SpatialPlane) :
    cartesianDerivative order word
        (fun source => ∫ scale in Icc lower upper, weight scale • field (source, scale)) point =
      ∫ scale in Icc lower upper,
        weight scale • cartesianDerivative order word (fun source => field (source, scale)) point := by
  have integralSmooth := weightedIntegral_contDiff smooth weight weightContinuous lower upper
  change wordDerivative order word _ point = _
  rw [← listDerivative_ofFn isOpen_univ order word integralSmooth.contDiffOn (mem_univ point),
    listDerivative_weightedIntegral _ smooth weight weightContinuous lower upper]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale _
  have sectionSmooth : ContDiff ℝ ∞ (fun source => field (source, scale)) :=
    smooth.comp (contDiff_id.prodMk contDiff_const)
  exact congrArg (fun value => weight scale • value)
    ((congrFun (sliceListDerivative_eq (List.ofFn word) smooth scale) point).trans
      (listDerivative_ofFn isOpen_univ order word sectionSmooth.contDiffOn (mem_univ point)))

end Grad.NonlinearRadial
