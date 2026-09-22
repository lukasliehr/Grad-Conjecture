import CompactSmoothIntegral
import SP1Words
import COR01Proof

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.RepresentedKernel.SpatialProduct

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]

def sliceDirectionDerivative (direction : Fin 2) (field : SpatialPlane × ℝ → Value)
    (argument : SpatialPlane × ℝ) : Value :=
  integralParameterDerivative field argument (spatialBasis direction)

def sliceListDerivative (word : List (Fin 2)) (field : SpatialPlane × ℝ → Value) :
    SpatialPlane × ℝ → Value := word.foldr sliceDirectionDerivative field

omit [CompleteSpace Value] in
theorem sliceDirectionDerivative_smooth (direction : Fin 2)
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (sliceDirectionDerivative direction field) := by
  have partialSmooth := integralParameterDerivative_smooth
    (domain := (univ : Set SpatialPlane)) isOpen_univ smooth.contDiffOn
  have wholeSmooth : ContDiff ℝ ∞ (integralParameterDerivative field) := by
    rw [← contDiffOn_univ]
    simpa only [univ_prod_univ] using partialSmooth
  exact wholeSmooth.clm_apply contDiff_const

omit [CompleteSpace Value] in
theorem sliceListDerivative_smooth (word : List (Fin 2))
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (sliceListDerivative word field) := by
  induction word with
  | nil => exact smooth
  | cons direction rest inductionHypothesis =>
    exact sliceDirectionDerivative_smooth direction inductionHypothesis

omit [CompleteSpace Value] in
theorem sliceDirectionDerivative_eq (direction : Fin 2)
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (point : SpatialPlane) (angle : ℝ) :
    sliceDirectionDerivative direction field (point, angle) =
      directionDerivative direction (fun source => field (source, angle)) point := by
  unfold sliceDirectionDerivative
  rw [integralParameterDerivative_eq point angle (smooth.differentiable (by simp) (point, angle))]
  rfl

omit [CompleteSpace Value] in
theorem sliceListDerivative_eq (word : List (Fin 2))
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (angle : ℝ) :
    (fun point => sliceListDerivative word field (point, angle)) =
      listDerivative word (fun point => field (point, angle)) := by
  induction word with
  | nil => rfl
  | cons direction rest inductionHypothesis =>
    funext point
    change sliceDirectionDerivative direction (sliceListDerivative rest field) (point, angle) = _
    rw [sliceDirectionDerivative_eq direction (sliceListDerivative_smooth rest smooth)]
    rw [inductionHypothesis]
    rfl

omit [CompleteSpace Value] in
theorem directionDerivative_compactIntegral (direction : Fin 2)
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (lower upper : ℝ) :
    directionDerivative direction
        (fun point => ∫ angle in Icc lower upper, field (point, angle)) =
      fun point => ∫ angle in Icc lower upper,
        sliceDirectionDerivative direction field (point, angle) := by
  funext point
  have derivative := hasFDerivAt_compactIntegral
    (domain := (univ : Set SpatialPlane)) isOpen_univ smooth.contDiffOn lower upper point (mem_univ _)
  have partialSmooth := integralParameterDerivative_smooth
    (domain := (univ : Set SpatialPlane)) isOpen_univ smooth.contDiffOn
  have partialContinuous : Continuous (fun angle => integralParameterDerivative field (point, angle)) :=
    partialSmooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨mem_univ _, mem_univ _⟩)
  rw [directionDerivative, derivative.fderiv,
    ContinuousLinearMap.integral_apply partialContinuous.continuousOn.integrableOn_Icc]
  rfl

omit [CompleteSpace Value] in
theorem listDerivative_compactIntegral (word : List (Fin 2))
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (lower upper : ℝ) :
    listDerivative word (fun point => ∫ angle in Icc lower upper, field (point, angle)) =
      fun point => ∫ angle in Icc lower upper, sliceListDerivative word field (point, angle) := by
  induction word with
  | nil => rfl
  | cons direction rest inductionHypothesis =>
    change directionDerivative direction
      (listDerivative rest (fun point => ∫ angle in Icc lower upper, field (point, angle))) = _
    rw [inductionHypothesis]
    exact directionDerivative_compactIntegral direction (sliceListDerivative_smooth rest smooth) lower upper

theorem cartesianDerivative_compactIntegral (order : ℕ) (word : CartesianWord order)
    {field : SpatialPlane × ℝ → Value} (smooth : ContDiff ℝ ∞ field)
    (lower upper : ℝ) (point : SpatialPlane) :
    cartesianDerivative order word
        (fun source => ∫ angle in Icc lower upper, field (source, angle)) point =
      ∫ angle in Icc lower upper,
        cartesianDerivative order word (fun source => field (source, angle)) point := by
  have integralSmooth : ContDiff ℝ ∞
      (fun source => ∫ angle in Icc lower upper, field (source, angle)) :=
    contDiffOn_univ.mp (contDiffOn_compactIntegral isOpen_univ smooth.contDiffOn lower upper)
  change wordDerivative order word
      (fun source => ∫ angle in Icc lower upper, field (source, angle)) point = _
  rw [← listDerivative_ofFn isOpen_univ order word integralSmooth.contDiffOn (mem_univ point)]
  rw [listDerivative_compactIntegral _ smooth]
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  have sectionSmooth : ContDiff ℝ ∞ (fun source => field (source, angle)) :=
    smooth.comp (contDiff_id.prodMk contDiff_const)
  exact (congrFun (sliceListDerivative_eq (List.ofFn word) smooth angle) point).trans
    (listDerivative_ofFn isOpen_univ order word sectionSmooth.contDiffOn (mem_univ point))

end Grad.Constraints
