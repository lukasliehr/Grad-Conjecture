import BT11AngularJets

noncomputable section

open Set
open scoped ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

def radialField {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (point : ℝ × ℝ) : Value := fderiv ℝ field point (1, 0)

theorem radialField_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (radialField field) := by
  exact (contDiff_infty_iff_fderiv.mp smooth).2.clm_apply contDiff_const

theorem radialField_hasDerivAt {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) (time angle : ℝ) :
    HasDerivAt (fun radial : ℝ => field (radial, angle)) (radialField field (time, angle)) time := by
  exact ((smooth.differentiable (by simp)) (time, angle)).hasFDerivAt.comp_hasDerivAt time
    ((hasDerivAt_id time).prodMk (hasDerivAt_const time angle))

theorem radialField_periodic {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (periodic : Function.Periodic field (0, 2 * Real.pi)) :
    Function.Periodic (radialField field) (0, 2 * Real.pi) := by
  intro point
  have equality := congrArg (fun tensor => tensor (fun _ : Fin 1 => ((1, 0) : ℝ × ℝ)))
    (periodic_iteratedFDeriv 1 field periodic point)
  simpa only [iteratedFDeriv_one_apply, radialField] using equality

theorem radialField_iteratedFDeriv_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (radialField field) point‖ ≤ ‖iteratedFDeriv ℝ (order + 1) field point‖ := by
  let evaluation : ((ℝ × ℝ) →L[ℝ] Value) →L[ℝ] Value :=
    ContinuousLinearMap.apply ℝ Value ((1, 0) : ℝ × ℝ)
  have evaluationBound : ‖evaluation‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro linear
    simpa [evaluation, Prod.norm_def] using linear.le_opNorm ((1, 0) : ℝ × ℝ)
  change ‖iteratedFDeriv ℝ order (evaluation ∘ fderiv ℝ field) point‖ ≤ _
  rw [evaluation.iteratedFDeriv_comp_left (contDiff_infty_iff_fderiv.mp smooth).2.contDiffAt
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply (evaluation.norm_compContinuousMultilinearMap_le _).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_of_le_one_left (norm_nonneg _) evaluationBound

theorem radialAngularJet_norm_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ℝ × ℝ → Value) (smooth : ContDiff ℝ ∞ field) (order : ℕ) (point : ℝ × ℝ) :
    ‖angularJet order (radialField field) point‖ ≤ ‖iteratedFDeriv ℝ (order + 1) field point‖ :=
  (angularJet_norm_le order (radialField field) point).trans
    (radialField_iteratedFDeriv_norm_le field smooth order point)

theorem collarField_periodic {Value : Type*} [SMul ℝ Value] (field : SpatialPlane → Value) :
    Function.Periodic (collarField field) (0, 2 * Real.pi) := by
  intro point
  have geometry : collarPlane (point + (0, 2 * Real.pi)) = collarPlane point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [collarPlane]
  simp only [collarField, geometry, collarCutoff, Prod.fst_add, add_zero]

end Grad.BoundaryTrace
