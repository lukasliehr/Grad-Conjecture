import SP1Positions

noncomputable section

open Grad.PDEBootstrap
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel.SpatialProduct

theorem bilinear_derivative {First Second Third : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    (bilinearMap : First →L[ℝ] Second →L[ℝ] Third)
    {first : Spatial → First} {second : Spatial → Second} {point : Spatial}
    {firstDerivative : Spatial →L[ℝ] First} {secondDerivative : Spatial →L[ℝ] Second}
    (firstDifferentiable : HasFDerivAt first firstDerivative point)
    (secondDifferentiable : HasFDerivAt second secondDerivative point) (direction : Spatial) :
    fderiv ℝ (fun source => bilinearMap (first source) (second source)) point direction =
      bilinearMap (firstDerivative direction) (second point) +
        bilinearMap (first point) (secondDerivative direction) := by
  rw [(bilinearMap.hasFDerivAt_of_bilinear firstDifferentiable secondDifferentiable).fderiv]
  simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, add_comm]

theorem differentiable_iterated {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {function : Spatial → Value} {point : Spatial} (smooth : ContDiffAt ℝ ∞ function point)
    (rank : ℕ) : DifferentiableAt ℝ (iteratedFDeriv ℝ rank function) point :=
  smooth.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl rank)

theorem differentiable_selected {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {function : Spatial → Value} {point : Spatial} (smooth : ContDiffAt ℝ ∞ function point)
    {rank : ℕ} (directions : Fin rank → Spatial) (selected : Finset (Fin rank)) :
    DifferentiableAt ℝ (fun source => selectedDerivative directions selected function source) point :=
  (differentiable_iterated smooth selected.card).continuousMultilinear_apply_const _

theorem fderiv_selected {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {function : Spatial → Value} {point : Spatial} (smooth : ContDiffAt ℝ ∞ function point)
    {rank : ℕ} (directions : Fin (rank + 1) → Spatial) (selected : Finset (Fin rank)) :
    fderiv ℝ (fun source => selectedDerivative (Fin.tail directions) selected function source)
      point (directions 0) = selectedDerivative directions (headSelected selected) function point := by
  rw [selectedDerivative_head]
  simpa only [Fin.tail_cons, Fin.cons_zero, selectedDerivative, Fin.tail] using
    (differentiable_iterated smooth selected.card).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons (directions 0)
        (fun position => directions (selected.orderEmbOfFin rfl position).succ)) |>.symm

theorem bilinear : BilinearGoal := by
  intro First Second Third _ _ _ _ _ _ bilinearMap domain openDomain first second firstSmooth secondSmooth
  have productSmooth : ContDiffOn ℝ ∞ (fun source => bilinearMap (first source) (second source)) domain :=
    bilinearMap.isBoundedBilinearMap.contDiff.comp₂_contDiffOn firstSmooth secondSmooth
  intro rank
  induction rank with
  | zero =>
    intro directions point _
    rw [Fintype.sum_unique]
    rfl
  | succ rank inductionHypothesis =>
    intro directions point inside
    have firstLocal := firstSmooth.contDiffAt (openDomain.mem_nhds inside)
    have secondLocal := secondSmooth.contDiffAt (openDomain.mem_nhds inside)
    have productLocal := productSmooth.contDiffAt (openDomain.mem_nhds inside)
    have localEquality :
        (fun source => iteratedFDeriv ℝ rank (fun source => bilinearMap (first source) (second source))
          source (Fin.tail directions)) =ᶠ[𝓝 point]
        (fun source => ∑ selected : Finset (Fin rank),
          bilinearMap (selectedDerivative (Fin.tail directions) selected first source)
            (selectedDerivative (Fin.tail directions) selectedᶜ second source)) := by
      filter_upwards [openDomain.mem_nhds inside] with source sourceInside
      exact inductionHypothesis (Fin.tail directions) source sourceInside
    rw [(differentiable_iterated productLocal rank).iteratedFDeriv_succ_apply_left',
      localEquality.fderiv_eq]
    rw [fderiv_fun_sum (fun selected _ =>
      (bilinearMap.hasFDerivAt_of_bilinear
        (differentiable_selected firstLocal (Fin.tail directions) selected).hasFDerivAt
        (differentiable_selected secondLocal (Fin.tail directions) selectedᶜ).hasFDerivAt).differentiableAt)]
    rw [sum_allocations, ← Finset.sum_add_distrib]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro selected _
    rw [bilinearMap.fderiv_of_bilinear
      (differentiable_selected firstLocal (Fin.tail directions) selected)
      (differentiable_selected secondLocal (Fin.tail directions) selectedᶜ)]
    simp only [add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      fderiv_selected firstLocal, fderiv_selected secondLocal,
      lift_compl, head_compl, selectedDerivative_lift]

end Grad.RepresentedKernel.SpatialProduct
