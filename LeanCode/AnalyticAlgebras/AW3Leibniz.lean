import AW3Exponential
import SP1Bilinear

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers
open scoped ContDiff BigOperators Topology

namespace Grad.AnalyticWeights.Higher

universe valueUniverse firstUniverse secondUniverse thirdUniverse

namespace LocalLeibniz

theorem differentiable_iterated_finite {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {function : Spatial → Value} {point : Spatial} {order : ℕ}
    (smooth : ContDiffAt ℝ order function point) (rank : ℕ) (strict : rank < order) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ rank function) point :=
  smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast strict)

theorem selected_card_le {rank : ℕ} (selected : Finset (Fin rank)) : selected.card ≤ rank := by
  simpa using Finset.card_le_card (Finset.subset_univ selected)

theorem differentiable_selected_finite {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {function : Spatial → Value} {point : Spatial} {order rank : ℕ}
    (smooth : ContDiffAt ℝ order function point) (strict : rank < order)
    (directions : Fin rank → Spatial) (selected : Finset (Fin rank)) :
    DifferentiableAt ℝ (fun source =>
      Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions selected function source) point :=
  (differentiable_iterated_finite smooth selected.card (by
    exact (selected_card_le selected).trans_lt strict)).continuousMultilinear_apply_const _

theorem fderiv_selected_finite {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {function : Spatial → Value} {point : Spatial} {order rank : ℕ}
    (smooth : ContDiffAt ℝ order function point) (strict : rank < order)
    (directions : Fin (rank + 1) → Spatial) (selected : Finset (Fin rank)) :
    fderiv ℝ (fun source => Grad.RepresentedKernel.SpatialProduct.selectedDerivative
      (Fin.tail directions) selected function source) point (directions 0) =
        Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
          (Grad.RepresentedKernel.SpatialProduct.headSelected selected) function point := by
  rw [Grad.RepresentedKernel.SpatialProduct.selectedDerivative_head]
  simpa only [Fin.tail_cons, Fin.cons_zero,
    Grad.RepresentedKernel.SpatialProduct.selectedDerivative, Fin.tail] using
    (differentiable_iterated_finite smooth selected.card
      ((selected_card_le selected).trans_lt strict)).iteratedFDeriv_succ_apply_left'
        (m := Fin.cons (directions 0)
          (fun position => directions (selected.orderEmbOfFin rfl position).succ)) |>.symm

theorem bilinear_finite {First Second Third : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    (bilinearMap : First →L[ℝ] Second →L[ℝ] Third) (order : ℕ)
    (domain : Set Spatial) (openDomain : IsOpen domain)
    (first : Spatial → First) (second : Spatial → Second)
    (firstSmooth : ContDiffOn ℝ order first domain)
    (secondSmooth : ContDiffOn ℝ order second domain) :
    ∀ (rank : ℕ), rank ≤ order → ∀ (directions : Fin rank → Spatial)
      (point : Spatial), point ∈ domain →
      iteratedFDeriv ℝ rank (fun source => bilinearMap (first source) (second source)) point directions =
        ∑ selected : Finset (Fin rank),
          bilinearMap
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions selected first point)
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions selectedᶜ second point) := by
  have productSmooth : ContDiffOn ℝ order
      (fun source => bilinearMap (first source) (second source)) domain :=
    bilinearMap.isBoundedBilinearMap.contDiff.comp₂_contDiffOn firstSmooth secondSmooth
  intro rank rankBound
  induction rank with
  | zero =>
    intro directions point _
    rw [Fintype.sum_unique]
    rfl
  | succ rank inductionHypothesis =>
    intro directions point inside
    have strict : rank < order := by omega
    have firstLocal := firstSmooth.contDiffAt (openDomain.mem_nhds inside)
    have secondLocal := secondSmooth.contDiffAt (openDomain.mem_nhds inside)
    have productLocal := productSmooth.contDiffAt (openDomain.mem_nhds inside)
    have localEquality :
        (fun source => iteratedFDeriv ℝ rank
          (fun source => bilinearMap (first source) (second source)) source (Fin.tail directions)) =ᶠ[𝓝 point]
        (fun source => ∑ selected : Finset (Fin rank),
          bilinearMap
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative
              (Fin.tail directions) selected first source)
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative
              (Fin.tail directions) selectedᶜ second source)) := by
      filter_upwards [openDomain.mem_nhds inside] with source sourceInside
      exact inductionHypothesis (by omega) (Fin.tail directions) source sourceInside
    rw [(differentiable_iterated_finite productLocal rank strict).iteratedFDeriv_succ_apply_left',
      localEquality.fderiv_eq]
    rw [fderiv_fun_sum (fun selected _ =>
      (bilinearMap.hasFDerivAt_of_bilinear
        (differentiable_selected_finite firstLocal strict (Fin.tail directions) selected).hasFDerivAt
        (differentiable_selected_finite secondLocal strict (Fin.tail directions) selectedᶜ).hasFDerivAt).differentiableAt)]
    rw [Grad.RepresentedKernel.SpatialProduct.sum_allocations, ← Finset.sum_add_distrib]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro selected _
    rw [bilinearMap.fderiv_of_bilinear
      (differentiable_selected_finite firstLocal strict (Fin.tail directions) selected)
      (differentiable_selected_finite secondLocal strict (Fin.tail directions) selectedᶜ)]
    simp only [add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply,
      fderiv_selected_finite firstLocal strict, fderiv_selected_finite secondLocal strict,
      Grad.RepresentedKernel.SpatialProduct.lift_compl,
      Grad.RepresentedKernel.SpatialProduct.head_compl,
      Grad.RepresentedKernel.SpatialProduct.selectedDerivative_lift]

theorem bilinear_at {First Second Third : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    (bilinearMap : First →L[ℝ] Second →L[ℝ] Third)
    (first : Spatial → First) (second : Spatial → Second) (point : Spatial)
    (firstSmooth : ContDiffAt ℝ ∞ first point) (secondSmooth : ContDiffAt ℝ ∞ second point)
    (rank : ℕ) (directions : Fin rank → Spatial) :
    iteratedFDeriv ℝ rank (fun source => bilinearMap (first source) (second source)) point directions =
      ∑ selected : Finset (Fin rank),
        bilinearMap
          (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions selected first point)
          (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions selectedᶜ second point) := by
  let order := rank + 1
  have firstFinite : ContDiffAt ℝ order first point := firstSmooth.of_le (by exact_mod_cast le_top)
  have secondFinite : ContDiffAt ℝ order second point := secondSmooth.of_le (by exact_mod_cast le_top)
  rcases firstFinite.contDiffOn le_rfl (by simp) with ⟨firstSet, firstNeighborhood, firstOn⟩
  rcases secondFinite.contDiffOn le_rfl (by simp) with ⟨secondSet, secondNeighborhood, secondOn⟩
  rcases mem_nhds_iff.mp firstNeighborhood with
    ⟨firstOpen, firstSubset, firstOpenDomain, pointFirst⟩
  rcases mem_nhds_iff.mp secondNeighborhood with
    ⟨secondOpen, secondSubset, secondOpenDomain, pointSecond⟩
  let domain := firstOpen ∩ secondOpen
  have openDomain : IsOpen domain := firstOpenDomain.inter secondOpenDomain
  have pointInside : point ∈ domain := ⟨pointFirst, pointSecond⟩
  have firstSmoothOn : ContDiffOn ℝ order first domain :=
    firstOn.mono (Set.inter_subset_left.trans firstSubset)
  have secondSmoothOn : ContDiffOn ℝ order second domain :=
    secondOn.mono (Set.inter_subset_right.trans secondSubset)
  exact bilinear_finite bilinearMap order domain openDomain first second firstSmoothOn secondSmoothOn
    rank (by omega) directions point pointInside

def allocationHeadEquiv (rank : ℕ) :
    (Fin (rank + 1) → Fin 3) ≃ Fin 3 × (Fin rank → Fin 3) where
  toFun allocation := (allocation 0, Fin.tail allocation)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv allocation := Fin.cons_self_tail allocation
  right_inv pair := by
    rcases pair with ⟨label, allocation⟩
    simp only [Fin.cons_zero, Fin.tail_cons]

theorem sum_allocations_three {Result : Type*} [AddCommMonoid Result] (rank : ℕ)
    (function : (Fin (rank + 1) → Fin 3) → Result) :
    ∑ allocation, function allocation =
      (∑ allocation : Fin rank → Fin 3, function (Fin.cons 0 allocation)) +
      (∑ allocation : Fin rank → Fin 3, function (Fin.cons 1 allocation)) +
      ∑ allocation : Fin rank → Fin 3, function (Fin.cons 2 allocation) := by
  calc
    _ = ∑ pair : Fin 3 × (Fin rank → Fin 3),
        function ((allocationHeadEquiv rank).symm pair) :=
      Fintype.sum_equiv (allocationHeadEquiv rank) function _ (fun allocation =>
        congrArg function ((allocationHeadEquiv rank).symm_apply_apply allocation).symm)
    _ = ∑ label : Fin 3, ∑ allocation : Fin rank → Fin 3,
        function (Fin.cons label allocation) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := by rw [Fin.sum_univ_three]

@[simp] theorem allocationFiber_cons_same {rank : ℕ} (label : Fin 3)
    (allocation : Fin rank → Fin 3) :
    allocationFiber (Fin.cons label allocation) label =
      Grad.RepresentedKernel.SpatialProduct.headSelected (allocationFiber allocation label) := by
  ext position
  refine Fin.cases ?_ (fun previous => ?_) position <;>
    simp [allocationFiber, Grad.RepresentedKernel.SpatialProduct.headSelected,
      Grad.RepresentedKernel.SpatialProduct.liftSelected]

@[simp] theorem allocationFiber_cons_ne {rank : ℕ} (head label : Fin 3)
    (different : head ≠ label) (allocation : Fin rank → Fin 3) :
    allocationFiber (Fin.cons head allocation) label =
      Grad.RepresentedKernel.SpatialProduct.liftSelected (allocationFiber allocation label) := by
  ext position
  refine Fin.cases ?_ (fun previous => ?_) position <;>
    simp [allocationFiber, Grad.RepresentedKernel.SpatialProduct.liftSelected, different]

theorem trilinear_derivative {First Second Third Intermediate Fourth : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    [NormedAddCommGroup Intermediate] [NormedSpace ℝ Intermediate]
    [NormedAddCommGroup Fourth] [NormedSpace ℝ Fourth]
    (outerMap : First →L[ℝ] Intermediate →L[ℝ] Fourth)
    (innerMap : Second →L[ℝ] Third →L[ℝ] Intermediate)
    {first : Spatial → First} {second : Spatial → Second} {third : Spatial → Third}
    {point : Spatial} {firstDerivative : Spatial →L[ℝ] First}
    {secondDerivative : Spatial →L[ℝ] Second} {thirdDerivative : Spatial →L[ℝ] Third}
    (firstDifferentiable : HasFDerivAt first firstDerivative point)
    (secondDifferentiable : HasFDerivAt second secondDerivative point)
    (thirdDifferentiable : HasFDerivAt third thirdDerivative point) (direction : Spatial) :
    fderiv ℝ (fun source => outerMap (first source) (innerMap (second source) (third source)))
        point direction =
      outerMap (firstDerivative direction) (innerMap (second point) (third point)) +
      outerMap (first point) (innerMap (secondDerivative direction) (third point)) +
      outerMap (first point) (innerMap (second point) (thirdDerivative direction)) := by
  have innerDerivative := innerMap.hasFDerivAt_of_bilinear secondDifferentiable thirdDifferentiable
  rw [outerMap.fderiv_of_bilinear firstDifferentiable.differentiableAt innerDerivative.differentiableAt,
    innerMap.fderiv_of_bilinear secondDifferentiable.differentiableAt
      thirdDifferentiable.differentiableAt]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [firstDifferentiable.fderiv, secondDifferentiable.fderiv, thirdDifferentiable.fderiv]
  abel

theorem trilinear_finite {First Second Third Intermediate Fourth : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    [NormedAddCommGroup Intermediate] [NormedSpace ℝ Intermediate]
    [NormedAddCommGroup Fourth] [NormedSpace ℝ Fourth]
    (outerMap : First →L[ℝ] Intermediate →L[ℝ] Fourth)
    (innerMap : Second →L[ℝ] Third →L[ℝ] Intermediate)
    (order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (first : Spatial → First) (second : Spatial → Second) (third : Spatial → Third)
    (firstSmooth : ContDiffOn ℝ order first domain)
    (secondSmooth : ContDiffOn ℝ order second domain)
    (thirdSmooth : ContDiffOn ℝ order third domain) :
    ∀ (rank : ℕ), rank ≤ order → ∀ (directions : Fin rank → Spatial)
      (point : Spatial), point ∈ domain →
      iteratedFDeriv ℝ rank
        (fun source => outerMap (first source) (innerMap (second source) (third source))) point directions =
      ∑ allocation : Fin rank → Fin 3,
        outerMap
          (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
            (allocationFiber allocation 0) first point)
          (innerMap
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
              (allocationFiber allocation 1) second point)
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
              (allocationFiber allocation 2) third point)) := by
  have innerSmooth : ContDiffOn ℝ order
      (fun source => innerMap (second source) (third source)) domain :=
    innerMap.isBoundedBilinearMap.contDiff.comp₂_contDiffOn secondSmooth thirdSmooth
  have productSmooth : ContDiffOn ℝ order
      (fun source => outerMap (first source) (innerMap (second source) (third source))) domain :=
    outerMap.isBoundedBilinearMap.contDiff.comp₂_contDiffOn firstSmooth innerSmooth
  intro rank rankBound
  induction rank with
  | zero =>
    intro directions point _
    rw [Fintype.sum_unique]
    rfl
  | succ rank inductionHypothesis =>
    intro directions point inside
    have strict : rank < order := by omega
    have firstLocal := firstSmooth.contDiffAt (openDomain.mem_nhds inside)
    have secondLocal := secondSmooth.contDiffAt (openDomain.mem_nhds inside)
    have thirdLocal := thirdSmooth.contDiffAt (openDomain.mem_nhds inside)
    have productLocal := productSmooth.contDiffAt (openDomain.mem_nhds inside)
    have localEquality :
        (fun source => iteratedFDeriv ℝ rank
          (fun source => outerMap (first source) (innerMap (second source) (third source)))
            source (Fin.tail directions)) =ᶠ[𝓝 point]
        (fun source => ∑ allocation : Fin rank → Fin 3,
          outerMap
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative (Fin.tail directions)
              (allocationFiber allocation 0) first source)
            (innerMap
              (Grad.RepresentedKernel.SpatialProduct.selectedDerivative (Fin.tail directions)
                (allocationFiber allocation 1) second source)
              (Grad.RepresentedKernel.SpatialProduct.selectedDerivative (Fin.tail directions)
                (allocationFiber allocation 2) third source))) := by
      filter_upwards [openDomain.mem_nhds inside] with source sourceInside
      exact inductionHypothesis (by omega) (Fin.tail directions) source sourceInside
    rw [(differentiable_iterated_finite productLocal rank strict).iteratedFDeriv_succ_apply_left',
      localEquality.fderiv_eq]
    rw [fderiv_fun_sum (fun allocation _ =>
      (outerMap.hasFDerivAt_of_bilinear
        (differentiable_selected_finite firstLocal strict (Fin.tail directions)
          (allocationFiber allocation 0)).hasFDerivAt
        (innerMap.hasFDerivAt_of_bilinear
          (differentiable_selected_finite secondLocal strict (Fin.tail directions)
            (allocationFiber allocation 1)).hasFDerivAt
          (differentiable_selected_finite thirdLocal strict (Fin.tail directions)
            (allocationFiber allocation 2)).hasFDerivAt)).differentiableAt)]
    rw [sum_allocations_three, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro allocation _
    rw [trilinear_derivative outerMap innerMap
      (differentiable_selected_finite firstLocal strict (Fin.tail directions)
        (allocationFiber allocation 0)).hasFDerivAt
      (differentiable_selected_finite secondLocal strict (Fin.tail directions)
        (allocationFiber allocation 1)).hasFDerivAt
      (differentiable_selected_finite thirdLocal strict (Fin.tail directions)
        (allocationFiber allocation 2)).hasFDerivAt]
    simp only [allocationFiber_cons_same,
      allocationFiber_cons_ne 0 1 (by decide) allocation,
      allocationFiber_cons_ne 0 2 (by decide) allocation,
      allocationFiber_cons_ne 1 0 (by decide) allocation,
      allocationFiber_cons_ne 1 2 (by decide) allocation,
      allocationFiber_cons_ne 2 0 (by decide) allocation,
      allocationFiber_cons_ne 2 1 (by decide) allocation,
      fderiv_selected_finite firstLocal strict,
      fderiv_selected_finite secondLocal strict,
      fderiv_selected_finite thirdLocal strict,
      Grad.RepresentedKernel.SpatialProduct.selectedDerivative_lift]

theorem trilinear_at {First Second Third Intermediate Fourth : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    [NormedAddCommGroup Intermediate] [NormedSpace ℝ Intermediate]
    [NormedAddCommGroup Fourth] [NormedSpace ℝ Fourth]
    (outerMap : First →L[ℝ] Intermediate →L[ℝ] Fourth)
    (innerMap : Second →L[ℝ] Third →L[ℝ] Intermediate)
    (first : Spatial → First) (second : Spatial → Second) (third : Spatial → Third)
    (point : Spatial) (firstSmooth : ContDiffAt ℝ ∞ first point)
    (secondSmooth : ContDiffAt ℝ ∞ second point) (thirdSmooth : ContDiffAt ℝ ∞ third point)
    (rank : ℕ) (directions : Fin rank → Spatial) :
    iteratedFDeriv ℝ rank
      (fun source => outerMap (first source) (innerMap (second source) (third source))) point directions =
      ∑ allocation : Fin rank → Fin 3,
        outerMap
          (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
            (allocationFiber allocation 0) first point)
          (innerMap
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
              (allocationFiber allocation 1) second point)
            (Grad.RepresentedKernel.SpatialProduct.selectedDerivative directions
              (allocationFiber allocation 2) third point)) := by
  let order := rank + 1
  have firstFinite : ContDiffAt ℝ order first point := firstSmooth.of_le (by exact_mod_cast le_top)
  have secondFinite : ContDiffAt ℝ order second point := secondSmooth.of_le (by exact_mod_cast le_top)
  have thirdFinite : ContDiffAt ℝ order third point := thirdSmooth.of_le (by exact_mod_cast le_top)
  rcases firstFinite.contDiffOn le_rfl (by simp) with ⟨firstSet, firstNeighborhood, firstOn⟩
  rcases secondFinite.contDiffOn le_rfl (by simp) with ⟨secondSet, secondNeighborhood, secondOn⟩
  rcases thirdFinite.contDiffOn le_rfl (by simp) with ⟨thirdSet, thirdNeighborhood, thirdOn⟩
  rcases mem_nhds_iff.mp firstNeighborhood with
    ⟨firstOpen, firstSubset, firstOpenDomain, pointFirst⟩
  rcases mem_nhds_iff.mp secondNeighborhood with
    ⟨secondOpen, secondSubset, secondOpenDomain, pointSecond⟩
  rcases mem_nhds_iff.mp thirdNeighborhood with
    ⟨thirdOpen, thirdSubset, thirdOpenDomain, pointThird⟩
  let domain := firstOpen ∩ secondOpen ∩ thirdOpen
  have openDomain : IsOpen domain := (firstOpenDomain.inter secondOpenDomain).inter thirdOpenDomain
  have pointInside : point ∈ domain := ⟨⟨pointFirst, pointSecond⟩, pointThird⟩
  have firstSmoothOn : ContDiffOn ℝ order first domain :=
    firstOn.mono (Set.inter_subset_left.trans (Set.inter_subset_left.trans firstSubset))
  have secondSmoothOn : ContDiffOn ℝ order second domain :=
    secondOn.mono (Set.inter_subset_left.trans (Set.inter_subset_right.trans secondSubset))
  have thirdSmoothOn : ContDiffOn ℝ order third domain :=
    thirdOn.mono (Set.inter_subset_right.trans thirdSubset)
  exact trilinear_finite outerMap innerMap order domain openDomain first second third
    firstSmoothOn secondSmoothOn thirdSmoothOn rank (by omega) directions point pointInside

end LocalLeibniz

theorem selectedDerivative_eq_spatialProduct {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {rank : ℕ} (word : Fin rank → Fin 2) (selected : Finset (Fin rank))
    (function : Spatial → Value) (point : Spatial) :
    selectedDerivative word selected function point =
      Grad.RepresentedKernel.SpatialProduct.selectedDerivative
        (fun position => spatialDirection (word position)) selected function point := rfl

theorem ordered_bilinear_at {First : Type firstUniverse} {Second : Type secondUniverse}
    {Third : Type thirdUniverse}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    (bilinearMap : First →L[ℝ] Second →L[ℝ] Third)
    (first : Spatial → First) (second : Spatial → Second) (point : Spatial)
    (firstSmooth : ContDiffAt ℝ ∞ first point) (secondSmooth : ContDiffAt ℝ ∞ second point)
    (rank : ℕ) (word : Fin rank → Fin 2) :
    orderedDerivative rank word (fun source => bilinearMap (first source) (second source)) point =
      ∑ selected : Finset (Fin rank),
        bilinearMap (selectedDerivative word selected first point)
          (selectedDerivative word selectedᶜ second point) := by
  exact LocalLeibniz.bilinear_at bilinearMap first second point firstSmooth secondSmooth rank
    (fun position => spatialDirection (word position))

theorem ordered_trilinear_at {First : Type firstUniverse} {Second : Type secondUniverse}
    {Third : Type thirdUniverse} {Intermediate : Type*} {Fourth : Type*}
    [NormedAddCommGroup First] [NormedSpace ℝ First]
    [NormedAddCommGroup Second] [NormedSpace ℝ Second]
    [NormedAddCommGroup Third] [NormedSpace ℝ Third]
    [NormedAddCommGroup Intermediate] [NormedSpace ℝ Intermediate]
    [NormedAddCommGroup Fourth] [NormedSpace ℝ Fourth]
    (outerMap : First →L[ℝ] Intermediate →L[ℝ] Fourth)
    (innerMap : Second →L[ℝ] Third →L[ℝ] Intermediate)
    (first : Spatial → First) (second : Spatial → Second) (third : Spatial → Third)
    (point : Spatial) (firstSmooth : ContDiffAt ℝ ∞ first point)
    (secondSmooth : ContDiffAt ℝ ∞ second point) (thirdSmooth : ContDiffAt ℝ ∞ third point)
    (rank : ℕ) (word : Fin rank → Fin 2) :
    orderedDerivative rank word
      (fun source => outerMap (first source) (innerMap (second source) (third source))) point =
      ∑ allocation : Fin rank → Fin 3,
        outerMap (selectedDerivative word (allocationFiber allocation 0) first point)
          (innerMap (selectedDerivative word (allocationFiber allocation 1) second point)
            (selectedDerivative word (allocationFiber allocation 2) third point)) := by
  exact LocalLeibniz.trilinear_at outerMap innerMap first second third point
    firstSmooth secondSmooth thirdSmooth rank (fun position => spatialDirection (word position))

end Grad.AnalyticWeights.Higher
