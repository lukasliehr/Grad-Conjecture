import CUT1Interface

noncomputable section

open Grad.PDEBootstrap
open scoped BigOperators ContDiff Topology

namespace Grad.CompactCutoff

theorem local_bump (domain : Set Spatial) (openDomain : IsOpen domain)
    (point : Spatial) (membership : point ∈ domain) :
    ∃ bump : ContDiffBump point, Metric.closedBall point bump.rOut ⊆ domain := by
  obtain ⟨radius, positiveRadius, contained⟩ := Metric.isOpen_iff.mp openDomain point membership
  refine ⟨⟨radius / 4, radius / 2, by positivity, by linarith⟩, ?_⟩
  exact (Metric.closedBall_subset_ball (by change radius / 2 < radius; linarith)).trans contained

theorem cover_consumer : CoverGoal := by
  classical
  intro compactSet domain compactSetCompact openDomain included
  choose bumps contained using fun point : compactSet =>
    local_bump domain openDomain point.val (included point.property)
  have covered : compactSet ⊆ ⋃ point : compactSet, Metric.ball point.val (bumps point).rIn := by
    intro point membership
    exact Set.mem_iUnion.mpr ⟨⟨point, membership⟩, Metric.mem_ball_self (bumps _).rIn_pos⟩
  obtain ⟨selected, selectedCover⟩ := compactSetCompact.elim_finite_subcover
    (fun point : compactSet => Metric.ball point.val (bumps point).rIn)
    (fun _ => Metric.isOpen_ball) covered
  let enumerate := (Fintype.equivFin ↥selected).symm
  refine ⟨{
    count := Fintype.card ↥selected
    center := fun index => (enumerate index).val.val
    bump := fun index => bumps (enumerate index).val
    contained := fun index => contained (enumerate index).val
    covers := ?_ }⟩
  intro point membership
  obtain ⟨center, selectedCenter, inBall⟩ := Set.mem_iUnion₂.mp (selectedCover membership)
  refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin ↥selected) ⟨center, selectedCenter⟩, ?_⟩
  have equality : enumerate ((Fintype.equivFin ↥selected) ⟨center, selectedCenter⟩) =
      ⟨center, selectedCenter⟩ := Equiv.symm_apply_apply _ _
  rw [equality]
  exact inBall

theorem BumpCover.inner_open {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : IsOpen cover.innerRegion :=
  isOpen_iUnion fun _ => Metric.isOpen_ball

theorem BumpCover.inner_subset_outer {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : cover.innerRegion ⊆ cover.outerRegion := by
  intro point membership
  obtain ⟨index, inBall⟩ := Set.mem_iUnion.mp membership
  exact Set.mem_iUnion.mpr ⟨index,
    Metric.closedBall_subset_closedBall (cover.bump index).rIn_lt_rOut.le
      (Metric.ball_subset_closedBall inBall)⟩

theorem BumpCover.outer_compact {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : IsCompact cover.outerRegion :=
  isCompact_iUnion fun index => isCompact_closedBall (cover.center index) (cover.bump index).rOut

theorem BumpCover.outer_subset {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : cover.outerRegion ⊆ domain :=
  Set.iUnion_subset cover.contained

theorem BumpCover.smooth {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : ContDiff ℝ ∞ cover.toFun :=
  contDiff_const.sub (contDiff_prod fun index _ => contDiff_const.sub (cover.bump index).contDiff)

theorem BumpCover.nonnegative {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) (point : Spatial) : 0 ≤ cover.toFun point := by
  apply sub_nonneg.mpr
  exact Finset.prod_le_one (fun index _ => sub_nonneg.mpr (cover.bump index).le_one)
    (fun index _ => sub_le_self _ (cover.bump index).nonneg)

theorem BumpCover.atMostOne {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) (point : Spatial) : cover.toFun point ≤ 1 :=
  sub_le_self _ (Finset.prod_nonneg fun index _ => sub_nonneg.mpr (cover.bump index).le_one)

theorem BumpCover.supported_outer {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : tsupport cover.toFun ⊆ cover.outerRegion := by
  apply closure_minimal _ cover.outer_compact.isClosed
  intro point membership
  change cover.toFun point ≠ 0 at membership
  by_contra outside
  have vanishes : ∀ index, cover.bump index point = 0 := by
    intro index
    have notInBall : point ∉ Metric.closedBall (cover.center index) (cover.bump index).rOut :=
      fun inBall => outside (Set.mem_iUnion.mpr ⟨index, inBall⟩)
    exact (cover.bump index).zero_of_le_dist (le_of_lt (lt_of_not_ge notInBall))
  apply membership
  change 1 - ∏ index : Fin cover.count, (1 - cover.bump index point) = 0
  simp only [vanishes, sub_zero, Finset.prod_const_one, sub_self]

theorem BumpCover.one_inner {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) :
    Set.EqOn cover.toFun (fun _ => 1) cover.innerRegion := by
  intro point membership
  obtain ⟨index, inBall⟩ := Set.mem_iUnion.mp membership
  have bumpOne := (cover.bump index).one_of_mem_closedBall (Metric.ball_subset_closedBall inBall)
  have productZero : ∏ index : Fin cover.count, (1 - cover.bump index point) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ index) (sub_eq_zero.mpr bumpOne.symm)
  change 1 - ∏ index : Fin cover.count, (1 - cover.bump index point) = 1
  rw [productZero, sub_zero]

def BumpCover.cutoff {compactSet domain : Set Spatial}
    (cover : BumpCover compactSet domain) : Cutoff compactSet domain where
  toFun := cover.toFun
  smooth := cover.smooth
  compact := cover.outer_compact.of_isClosed_subset (isClosed_tsupport _) cover.supported_outer
  nonnegative := cover.nonnegative
  atMostOne := cover.atMostOne
  supported := cover.supported_outer.trans cover.outer_subset
  near := ⟨cover.innerRegion, cover.inner_open, cover.covers,
    cover.inner_subset_outer.trans cover.outer_subset, cover.one_inner⟩

theorem finite_product_consumer : FiniteProductGoal := by
  intro compactSet domain cover
  exact ⟨cover.inner_open, cover.covers, cover.inner_subset_outer, cover.outer_compact,
    cover.outer_subset, cover.supported_outer, cover.one_inner, cover.cutoff, rfl⟩

theorem Cutoff.germ {compactSet domain : Set Spatial} (cutoff : Cutoff compactSet domain)
    (point : Spatial) (membership : point ∈ compactSet) :
    cutoff.toFun =ᶠ[𝓝 point] (fun _ => 1) := by
  obtain ⟨neighborhood, openNeighborhood, included, _, oneOn⟩ := cutoff.near
  exact Filter.mem_of_superset (openNeighborhood.mem_nhds (included membership)) oneOn

theorem Cutoff.one_on {compactSet domain : Set Spatial} (cutoff : Cutoff compactSet domain) :
    Set.EqOn cutoff.toFun (fun _ => 1) compactSet := by
  obtain ⟨_, _, included, _, oneOn⟩ := cutoff.near
  exact oneOn.mono included

theorem existence_consumer : ExistenceGoal := by
  intro compactSet domain compactSetCompact openDomain included
  obtain ⟨cover⟩ := cover_consumer compactSet domain compactSetCompact openDomain included
  exact ⟨cover.cutoff, ⟨cover, rfl⟩, cover.cutoff.germ⟩

def compactCutoff (compactSet domain : Set Spatial) (compactSetCompact : IsCompact compactSet)
    (openDomain : IsOpen domain) (included : compactSet ⊆ domain) : Cutoff compactSet domain :=
  (existence_consumer compactSet domain compactSetCompact openDomain included).choose

theorem compactCutoff_finite_product (compactSet domain : Set Spatial)
    (compactSetCompact : IsCompact compactSet) (openDomain : IsOpen domain)
    (included : compactSet ⊆ domain) :
    ∃ cover : BumpCover compactSet domain,
      (compactCutoff compactSet domain compactSetCompact openDomain included).toFun = cover.toFun :=
  (existence_consumer compactSet domain compactSetCompact openDomain included).choose_spec.1

theorem compactCutoff_germ (compactSet domain : Set Spatial)
    (compactSetCompact : IsCompact compactSet) (openDomain : IsOpen domain)
    (included : compactSet ⊆ domain) (point : Spatial) (membership : point ∈ compactSet) :
    (compactCutoff compactSet domain compactSetCompact openDomain included).toFun =ᶠ[𝓝 point]
      (fun _ => 1) :=
  (compactCutoff compactSet domain compactSetCompact openDomain included).germ point membership

end Grad.CompactCutoff
