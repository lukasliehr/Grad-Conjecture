import AKBV3OriginalCoreMixedApproximation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.CompatibleCompletion Grad.RawSourceFaithfulness

/-- A genuine mixed weak jet belongs to the original norm completion, with exact norm and SAME weighted base in every signed cell. -/
theorem mixedJet_originalCompletion {dimension grade : ℕ} (parameters : PhaseParameters)
    (jet : Mixed dimension grade openUnitDisk) :
    ∃ completed : AGrade parameters dimension grade,
      ‖completed‖ = ‖jet‖ ∧
      ∀ cell : ℤ, zeroCell parameters cell (completedInclusion parameters (Nat.zero_le grade) completed) =
        fieldCellProjection dimension openUnitDisk cell
          (base dimension grade openUnitDisk (fun index => grade-degree index) jet) := by
  obtain ⟨cores,approximants,converges,coordinates,zeroCoordinates⟩ := originalCore_mixedApproximation parameters jet
  let sequence := fun number => aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (cores number))
  have sameDistance (first second : ℕ) : dist (sequence first) (sequence second) = dist (approximants first) (approximants second) :=
    originalCore_dist_eq_mixed parameters (cores first) (cores second) (approximants first) (approximants second)
      (coordinates first) (coordinates second)
  have cauchy : CauchySeq sequence := by
    apply Metric.cauchySeq_iff.mpr
    intro epsilon positive
    obtain ⟨number,tail⟩ := Metric.cauchySeq_iff.mp converges.cauchy_map epsilon positive
    exact ⟨number,fun first firstLarge second secondLarge =>
      (sameDistance first second).trans_lt (tail first firstLarge second secondLarge)⟩
  obtain ⟨completed,limit⟩ := cauchy_map_iff_exists_tendsto.mp cauchy
  refine ⟨completed,?_,?_⟩
  · have left := continuous_norm.tendsto completed |>.comp limit
    have right := continuous_norm.tendsto jet |>.comp converges
    apply tendsto_nhds_unique (left.congr' (Eventually.of_forall (fun number => ?_))) right
    exact (aGradeEta_norm parameters _).trans
      (originalCore_norm_eq_mixed parameters (cores number) (approximants number) (coordinates number))
  · intro cell
    let mapping := (zeroCell (dimension := dimension) parameters cell).comp (completedInclusion parameters (Nat.zero_le grade))
    let target := (fieldCellProjection dimension openUnitDisk cell).comp
      (base dimension grade openUnitDisk (fun index => grade-degree index))
    have left := mapping.continuous.tendsto completed |>.comp limit
    have right := target.continuous.tendsto jet |>.comp converges
    apply tendsto_nhds_unique (left.congr' (Eventually.of_forall (fun number => ?_))) right
    change zeroCell parameters cell (completedInclusion parameters (Nat.zero_le grade)
      (aGradeEta parameters (GradeCore.ofCoreLinear (cores number)))) = _
    rw [completedInclusion_apply_eta]
    exact zeroCoordinates number cell

end Grad.CartesianCoreRecovery
