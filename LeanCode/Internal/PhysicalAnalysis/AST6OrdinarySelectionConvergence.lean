import AST5CompletedAngularSelection
import ABF1OrdinaryBulkFaithfulness

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskFaithfulness
attribute [local instance] unitNormedSpace
local instance selectionComplete (grade : ℕ) : CompleteSpace (unitDiskSobolev grade) := by
  unfold unitDiskSobolev
  infer_instance

theorem ordinaryMode_square_summable (grade : ℕ) (field : unitDiskSobolev grade) :
    Summable (fun mode : ℤ => ‖ordinaryMode grade mode field‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (fun modes => ordinaryMode_square_sum grade modes field)

/-- Square summability together with a uniform finite synthesis estimate
implies unconditional summability in the original Banach norm. -/
theorem summable_of_square_synthesis {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (field : ℤ → E) (constant : ℝ) (nonnegativeConstant : 0 ≤ constant)
    (squareSummable : Summable (fun mode => ‖field mode‖ ^ 2))
    (synthesis : ∀ modes : Finset ℤ, ‖∑ mode ∈ modes, field mode‖ ^ 2 ≤
      constant * ∑ mode ∈ modes, ‖field mode‖ ^ 2) : Summable field := by
  apply summable_iff_vanishing_norm.mpr
  intro epsilon positive
  have denominator : 0 < constant + 1 := by linarith
  obtain ⟨base, tail⟩ := summable_iff_vanishing_norm.mp squareSummable
    (epsilon ^ 2 / (constant + 1)) (div_pos (sq_pos_of_pos positive) denominator)
  refine ⟨base, fun modes disjoint => ?_⟩
  have tailBound := tail modes disjoint
  have nonnegative : 0 ≤ ∑ mode ∈ modes, ‖field mode‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.norm_of_nonneg nonnegative] at tailBound
  have productBound := (lt_div_iff₀ denominator).mp tailBound
  have bound := synthesis modes
  apply (sq_lt_sq₀ (norm_nonneg _) positive.le).mp
  nlinarith

theorem ordinaryMode_summable (grade : ℕ) (field : unitDiskSobolev grade) :
    Summable (fun mode : ℤ => ordinaryMode grade mode field) := by
  apply summable_of_square_synthesis (fun mode => ordinaryMode grade mode field)
    (orthogonalGradeConstant grade ^ 2) (sq_nonneg _) (ordinaryMode_square_summable grade field)
  intro modes
  exact (ordinarySelected_apply grade modes field) ▸ ordinarySelected_square_bound grade modes field

theorem ordinaryMode_hasSum (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade) :
    HasSum (fun mode : ℤ => ordinaryMode grade mode field) field := by
  have converges : Tendsto (fun modes : Finset ℤ => ordinarySelected grade modes field) atTop
      (𝓝 (∑' mode : ℤ, ordinaryMode grade mode field)) := by
    have series := (ordinaryMode_summable grade field).hasSum
    change Tendsto (fun modes : Finset ℤ => ∑ mode ∈ modes, ordinaryMode grade mode field) atTop
      (𝓝 (∑' mode : ℤ, ordinaryMode grade mode field)) at series
    exact series.congr' (Eventually.of_forall (fun modes => (ordinarySelected_apply grade modes field).symm))
  have bulkConverges := ((unitDiskBulk grade).continuous.tendsto _).comp converges
  change Tendsto (fun modes : Finset ℤ => unitDiskBulk grade (ordinarySelected grade modes field)) atTop
    (𝓝 (unitDiskBulk grade (∑' mode : ℤ, ordinaryMode grade mode field))) at bulkConverges
  simp_rw [ordinarySelected_bulk] at bulkConverges
  have sameBulk := tendsto_nhds_unique bulkConverges (diskSelectedModes_tendsto (unitDiskBulk grade field))
  have same := ordinaryBulk_injective parameters grade sameBulk
  exact (congrArg (fun value : unitDiskSobolev grade => HasSum
    (fun mode : ℤ => ordinaryMode grade mode field) value) same).mp (ordinaryMode_summable grade field).hasSum

/-- Finite angular selections converge for the directed set of all finite
subsets of Z, in the literal H^s norm of the original source. -/
theorem ordinarySelected_tendsto (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade) :
    Tendsto (fun modes : Finset ℤ => ordinarySelected grade modes field) atTop (𝓝 field) := by
  have series := ordinaryMode_hasSum parameters grade field
  change Tendsto (fun modes : Finset ℤ => ∑ mode ∈ modes, ordinaryMode grade mode field) atTop (𝓝 field) at series
  exact series.congr' (Eventually.of_forall (fun modes => (ordinarySelected_apply grade modes field).symm))

theorem ordinarySelected_tendsto_along (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade)
    {ι : Type*} {filter : Filter ι} {modes : ι → Finset ℤ} (exhausts : Tendsto modes filter atTop) :
    Tendsto (fun index => ordinarySelected grade (modes index) field) filter (𝓝 field) :=
  (ordinarySelected_tendsto parameters grade field).comp exhausts

end Grad.AngularSobolevTruncation
