import AST6OrdinarySelectionConvergence

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

theorem ordinaryMode_projection (grade : ℕ) (first second : ℤ) (field : unitDiskSobolev grade) :
    ordinaryMode grade first (ordinaryMode grade second field) =
      if first = second then ordinaryMode grade first field else 0 := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((ordinaryMode grade first).continuous.comp (ordinaryMode grade second).continuous)
      (by split_ifs <;> fun_prop)) _ field
  intro core
  change ordinaryMode grade first (ordinaryMode grade second (unitDiskCoreInto grade core)) =
    if first = second then ordinaryMode grade first (unitDiskCoreInto grade core) else 0
  calc
    _ = ordinaryMode grade first (unitDiskCoreInto grade (angularClosedJet second core)) :=
      congrArg (ordinaryMode grade first) (ordinaryMode_core grade second core)
    _ = unitDiskCoreInto grade (angularClosedJet first (angularClosedJet second core)) :=
      ordinaryMode_core grade first (angularClosedJet second core)
    _ = unitDiskCoreInto grade (if first = second then angularClosedJet first core else 0) :=
      congrArg (unitDiskCoreInto grade) (angularClosedJet_projection first second core)
    _ = _ := by
      split_ifs
      · exact (ordinaryMode_core grade first core).symm
      · exact map_zero _

theorem ordinaryMode_selected (grade : ℕ) (modes : Finset ℤ) (mode : ℤ) (field : unitDiskSobolev grade) :
    ordinaryMode grade mode (ordinarySelected grade modes field) =
      if mode ∈ modes then ordinaryMode grade mode field else 0 := by
  calc
    _ = ordinaryMode grade mode (∑ selected ∈ modes, ordinaryMode grade selected field) :=
      congrArg (ordinaryMode grade mode) (ordinarySelected_apply grade modes field)
    _ = ∑ selected ∈ modes, ordinaryMode grade mode (ordinaryMode grade selected field) := map_sum _ _ _
    _ = ∑ selected ∈ modes, if mode = selected then ordinaryMode grade mode field else 0 :=
      Finset.sum_congr rfl (fun selected _ => ordinaryMode_projection grade mode selected field)
    _ = _ := by simp

theorem ordinarySelected_idempotent (grade : ℕ) (modes : Finset ℤ) (field : unitDiskSobolev grade) :
    ordinarySelected grade modes (ordinarySelected grade modes field) = ordinarySelected grade modes field := by
  calc
    _ = ∑ mode ∈ modes, ordinaryMode grade mode (ordinarySelected grade modes field) :=
      ordinarySelected_apply grade modes (ordinarySelected grade modes field)
    _ = ∑ mode ∈ modes, ordinaryMode grade mode field :=
      Finset.sum_congr rfl (fun mode member => (ordinaryMode_selected grade modes mode field).trans (if_pos member))
    _ = _ := (ordinarySelected_apply grade modes field).symm

theorem ordinarySelected_operatorNorm (grade : ℕ) (modes : Finset ℤ) :
    ‖ordinarySelected grade modes‖ ≤ orthogonalGradeConstant grade ^ 2 := by
  exact @ContinuousLinearMap.opNorm_le_bound ℂ ℂ (unitDiskSobolev grade) (unitDiskSobolev grade)
    inferInstance inferInstance inferInstance inferInstance (unitNormedSpace grade) (unitNormedSpace grade)
    (RingHom.id ℂ) (ordinarySelected grade modes) (orthogonalGradeConstant grade ^ 2)
    (sq_nonneg _) (ordinarySelected_uniform_bound grade modes)

/-- Exact all-grade angular truncation on the original source space. Its
finite selections represent the literal L2 angular projections, have a
mode-set-independent bound, and converge to that same source in H^s. -/
theorem actualOrdinarySourceTruncations (parameters : PhaseParameters) (grade : ℕ)
    (source : unitDiskSobolev grade) :
    (∀ modes : Finset ℤ, unitDiskBulk grade (ordinarySelected grade modes source) =
      diskSelectedModes modes (unitDiskBulk grade source)) ∧
    (∀ modes : Finset ℤ, ‖ordinarySelected grade modes source‖ ≤
      orthogonalGradeConstant grade ^ 2 * ‖source‖) ∧
    Tendsto (fun modes : Finset ℤ => ordinarySelected grade modes source) atTop (𝓝 source) :=
  ⟨fun modes => ordinarySelected_bulk grade modes source,
    fun modes => ordinarySelected_uniform_bound grade modes source,
    ordinarySelected_tendsto parameters grade source⟩

/-- The dense smooth source used by the finite inverse is exactly the
accepted selectedAngularJet, in the same ordinary grade and norm. -/
theorem actualSmoothSourceTruncations (parameters : PhaseParameters) (grade : ℕ) (core : ClosedJet 1) :
    (∀ modes : Finset ℤ, ordinarySelected grade modes (unitDiskCoreInto grade core) =
      unitDiskCoreInto grade (selectedAngularJet modes core)) ∧
    (∀ modes : Finset ℤ, ‖unitDiskCoreInto grade (selectedAngularJet modes core)‖ ≤
      orthogonalGradeConstant grade ^ 2 * ‖unitDiskCoreInto grade core‖) ∧
    Tendsto (fun modes : Finset ℤ => unitDiskCoreInto grade (selectedAngularJet modes core)) atTop
      (𝓝 (unitDiskCoreInto grade core)) := by
  refine ⟨fun modes => ordinarySelected_core grade modes core, ?_, ?_⟩
  · intro modes
    exact (ordinarySelected_core grade modes core) ▸ ordinarySelected_uniform_bound grade modes (unitDiskCoreInto grade core)
  · simpa only [ordinarySelected_core] using ordinarySelected_tendsto parameters grade (unitDiskCoreInto grade core)

end Grad.AngularSobolevTruncation
