import ANG5ContractiveModes
import ANH17RobinForm
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Set
namespace Grad.CircularHighWeak

/-- A contractive idempotent has orthogonal image and kernel. -/
private theorem contractiveProjection_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (projection : E →L[ℂ] E)
    (contract : ∀ field, ‖projection field‖ ≤ ‖field‖)
    (idempotent : ∀ field, projection (projection field) = projection field)
    (first second : E) : inner ℂ (projection first) (second - projection second) = 0 := by
  let kernel := LinearMap.ker projection.toLinearMap
  have residual (field : E) : field - projection field ∈ kernel := by
    change projection (field - projection field) = 0
    rw [map_sub, idempotent, sub_self]
  have positive : BddBelow (Set.range (fun field : kernel => ‖first - field.val‖)) :=
    ⟨0, by rintro _ ⟨field, rfl⟩; exact norm_nonneg _⟩
  have minimizing : ‖first - (first - projection first)‖ = ⨅ field : kernel, ‖first - field.val‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro field
      rw [sub_sub_cancel]
      have projected : projection (first - field.val) = projection first := by
        rw [map_sub, show projection field.val = 0 from field.property, sub_zero]
      exact projected ▸ contract (first - field.val)
    · exact ciInf_le positive ⟨first - projection first, residual first⟩
  have orthogonal := (kernel.norm_eq_iInf_iff_inner_eq_zero (residual first)).mp minimizing
  have result := orthogonal (second - projection second) (residual second)
  simpa only [sub_sub_cancel] using result

theorem contractiveProjection_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (projection : E →L[ℂ] E)
    (contract : ∀ field, ‖projection field‖ ≤ ‖field‖)
    (idempotent : ∀ field, projection (projection field) = projection field)
    (first second : E) : inner ℂ (projection first) second = inner ℂ first (projection second) := by
  have left := contractiveProjection_orthogonal projection contract idempotent first second
  have right := contractiveProjection_orthogonal projection contract idempotent second first
  rw [inner_sub_right] at left right
  have reverse : inner ℂ first (projection second) = inner ℂ (projection first) (projection second) := by
    have conjugated := congrArg (star : ℂ → ℂ) (sub_eq_zero.mp right)
    exact (inner_conj_symm first (projection second)).symm.trans
      (conjugated.trans (inner_conj_symm (projection first) (projection second)))
  exact (sub_eq_zero.mp left).trans reverse.symm

attribute [local instance] diskComplexNormedSpace

theorem highDiskMode_symmetric (mode : ℤ) (first second : highDiskGrade) :
    inner ℂ (highDiskMode mode first) second = inner ℂ first (highDiskMode mode second) :=
  contractiveProjection_symmetric (highDiskMode mode) (highDiskMode_contract mode)
    (fun field => (highDiskMode_projection mode mode field).trans (if_pos rfl)) first second

end Grad.CircularHighWeak
