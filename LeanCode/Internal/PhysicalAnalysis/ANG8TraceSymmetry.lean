import ANG6OrthogonalModes
import ANG7BoundaryModes

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Set
namespace Grad.CircularHighWeak

private theorem contractiveImage_orthogonal {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (evaluation : E →L[ℂ] F) (projection : E →L[ℂ] E)
    (contract : ∀ field, ‖evaluation (projection field)‖ ≤ ‖evaluation field‖)
    (idempotent : ∀ field, projection (projection field) = projection field)
    (first second : E) : inner ℂ (evaluation (projection first))
      (evaluation second - evaluation (projection second)) = 0 := by
  let residual := ContinuousLinearMap.id ℂ E - projection
  let kernelImage := (evaluation.comp residual).toLinearMap.range
  have residual_mem (field : E) : evaluation field - evaluation (projection field) ∈ kernelImage := by
    refine ⟨field, ?_⟩
    exact evaluation.map_sub field (projection field)
  have positive : BddBelow (Set.range (fun field : kernelImage => ‖evaluation (projection first) - field.val‖)) :=
    ⟨0, by rintro _ ⟨field, rfl⟩; exact norm_nonneg _⟩
  have minimizing : ‖evaluation (projection first) - 0‖ =
      ⨅ field : kernelImage, ‖evaluation (projection first) - field.val‖ := by
    apply le_antisymm
    · apply le_ciInf
      rintro ⟨_, field, rfl⟩
      change ‖evaluation (projection first) - 0‖ ≤
        ‖evaluation (projection first) - evaluation (field - projection field)‖
      rw [sub_zero, ← map_sub]
      have projected : projection (projection first - (field - projection field)) = projection first := by
        rw [map_sub, map_sub, idempotent, idempotent, sub_self, sub_zero]
      have bounded := contract (projection first - (field - projection field))
      rw [projected] at bounded
      exact bounded
    · exact ciInf_le positive ⟨0, kernelImage.zero_mem⟩
  have orthogonal := (kernelImage.norm_eq_iInf_iff_inner_eq_zero kernelImage.zero_mem).mp minimizing
  have result := orthogonal (evaluation second - evaluation (projection second)) (residual_mem second)
  simpa only [sub_zero] using result

theorem contractiveImage_symmetric {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (evaluation : E →L[ℂ] F) (projection : E →L[ℂ] E)
    (contract : ∀ field, ‖evaluation (projection field)‖ ≤ ‖evaluation field‖)
    (idempotent : ∀ field, projection (projection field) = projection field)
    (first second : E) : inner ℂ (evaluation (projection first)) (evaluation second) =
      inner ℂ (evaluation first) (evaluation (projection second)) := by
  have left := contractiveImage_orthogonal evaluation projection contract idempotent first second
  have right := contractiveImage_orthogonal evaluation projection contract idempotent second first
  rw [inner_sub_right] at left right
  have conjugated := congrArg (star : ℂ → ℂ) (sub_eq_zero.mp right)
  have reverse := (inner_conj_symm (evaluation first) (evaluation (projection second))).symm.trans
    (conjugated.trans (inner_conj_symm (evaluation (projection first)) (evaluation (projection second))))
  exact (sub_eq_zero.mp left).trans reverse.symm

theorem robinTrace_angular_symmetric (mode : ℤ) (first second : highDiskGrade) :
    inner ℂ (robinTrace (highDiskMode mode first)) (robinTrace second) =
      inner ℂ (robinTrace first) (robinTrace (highDiskMode mode second)) :=
  contractiveImage_symmetric robinTrace (highDiskMode mode)
    (fun field => diskBoundary_angular_contract mode field.val)
    (fun field => (highDiskMode_projection mode mode field).trans (if_pos rfl)) first second

end Grad.CircularHighWeak
