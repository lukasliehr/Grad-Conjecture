import OrthogonalPullback

noncomputable section

open Grad.PDEBootstrap Grad.KernelPullback

namespace Grad.KernelArrays

abbrev OrderedFields (rank : ℕ) := PiLp 2 (fun _ : Fin rank → Fin 2 => FieldL2)

def entrywisePullback (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    OrderedFields rank ≃ₗᵢ[ℂ] OrderedFields rank :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin rank → Fin 2 => orthogonalPullback orthogonal)

theorem entrywisePullback_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) (word : Fin rank → Fin 2) :
    entrywisePullback rank orthogonal field word = orthogonalPullback orthogonal (field word) :=
  rfl

theorem entrywisePullback_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) : ‖entrywisePullback rank orthogonal field‖ = ‖field‖ :=
  (entrywisePullback rank orthogonal).norm_map field

theorem entrywisePullback_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    entrywisePullback rank (first.trans second) field =
      entrywisePullback rank first (entrywisePullback rank second field) := by
  apply PiLp.ext
  intro word
  exact orthogonalPullback_trans first second (field word)

theorem entrywisePullback_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    entrywisePullback rank orthogonal.symm (entrywisePullback rank orthogonal field) = field := by
  apply PiLp.ext
  intro word
  exact orthogonalPullback_symm_apply orthogonal (field word)

theorem entrywisePullback_apply_symm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    entrywisePullback rank orthogonal (entrywisePullback rank orthogonal.symm field) = field := by
  apply PiLp.ext
  intro word
  exact orthogonalPullback_apply_symm orthogonal (field word)

end Grad.KernelArrays
