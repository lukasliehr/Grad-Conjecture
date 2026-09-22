import AKDT22ActualAxisChartData

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget

/-- Both possible magnetic signs preserve precisely the SAME zero axis. -/
theorem signedStabilizes_preserves_axis (body axis : Set Vec) (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (axisBody : axis ⊆ body) (zeroSet : ∀ point ∈ body, magnetic point = 0 ↔ point ∈ axis)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (stabilizes : SignedStabilizes body magnetic pressure orthogonal translation) :
    (fun point : Vec => orthogonal point + translation) '' axis = axis := by
  obtain ⟨bodyEquality, _, sign, signValue, magneticEquality⟩ := stabilizes
  have signNonzero : sign ≠ 0 := by rcases signValue with rfl | rfl <;> norm_num
  apply Subset.antisymm
  · rintro point ⟨source, axisIn, rfl⟩
    have sourceIn := axisBody axisIn
    have imageIn : orthogonal source + translation ∈ body := by
      rw [← bodyEquality]
      exact ⟨source, sourceIn, rfl⟩
    apply (zeroSet _ imageIn).mp
    rw [magneticEquality source sourceIn, (zeroSet source sourceIn).mpr axisIn, map_zero, smul_zero]
  · intro point axisIn
    have pointIn := axisBody axisIn
    rw [← bodyEquality] at pointIn
    obtain ⟨source, sourceIn, rfl⟩ := pointIn
    refine ⟨source, ?_, rfl⟩
    have imageIn : orthogonal source + translation ∈ body := axisBody axisIn
    have imageZero := (zeroSet _ imageIn).mpr axisIn
    rw [magneticEquality source sourceIn] at imageZero
    have orthogonalZero := (smul_eq_zero.mp imageZero).resolve_left signNonzero
    apply (zeroSet source sourceIn).mp
    exact orthogonal.injective (orthogonalZero.trans (map_zero orthogonal).symm)

end Grad.PhysicalGeometry
