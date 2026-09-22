import AJI27ActualUnknownRadialRHS
import AJQ2ActualKnownSourceRHS
import AJO7SameSharedResponseLowPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowClassical

/-- Literal low x algebra, retaining both full row pieces and positive Rg. -/
theorem lowOriginalX_source_split (length radius : ℝ) (nonzero : radius ≠ 0)
    (mode : ℤ × ℤ) (x j c v sourceJ sourceC sourceV f g : ComplexEuclidean 1) :
    (-radius⁻¹) • x +
      (-Complex.I) • (((mode.2 : ℝ) / length) • (c + sourceC)) +
      (-Complex.I) • (((mode.1 : ℝ) * radius⁻¹) • (v + sourceV - radius • g)) =
    (rawOriginalUnknownRHS length radius mode x j c v +
      rawOriginalSourceRHS length radius mode sourceJ sourceC sourceV f g).1 := by
  have radiusC : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  apply PiLp.ext
  intro entry
  simp only [rawOriginalUnknownRHS, rawOriginalSourceRHS, Prod.fst_add,
    frequencyNumerator, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have cast (t : ℝ) : (RCLike.ofReal t : ℂ) = (t : ℂ) := rfl
  simp only [cast]
  push_cast
  simp only [div_eq_mul_inv]
  field_simp [radiusC]
  ring

/-- On the genuine low modes P is the identity, with f inserted once. -/
theorem lowOriginalXi_source_split (length radius : ℝ) (mode : ℤ × ℤ)
    (nonzero : mode.1 ≠ 0) (x j c v sourceJ sourceC sourceV f g : ComplexEuclidean 1) :
    j + sourceJ + f =
      (rawOriginalUnknownRHS length radius mode x j c v +
        rawOriginalSourceRHS length radius mode sourceJ sourceC sourceV f g).2 := by
  simp only [rawOriginalUnknownRHS, rawOriginalSourceRHS, Prod.snd_add,
    if_neg nonzero, one_smul]
  exact add_assoc j sourceJ f

end Grad.AnnularSmoothCore
