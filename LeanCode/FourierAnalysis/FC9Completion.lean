import FC5Proof
import Mathlib.Analysis.InnerProductSpace.Completion

noncomputable section

open Set

namespace Grad.CartesianState

/-- The actual norm completion of the COR05 grade-tagged original core. -/
abbrev AGrade (parameters : PhaseParameters) (dimension grade : ℕ) :=
  UniformSpace.Completion (GradeCore parameters dimension grade)

/-- The canonical complex-linear isometric dense core embedding `eta_q`. -/
def aGradeEta {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →ₗᵢ[ℂ]
      AGrade parameters dimension grade :=
  UniformSpace.Completion.toComplₗᵢ

theorem aGradeEta_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    aGradeEta parameters field =
      (field : UniformSpace.Completion
        (GradeCore parameters dimension grade)) := rfl

/-- The exact original-grade norm is retained by the completion embedding. -/
theorem aGradeEta_norm {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    ‖aGradeEta parameters field‖ = ‖field‖ :=
  (aGradeEta parameters).norm_map field

/-- On the dense core the completion norm is literally the COR04/COR05 M2
seminorm, not a Sobolev or later `J`-grade norm. -/
theorem aGradeEta_norm_eq_cartesianGradeSeminorm {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    ‖aGradeEta parameters field‖ = cartesianGradeSeminorm parameters field := by
  rw [aGradeEta_norm, gradeCore_norm_eq_cartesianGradeSeminorm]

theorem aGradeEta_inner {dimension grade : ℕ} (parameters : PhaseParameters)
    (first second : GradeCore parameters dimension grade) :
    inner ℂ (aGradeEta parameters first) (aGradeEta parameters second) =
      cartesianGradeInner parameters first second := by
  rw [aGradeEta_apply, aGradeEta_apply,
    UniformSpace.Completion.inner_coe,
    gradeCore_inner_eq_cartesianGradeInner]

/-- The canonical image of the original grade core is dense in its actual
norm completion. -/
theorem aGradeEta_denseRange {dimension grade : ℕ} (parameters : PhaseParameters) :
    DenseRange (aGradeEta parameters :
      GradeCore parameters dimension grade → AGrade parameters dimension grade) := by
  change DenseRange ((↑) : GradeCore parameters dimension grade →
    UniformSpace.Completion (GradeCore parameters dimension grade))
  exact UniformSpace.Completion.denseRange_coe

theorem aGradeEta_injective {dimension grade : ℕ} (parameters : PhaseParameters) :
    Function.Injective (aGradeEta parameters :
      GradeCore parameters dimension grade → AGrade parameters dimension grade) :=
  (aGradeEta parameters).injective

/-- Named evidence for the completion's complete metric structure. -/
theorem aGradeCompleteSpace {dimension grade : ℕ} (parameters : PhaseParameters) :
    CompleteSpace (AGrade parameters dimension grade) := inferInstance

/-- Named evidence for the complex Hilbert inner-product structure. -/
abbrev aGradeComplexInnerProductSpace {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    InnerProductSpace ℂ (AGrade parameters dimension grade) := inferInstance

/-- The explicit real scalar restriction of the complex Hilbert structure.
It is named rather than installed globally, avoiding an instance diamond. -/
abbrev aGradeRealInnerProductSpace {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    InnerProductSpace ℝ (AGrade parameters dimension grade) :=
  InnerProductSpace.rclikeToReal ℂ (AGrade parameters dimension grade)

theorem aGrade_real_inner_eq_re_complex {dimension grade : ℕ}
    (parameters : PhaseParameters) (first second : AGrade parameters dimension grade) :
    (Inner.rclikeToReal ℂ (AGrade parameters dimension grade)).inner first second =
      Complex.re (inner ℂ first second) := rfl

end Grad.CartesianState
