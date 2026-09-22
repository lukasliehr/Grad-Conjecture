import AXF16RealFiniteCells

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.RealFixedRanges Grad.ChartAxisProjections Grad.ConstrainedGrades

abbrev FlatSourceGradeCore (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade) :=
  LinearMap.range (flatSmoothEmbedding parameters cellLength positive grade large)

def flatGradeEmbedding (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade) :
    FlatSourceGradeCore parameters cellLength positive grade large →ₗᵢ[ℝ]
      flatSourceRange parameters grade large :=
  { (FlatSourceGradeCore parameters cellLength positive grade large).subtype with
    norm_map' := fun _ => rfl }

theorem flatGradeEmbedding_dense (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (flatGradeEmbedding parameters cellLength positive grade large) := by
  apply (flatSmoothEmbedding_denseRange parameters cellLength positive grade large).mono
  rintro _ ⟨source, rfl⟩
  exact ⟨⟨flatSmoothEmbedding parameters cellLength positive grade large source,
    ⟨source, rfl⟩⟩, rfl⟩

def denseRangeCompletionEquiv {E F : Type*} [AddCommMonoid E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (embedding : E →ₗ[ℝ] F) (dense : DenseRange embedding) :
    UniformSpace.Completion (LinearMap.range embedding) ≃ₗᵢ[ℝ] F := by
  let inclusion : LinearMap.range embedding →ₗᵢ[ℝ] F :=
    { (LinearMap.range embedding).subtype with norm_map' := fun _ => rfl }
  have denseInclusion : DenseRange inclusion := by
    apply dense.mono
    rintro _ ⟨source, rfl⟩
    exact ⟨⟨embedding source, ⟨source, rfl⟩⟩, rfl⟩
  exact completionEquiv inclusion denseInclusion

/-- Inferred from the generic range construction to avoid expanding the
actual physical extraction while synthesizing completion instances. -/
def flatSourceCompletionEquiv (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade) :=
  @denseRangeCompletionEquiv _ (flatSourceRange parameters grade large) _ _
    (flatSourceRange parameters grade large).normedAddCommGroup
    (flatSourceRange parameters grade large).normedSpace
    (flatSourceRange_complete parameters grade large)
    (flatSmoothEmbedding parameters cellLength positive grade large)
    (flatSmoothEmbedding_denseRange parameters cellLength positive grade large)

theorem sourceLowering_flat_mem (parameters : PhaseParameters)
    {lower upper : ℕ} (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (source : flatSourceRange parameters upper (large.trans ordered)) :
    sourceLowering parameters large ordered source.val ∈ flatSourceRange parameters lower large := by
  rw [mem_flatSourceRange, ← completedFlatSourceProjection_grade,
    (mem_flatSourceRange parameters upper (large.trans ordered) source.val).mp source.property]

def flatSourceLowering (parameters : PhaseParameters) {lower upper : ℕ}
    (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    flatSourceRange parameters upper (large.trans ordered) →L[ℝ] flatSourceRange parameters lower large :=
  ((sourceLowering parameters large ordered).comp
    (flatSourceRange parameters upper (large.trans ordered)).subtypeL).codRestrict
      (flatSourceRange parameters lower large) (sourceLowering_flat_mem parameters large ordered)

theorem flatSourceLowering_norm_le (parameters : PhaseParameters) {lower upper : ℕ}
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (source : flatSourceRange parameters upper (large.trans ordered)) :
    ‖flatSourceLowering parameters large ordered source‖ ≤ ‖source‖ :=
  sourceLowering_norm_le parameters large ordered source.val

theorem flatSourceLowering_injective (parameters : PhaseParameters) {lower upper : ℕ}
    (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    Function.Injective (flatSourceLowering parameters large ordered) := by
  intro first second equality
  apply Subtype.ext
  exact sourceLowering_injective parameters large ordered (congrArg Subtype.val equality)

theorem flatSourceLowering_core (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) {lower upper : ℕ} (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    flatSourceLowering parameters large ordered
      (flatSmoothEmbedding parameters cellLength positive upper (large.trans ordered) source) =
        flatSmoothEmbedding parameters cellLength positive lower large source :=
  Subtype.ext (sourceLowering_core parameters large ordered source.val)

end Grad.FlatSourceProjection
