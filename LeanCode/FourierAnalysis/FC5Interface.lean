import FC5Hilbert

noncomputable section

namespace Grad.CartesianState

/-- The exact FA-COR05 public boundary: literal seminorm definiteness on the
actual grade-tagged all-grade core, its induced complex norm/inner product,
and the injective coordinate isometry. -/
def GradeNormDefiniteGoal : Prop :=
  ∀ dimension parameters grade,
    (∀ field : GradeCore parameters dimension grade,
      cartesianGradeSeminorm parameters field = 0 ↔ field = 0) ∧
    Function.Injective (gradeCoreCoordinates parameters :
      GradeCore parameters dimension grade →
        lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2) ∧
    (∀ field : GradeCore parameters dimension grade,
      ‖field‖ = cartesianGradeSeminorm parameters field) ∧
    (∀ first second : GradeCore parameters dimension grade,
      inner ℂ first second = cartesianGradeInner parameters first second) ∧
    (gradeCoreCoordinateIsometry (dimension := dimension) (grade := grade)
      parameters).toLinearMap =
      gradeCoreCoordinates (dimension := dimension) (grade := grade) parameters ∧
    Function.Injective (gradeCoreCoordinateIsometry
      (dimension := dimension) (grade := grade) parameters :
      GradeCore parameters dimension grade →
        lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2)

end Grad.CartesianState
