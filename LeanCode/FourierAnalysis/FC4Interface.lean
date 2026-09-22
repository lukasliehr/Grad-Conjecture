import FC4GradeCore

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The exact COR04 public boundary: a grade-tagged pullback inner product and
seminorm, its norm laws, coordinate isometry identity, and the literal M2 series. -/
def GradeInnerBlockGoal : Prop :=
  ∀ dimension parameters grade,
    (∃ pulledInner : PreInnerProductSpace.Core ℂ
        (GradeCore parameters dimension grade),
      ∀ first second,
        pulledInner.inner first second = cartesianGradeInner parameters first second) ∧
    (∀ field : GradeCore parameters dimension grade,
      Complex.re (cartesianGradeInner parameters field field) =
        cartesianGradeSeminorm parameters field ^ 2) ∧
    (∀ first second : GradeCore parameters dimension grade,
      cartesianGradeSeminorm parameters (first + second) ≤
        cartesianGradeSeminorm parameters first + cartesianGradeSeminorm parameters second) ∧
    (∀ (scalar : ℂ) (field : GradeCore parameters dimension grade),
      cartesianGradeSeminorm parameters (scalar • field) =
        ‖scalar‖ * cartesianGradeSeminorm parameters field) ∧
    (∀ field : GradeCore parameters dimension grade,
      cartesianGradeSeminorm parameters field =
        ‖gradeCoreCoordinates parameters field‖) ∧
    ∀ field : GradeCore parameters dimension grade,
      cartesianGradeSeminorm parameters field ^ 2 =
        ∑' cell : ℤ, ∑ index : GradeMultiIndex grade,
          cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
            ∫ point : SpatialPlane,
              ‖closedDiskLift
                (closedMultiDerivative
                  (phaseWeightedJet parameters cell (field.toCore.1 cell))
                  index.toCartesian) point‖ ^ 2
                ∂volume.restrict openUnitDisk

end Grad.CartesianState

