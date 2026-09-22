import QuotientVectorDerivatives
import AngularCore

noncomputable section

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial

/-- Literal Q3 operator: first D, second R, the actual cell convolution,
then the ordinary angular mean, Cartesian Laplacian and radial integral.
There is no additional projection or shrink of the original width. -/
def bilinearRadialCore {dimension outputDimension : ℕ} (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean dimension) (ComplexEuclidean outputDimension))
    (first second : ACore parameters dimension) : ACore parameters outputDimension :=
  radialCore parameters (laplacianCore parameters (angularCore parameters 0
    (actualMultilinearProduct parameters multiplication
      ![eulerCore parameters first, rotationCore parameters second])))

/-- Q3, strengthened to arbitrary fixed complex-bilinear value maps.
Construction of every operator in the literal composition is already
present; this proposition asks for the exact six-grade/low-four estimate. -/
def RadialQuotientBoundGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (dimension outputDimension : ℕ) (parameters : PhaseParameters)
      (multiplication : ContinuousMultilinearMap ℂ
        (fun _ : Fin 2 => ComplexEuclidean dimension) (ComplexEuclidean outputDimension))
      (first second : ACore parameters dimension) (grade : ℕ),
      originalGradeNorm grade (bilinearRadialCore parameters multiplication first second) ≤
        constants grade * ‖multiplication‖ *
          (originalGradeNorm (grade + 6) first * originalGradeNorm 4 second +
            originalGradeNorm 4 first * originalGradeNorm (grade + 6) second)

end Grad.NonlinearQuotientBounds
