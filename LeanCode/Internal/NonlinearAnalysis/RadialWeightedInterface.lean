import ProductInterface
import ClosedJetSmoothExtension
import RadialIntegralBounds
import FC10Extension

noncomputable section

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotient

/-- Literal O8 on each original Fourier coefficient. The accepted smooth
extension only supplies values on the segment already in the closed disk. -/
def integralCoefficient {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) : ComplexEuclidean dimension :=
  radialIntegral (smoothClosedExtension field) point.val

def IsActualRadialIntegral {dimension : ℕ} {parameters : PhaseParameters}
    (field output : ACore parameters dimension) : Prop :=
  ∀ cell point, (output.val cell).value point = integralCoefficient (field.val cell) point

def IsActualDilation {dimension : ℕ} {parameters : PhaseParameters}
    (scale : ℝ) (field output : ACore parameters dimension) : Prop :=
  ∀ (cell : ℤ) (point : ClosedDisk),
    (output.val cell).value point = smoothClosedExtension (field.val cell) (scale • point.val)

/-- O8--O9 on the actual original all-grade core. Construction, linearity,
the literal coefficient law and every same-grade estimate are conclusions. -/
def RadialCoreGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (parameters : PhaseParameters) (dimension : ℕ),
      ∃ mapping : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
        (∀ field, IsActualRadialIntegral field (mapping field)) ∧
        ∀ grade field, originalGradeNorm grade (mapping field) ≤
          constants grade * originalGradeNorm grade field

/-- O10: no analytic-width shrink, no derivative loss, and exactly the
two-dimensional change-of-variables factor t⁻¹. -/
def RadialDilationGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (parameters : PhaseParameters) (dimension : ℕ) (scale : ℝ),
      0 < scale → scale ≤ 1 →
      ∃ mapping : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
        (∀ field, IsActualDilation scale field (mapping field)) ∧
        ∀ grade field, originalGradeNorm grade (mapping field) ≤
          constants grade * scale⁻¹ * originalGradeNorm grade field

/-- The original AGrade completion, with one common literal all-grade core
map and the unchanged dense-core embedding. No extension is a premise. -/
def RadialCompletedGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (parameters : PhaseParameters) (dimension : ℕ),
      ∃ core : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
        (∀ field, IsActualRadialIntegral field (core field)) ∧
        ∀ grade, ∃ completed : AGrade parameters dimension grade →L[ℂ]
            AGrade parameters dimension grade,
          (∀ field : ACore parameters dimension,
            completed (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
              aGradeEta parameters (GradeCore.ofCoreLinear (core field))) ∧
          ∀ field, ‖completed field‖ ≤ constants grade * ‖field‖

def RadialWeightedBlockGoal : Prop :=
  RadialCoreGoal ∧ RadialDilationGoal ∧ RadialCompletedGoal

end Grad.NonlinearRadial
