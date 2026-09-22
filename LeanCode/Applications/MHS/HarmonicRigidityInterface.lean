import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

open Set

namespace Grad.MainAssembly.HarmonicRigidity

def PiLatticeConstantGoal : Prop :=
  ∀ function : ℝ → ℝ,
    Continuous function →
    (∀ time, ∃ integer : ℤ,
      function time = (integer : ℝ) * Real.pi) →
    ∃ integer : ℤ, ∀ time,
      function time = (integer : ℝ) * Real.pi

def HarmonicNormalSignGoal
    (alphaAngle : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ alpha delta firstParameter secondParameter tangentSign normalSign shift,
    delta ≠ 0 →
    (∀ integer : ℤ, 2 * alpha ≠ (integer : ℝ) * Real.pi) →
    (tangentSign = 1 ∨ tangentSign = -1) →
    (normalSign = 1 ∨ normalSign = -1) →
    (∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
          normalSign * alphaAngle alpha delta firstParameter time =
        (integer : ℝ) * Real.pi) →
    normalSign = 1 ∧
      ∀ time,
        alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
          normalSign * alphaAngle alpha delta firstParameter time = 0

def FirstHarmonicPeriodGoal
    (alphaAngle : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ alpha delta firstParameter secondParameter tangentSign shift,
    delta ≠ 0 →
    (tangentSign = 1 ∨ tangentSign = -1) →
    (∀ time,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
        alphaAngle alpha delta firstParameter time = 0) →
    ∃ integer : ℤ, shift = (integer : ℝ) * (2 * Real.pi)

def SecondHarmonicRigidityGoal
    (alphaAngle : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ alpha delta firstParameter secondParameter tangentSign shift,
    0 < firstParameter → 0 < secondParameter → delta ≠ 0 →
    (tangentSign = 1 ∨ tangentSign = -1) →
    (∃ integer : ℤ, shift = (integer : ℝ) * (2 * Real.pi)) →
    (∀ time,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
        alphaAngle alpha delta firstParameter time = 0) →
    tangentSign = 1 ∧ secondParameter = firstParameter) ∧
  ∀ alpha delta parameter shift,
    (∃ integer : ℤ, shift = (integer : ℝ) * (2 * Real.pi)) →
    ∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta parameter (1 * time + shift) -
          1 * alphaAngle alpha delta parameter time =
        (integer : ℝ) * Real.pi

end Grad.MainAssembly.HarmonicRigidity
