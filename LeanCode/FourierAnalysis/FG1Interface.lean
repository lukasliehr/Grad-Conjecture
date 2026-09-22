import FG1Core
import COR01Proof

noncomputable section

open TopologicalSpace
open scoped BigOperators ENNReal Topology

universe valueUniverse

namespace Grad.FourierGrade

def FrequencyGoal : Prop :=
  ∀ mode : FourierMode,
    frequencyVector mode 0 = (Real.pi / 2) * mode.1 ∧
    frequencyVector mode 1 = (Real.pi / 2) * mode.2.1 ∧
    frequencyVector mode 2 = mode.2.2 ∧
    frequencyWeight mode ^ 2 = 1 + ‖frequencyVector mode‖ ^ 2 ∧
    1 ≤ frequencyWeight mode

def HilbertGoal : Prop :=
  ∀ (dimension grade : ℕ),
    Nonempty (CompleteSpace (JGrade (Grad.ClosedJets.ComplexEuclidean dimension) grade)) ∧
    Nonempty (InnerProductSpace ℂ (JGrade (Grad.ClosedJets.ComplexEuclidean dimension) grade))

def NormGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ) (field : JGrade Value grade),
    ‖field‖ ^ 2 = ∑' mode : FourierMode,
      frequencyWeight mode ^ (2 * grade) * ‖coefficient grade field mode‖ ^ 2

def InclusionGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (high middle low : ℕ) (middleHigh : middle ≤ high) (lowMiddle : low ≤ middle),
    ‖inclusion (Value := Value) high middle middleHigh‖ ≤ 1 ∧
    Function.Injective (inclusion (Value := Value) high middle middleHigh) ∧
    (∀ (field : JGrade Value high) (mode : FourierMode),
      coefficient middle (inclusion (Value := Value) high middle middleHigh field) mode =
      coefficient high field mode) ∧
    inclusion (Value := Value) high high le_rfl = ContinuousLinearMap.id ℂ _ ∧
    (inclusion (Value := Value) middle low lowMiddle).comp
      (inclusion (Value := Value) high middle middleHigh) =
        inclusion (Value := Value) high low (lowMiddle.trans middleHigh)

def FiniteDensityGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ),
    Dense (finiteCoefficientSpan Value grade : Set (JGrade Value grade)) ∧
    Dense (LinearMap.range (coreToGrade (Value := Value) grade) : Set (JGrade Value grade))

def CoreGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (values : JCore Value) (grade source target : ℕ) (ordered : target ≤ source)
    (mode : FourierMode),
    coefficient grade (coreToGrade grade values) mode = values.1 mode ∧
    Function.Injective (coreToGrade (Value := Value) grade) ∧
    inclusion source target ordered (coreToGrade source values) = coreToGrade target values

def BlockGoal : Prop :=
  FrequencyGoal ∧ HilbertGoal ∧ NormGoal.{valueUniverse} ∧
    InclusionGoal.{valueUniverse} ∧ FiniteDensityGoal.{valueUniverse} ∧
    CoreGoal.{valueUniverse}

end Grad.FourierGrade
