import FT4ExactDerivatives

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ContDiff

namespace Grad.FourierGrade.P1315

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- P13 on the literal probability product torus and the actual
finite-dimensional Euclidean value carrier. -/
def ParsevalGoal : Prop :=
  ∀ (dimension : ℕ) (field : EuclideanTorusL2 dimension),
    HasSum (euclideanVectorFourierTerm field) field ∧
      (∫ point : ProductTorus, ‖field point‖ ^ 2) =
        ∑' mode : FourierMode, ‖euclideanTorusCoefficient field mode‖ ^ 2

/-- P14's literal weighted Fourier-grade square norm. -/
def WeightedGradeGoal : Prop :=
  ∀ (dimension grade : ℕ)
    (field : JGrade (Grad.ClosedJets.ComplexEuclidean dimension) grade),
    ‖field‖ ^ 2 = gradeSequenceEnergy grade (coefficient grade field)

/-- P15 with exactly the factors `4⁻q` and `binom(q+3,3)`, for the actual
    unordered sum of squared `L²` norms of the reconstructed mixed derivatives. -/
def DerivativeComparisonGoal : Prop :=
  ∀ (dimension grade : ℕ)
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)),
    derivativeCount grade = Nat.choose (grade + 3) 3 ∧
      ((4 : ℝ) ^ grade)⁻¹ * ‖coreToGrade grade values‖ ^ 2 ≤
        actualDerivativeEnergy grade values ∧
      actualDerivativeEnergy grade values ≤
        (Nat.choose (grade + 3) 3 : ℝ) * ‖coreToGrade grade values‖ ^ 2 ∧
      (∀ (index : FourierMultiIndex) (y₁ y₂ ζ : ℝ),
        physicalMixedDerivative index (reconstructedPhysical values)
            (physicalPoint y₁ y₂ ζ) =
          torusMixedDerivative index values
            (normalizedTorusPoint y₁ y₂ ζ))

/-- P15's all-grade reconstruction: one uniformly convergent torus field,
one smooth physical representative with the exact P10 phase, and recovery of
every original vector coefficient. -/
def SmoothReconstructionGoal : Prop :=
  ∀ (dimension : ℕ)
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)),
    HasSum
        (fun mode : FourierMode => vectorTorusTerm mode (values.1 mode))
        (reconstructedTorus values) ∧
      ContDiff ℝ ∞ (reconstructedPhysical values) ∧
      (∀ y₁ y₂ ζ : ℝ,
        reconstructedPhysical values (physicalPoint y₁ y₂ ζ) =
          reconstructedTorus values (normalizedTorusPoint y₁ y₂ ζ)) ∧
      (∀ mode : FourierMode,
        UnitAddTorus.mFourierCoeff (reconstructedTorus values) (modeVector mode) =
          values.1 mode)

/-- The exact public P13--P15 Fourier/Sobolev prerequisite block. -/
def BlockGoal : Prop :=
  ParsevalGoal ∧ WeightedGradeGoal ∧ DerivativeComparisonGoal ∧
    SmoothReconstructionGoal

end Grad.FourierGrade.P1315
