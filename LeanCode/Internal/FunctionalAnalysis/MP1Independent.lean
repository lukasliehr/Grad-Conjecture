import MP1Calculus
import MP1Bump

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped ContDiff

namespace Grad.Mollifier.Pointwise

theorem independentGoal : IndependentGoal :=
  ⟨localGoal, kernelDerivativeGoal, pointwiseGoal, independenceGoal, bumpGoal, scalingGoal⟩

namespace Consumer

universe valueUniverse

theorem independentBlock : IndependentGoal := independentGoal

theorem smoothKernelValue (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ kernel) (compactSupport : HasCompactSupport kernel)
    (field : DomainL2 Value Set.univ) :
    ContDiff ℝ ∞ (smoothRepresentative Value kernel field) ∧
      ∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
        Integrable (fun source : Spatial =>
          (iteratedFDeriv ℝ rank kernel (point - source)
            (fun position => spatialDirection (word position))) • field source) volume ∧
        iteratedFDeriv ℝ rank (smoothRepresentative Value kernel field) point
            (fun position => spatialDirection (word position)) =
          ∫ source : Spatial,
            (iteratedFDeriv ℝ rank kernel (point - source)
              (fun position => spatialDirection (word position))) • field source :=
  (pointwiseGoal Value kernel smoothness compactSupport field).2

theorem scaledKernelValue (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (epsilon : ℝ) (positive : 0 < epsilon)
    (field : DomainL2 Value Set.univ) :
    ContDiff ℝ ∞ (smoothRepresentative Value (scaledEta epsilon) field) ∧
      ∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
        Integrable (fun source : Spatial =>
          orderedDerivative rank word (scaledEta epsilon) (point - source) • field source) volume ∧
        orderedDerivative rank word (smoothRepresentative Value (scaledEta epsilon) field) point =
          ∫ source : Spatial,
            orderedDerivative rank word (scaledEta epsilon) (point - source) • field source :=
  (pointwiseGoal Value (scaledEta epsilon) (scaledEta_contDiff epsilon)
    (scaledEta_compactSupport epsilon positive) field).2

theorem canonicalCells (dimension : ℕ) (epsilon : ℝ) (positive : 0 < epsilon)
    (field : FieldL2 dimension Set.univ) :
    ContDiff ℝ ∞ (smoothRepresentative (CellValues dimension) (scaledEta epsilon) field) ∧
      ∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
        Integrable (fun source : Spatial =>
          orderedDerivative rank word (scaledEta epsilon) (point - source) • field source) volume ∧
        orderedDerivative rank word
            (smoothRepresentative (CellValues dimension) (scaledEta epsilon) field) point =
          ∫ source : Spatial,
            orderedDerivative rank word (scaledEta epsilon) (point - source) • field source :=
  scaledKernelValue (CellValues dimension) epsilon positive field

theorem aeRepresentativeIndependence (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (field : DomainL2 Value Set.univ) (representative : Spatial → Value)
    (represented : representative =ᵐ[volume] field) :
    (fun point => ∫ source : Spatial, kernel (point - source) • representative source) =
      smoothRepresentative Value kernel field :=
  independenceGoal Value kernel field representative represented

theorem zeroRank (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (field : DomainL2 Value Set.univ) (word : Fin 0 → Fin 2) :
    orderedDerivative 0 word (smoothRepresentative Value kernel field) =
      smoothRepresentative Value kernel field := orderedDerivative_zero word _

theorem zeroDimension (epsilon : ℝ) (positive : 0 < epsilon) (field : FieldL2 0 Set.univ) :
    ContDiff ℝ ∞ (smoothRepresentative (CellValues 0) (scaledEta epsilon) field) :=
  (canonicalCells 0 epsilon positive field).1

theorem radialMassOne : BumpGoal := bumpGoal

theorem allPositiveScales : ScalingGoal := scalingGoal

end Consumer

end Grad.Mollifier.Pointwise
