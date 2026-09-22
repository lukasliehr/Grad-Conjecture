import SampledFullGeometry
import CylinderJets

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledFullGeometry.Consumer

open Grad.MainTarget
open Grad.MainTarget.SemanticBridges
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.PhysicalFamily.SampledFullGeometry
open Grad.PhysicalFamily.SampledPositionDerivative
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledAxisBasics
open Grad.MainAssembly.PhysicalNormalHessian

/-- The ambient all-point derivative result descends exactly to the relative
derivative required by `IsConfiguration`, including points on the boundary of
the closed cylinder. -/
theorem sampledRepresentative_derivativeInjective_of_ambient
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper)
    (ambientInjective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective
        (fderiv ℝ
          (sampledPositionCoordinateValue cellLength family period
            parameter.val)
          (coordinateDirection point time)))
    (point : Vec) (pointIn : point ∈ cylinder) :
    Function.Injective (fderivWithin ℝ
      (periodicLift
        (sampledRepresentativeFamily cellLength family period epsilonIn
          potential parameter).position)
      cylinder point) := by
  rw [periodicLift_position_fderivWithin_eq_sampled cellLength family period
    epsilonIn potential parameter point pointIn]
  have pointIdentity : point =
      coordinateDirection (planarPart point) (point 2) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [planarPart, coordinateDirection, vector]
  have functionIdentity :
      (fun argument : Vec =>
        sampledPositionLift cellLength family period parameter.val
          (planarPart argument) (argument 2)) =
      sampledPositionCoordinateValue cellLength family period parameter.val := by
    funext argument
    exact (sampledPositionJointLift_eq cellLength family period
      (parameter.val, argument)).symm
  have mappingDifferentiable : DifferentiableAt ℝ
      (fun argument : Vec =>
        sampledPositionLift cellLength family period parameter.val
          (planarPart argument) (argument 2)) point := by
    rw [functionIdentity, pointIdentity]
    exact sampledPositionCoordinateValue_differentiableAt cellLength family
      period epsilonIn parameter (planarPart point) pointIn (point 2)
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_cylinder point pointIn)
    mappingDifferentiable, functionIdentity, pointIdentity]
  exact ambientInjective (planarPart point) pointIn (point 2)

/-- One public threshold supplies the exact relative-derivative injectivity
clause for every sampled representative. -/
theorem exists_sampledRepresentativeDerivativeThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        ∀ (epsilonIn : sampledEpsilon period ∈
          Set.Ioo (-family.epsilonZero) family.epsilonZero)
          (potential : ℝ) (parameter : Set.Icc family.lower family.upper)
          (point : Vec), point ∈ cylinder →
          Function.Injective (fderivWithin ℝ
            (periodicLift
              (sampledRepresentativeFamily cellLength family period epsilonIn
                potential parameter).position)
            cylinder point) := by
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    exists_sampledPositionFullDerivativeThreshold cellLength
      cellLengthPositive family
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter epsilonIn potential parameter point pointIn
  have ambientThreshold := (threshold period periodAfter).2
  exact sampledRepresentative_derivativeInjective_of_ambient cellLength family
    period epsilonIn potential parameter (ambientThreshold parameter) point
      pointIn

/-- Immediate target consumer.  Once global embedding is supplied, the same
threshold closes the complete `IsConfiguration .smooth` package. -/
theorem sampledRepresentative_isConfiguration_of_embedding_and_fullDerivative
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper)
    (embedding : Topology.IsEmbedding
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter).position)
    (ambientInjective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective
        (fderiv ℝ
          (sampledPositionCoordinateValue cellLength family period
            parameter.val)
          (coordinateDirection point time))) :
    IsConfiguration .smooth
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter) := by
  apply sampledRepresentative_isConfiguration_of_embedding cellLength family
    period epsilonIn potential parameter embedding
  intro point pointIn
  exact sampledRepresentative_derivativeInjective_of_ambient cellLength family
    period epsilonIn potential parameter ambientInjective point pointIn

end Grad.PhysicalFamily.SampledFullGeometry.Consumer
