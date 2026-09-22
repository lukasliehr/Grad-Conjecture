import AW2Proof
import Mathlib.Data.Finset.Sort

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers Grad.AnalyticWeights.Calculus
open scoped BigOperators ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Higher

universe valueUniverse

def profile (point : Spatial) : ℝ := Real.sqrt (1 + ‖point‖ ^ 2) - 1

def phaseDifference (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial) : ℝ :=
  physicalPhase sigma gamma scale output point - physicalPhase sigma gamma scale input point

def weightRatio (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial) : ℝ :=
  physicalWeight sigma gamma scale output point * inverseWeight sigma gamma scale input point

def weightCost (rank : ℕ) (gamma scale : ℝ) : ℝ :=
  if rank = 0 then 1 else gamma * (1 + gamma) ^ (rank - 1) * scale ^ rank

def allocationPolynomial (rank : ℕ) (output input : ℤ) : ℝ :=
  ∑ displacementOrder ∈ Finset.Icc 1 rank,
    Grad.CellWeights.cellWeight (output - input) ^ displacementOrder *
      Grad.CellWeights.cellWeight input ^ (rank - displacementOrder)

def orderedDerivative {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (word : Fin rank → Fin 2) (function : Spatial → Value) (point : Spatial) : Value :=
  iteratedFDeriv ℝ rank function point (fun position => spatialDirection (word position))

def orderedTensor {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (function : Spatial → Value) (point : Spatial) : Tensor rank Value :=
  tensorOfCoordinates rank (fun word => orderedDerivative rank word function point)

def DerivativeBound {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (function : Spatial → Value) (point : Spatial) (bound : ℝ) : Prop :=
  ‖iteratedFDeriv ℝ rank function point‖ ≤ bound ∧ ‖orderedTensor rank function point‖ ≤ bound

def subword {rank : ℕ} (word : Fin rank → Fin 2) (selected : Finset (Fin rank)) :
    Fin selected.card → Fin 2 := fun position => word (selected.orderEmbOfFin rfl position)

def selectedDerivative {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {rank : ℕ} (word : Fin rank → Fin 2) (selected : Finset (Fin rank))
    (function : Spatial → Value) (point : Spatial) : Value :=
  orderedDerivative selected.card (subword word selected) function point

def allocationFiber {rank : ℕ} (allocation : Fin rank → Fin 3) (label : Fin 3) : Finset (Fin rank) :=
  Finset.univ.filter (fun position => allocation position = label)

def conjugatedCoefficient {inputDimension outputDimension : ℕ}
    (sigma gamma scale : ℝ) (output input : ℤ)
    (coefficient : Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (point : Spatial) : PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  weightRatio sigma gamma scale output input point • coefficient point

def CoordinateGoal : Prop :=
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
      (rank : ℕ) (function : Spatial → Value) (point : Spatial),
    ‖orderedTensor rank function point‖ ^ 2 =
      ∑ word : Fin rank → Fin 2, ‖orderedDerivative rank word function point‖ ^ 2) ∧
  (∀ (rank : ℕ) (word : Fin rank → Fin 2) (function : Spatial → ℝ),
    orderedDerivative rank word function = Grad.WeakTesting.orderedTestDerivative rank word function)

def RankZeroGoal : Prop :=
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
      (word : Fin 0 → Fin 2) (function : Spatial → Value) (point : Spatial),
    orderedDerivative 0 word function point = function point ∧
    ‖iteratedFDeriv ℝ 0 function point‖ = ‖function point‖ ∧
    ‖orderedTensor 0 function point‖ = ‖function point‖) ∧
  (∀ (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial),
    weightCost 0 gamma scale = 1 ∧ allocationPolynomial 0 output input = 0 ∧
    physicalWeight sigma gamma scale output point * inverseWeight sigma gamma scale output point = 1 ∧
    weightRatio sigma gamma scale output input point =
      Real.exp (phaseDifference sigma gamma scale output input point))

def CellGoal : Prop :=
  ∀ output input : ℤ,
    |Grad.CellWeights.cellWeight output - Grad.CellWeights.cellWeight input| ≤ |((output - input : ℤ) : ℝ)| ∧
    Grad.CellWeights.cellWeight output ≤ Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|

def RatioGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial),
    0 < weightRatio sigma gamma scale output input point ∧
    weightRatio sigma gamma scale output input point =
      Real.exp (phaseDifference sigma gamma scale output input point) ∧
    ContDiff ℝ ∞ (weightRatio sigma gamma scale output input) ∧
    (∀ orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial,
      weightRatio sigma gamma scale output input (orthogonal point) =
        weightRatio sigma gamma scale output input point) ∧
    (0 ≤ gamma → 0 ≤ scale → 0 ≤ rate sigma gamma (scale * ‖point‖) →
      weightRatio sigma gamma scale output input point ≤
        Real.exp (sigma + gamma) * envelope sigma gamma scale output input point)

def ProfileGoal (constant : ℕ → ℝ) : Prop :=
  ContDiff ℝ ∞ profile ∧ ∀ (rank : ℕ), 1 ≤ rank → ∀ point : Spatial,
    ‖iteratedFDeriv ℝ rank profile point‖ ≤ constant rank / Real.sqrt (1 + ‖point‖ ^ 2) ^ (rank - 1) ∧
    ‖point‖ * ‖iteratedFDeriv ℝ (rank + 1) profile point‖ ≤
      constant rank / Real.sqrt (1 + ‖point‖ ^ 2) ^ (rank - 1)

def PhaseGoal (constant : ℕ → ℝ) : Prop :=
  ∀ (sigma gamma scale : ℝ), 0 ≤ gamma → 0 ≤ scale →
    ∀ (rank : ℕ), 1 ≤ rank → ∀ (output input : ℤ) (point : Spatial),
      DerivativeBound rank (physicalPhase sigma gamma scale output) point
        (constant rank * gamma * scale ^ rank * Grad.CellWeights.cellWeight output ^ rank) ∧
      DerivativeBound rank (phaseDifference sigma gamma scale output input) point
        (constant rank * gamma * scale ^ rank * |((output - input : ℤ) : ℝ)| *
          (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ (rank - 1))

def ExponentialGoal (constant : ℕ → ℝ) : Prop :=
  ∀ (sigma gamma scale : ℝ), 0 ≤ gamma → 0 ≤ scale →
    ∀ (rank : ℕ), 1 ≤ rank → ∀ (output input : ℤ) (point : Spatial),
      DerivativeBound rank (weightRatio sigma gamma scale output input) point
        (constant rank * weightCost rank gamma scale * weightRatio sigma gamma scale output input point *
          allocationPolynomial rank output input)

def WeightGoal (constant : ℕ → ℝ) : Prop :=
  ∀ (sigma gamma scale : ℝ), 0 ≤ gamma → 0 ≤ scale →
    ∀ (rank : ℕ), 1 ≤ rank → ∀ (cell : ℤ) (point : Spatial),
      DerivativeBound rank (physicalWeight sigma gamma scale cell) point
        (constant rank * weightCost rank gamma scale * physicalWeight sigma gamma scale cell point *
          Grad.CellWeights.cellWeight cell ^ rank) ∧
      DerivativeBound rank (inverseWeight sigma gamma scale cell) point
        (constant rank * weightCost rank gamma scale * inverseWeight sigma gamma scale cell point *
          Grad.CellWeights.cellWeight cell ^ rank)

def DiagonalGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (sigma gamma scale : ℝ) (cell : ℤ) (rank : ℕ) (word : Fin rank → Fin 2)
    (function : Spatial → Value) (point : Spatial), ContDiffAt ℝ ∞ function point →
      physicalWeight sigma gamma scale cell point •
          orderedDerivative rank word (fun source => inverseWeight sigma gamma scale cell source • function source) point =
        ∑ selected : Finset (Fin rank),
          (physicalWeight sigma gamma scale cell point *
            selectedDerivative word selected (inverseWeight sigma gamma scale cell) point) •
              selectedDerivative word selectedᶜ function point

def DiagonalBoundGoal (constant : ℕ → ℝ) : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (sigma gamma scale : ℝ), 0 ≤ gamma → 0 ≤ scale →
    ∀ (cell : ℤ) (rank : ℕ) (word : Fin rank → Fin 2) (selected : Finset (Fin rank))
      (function : Spatial → Value) (point : Spatial),
      ‖(physicalWeight sigma gamma scale cell point *
          selectedDerivative word selected (inverseWeight sigma gamma scale cell) point) •
            selectedDerivative word selectedᶜ function point‖ ≤
        constant selected.card * weightCost selected.card gamma scale *
          ‖(Grad.CellWeights.cellWeight cell ^ selected.card) • selectedDerivative word selectedᶜ function point‖

def CoefficientGoal : Prop :=
  (∀ (inputDimension outputDimension : ℕ) (sigma gamma scale : ℝ) (output input : ℤ)
    (rank : ℕ) (word : Fin rank → Fin 2)
    (coefficient : Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (point : Spatial), ContDiffAt ℝ ∞ coefficient point →
      orderedDerivative rank word (conjugatedCoefficient sigma gamma scale output input coefficient) point =
        ∑ selected : Finset (Fin rank),
          selectedDerivative word selected (weightRatio sigma gamma scale output input) point •
            selectedDerivative word selectedᶜ coefficient point) ∧
  (∀ (inputDimension outputDimension : ℕ) (sigma gamma scale : ℝ) (output input : ℤ)
    (rank : ℕ) (word : Fin rank → Fin 2)
    (coefficient : Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (function : Spatial → PhysicalValue inputDimension) (point : Spatial),
    ContDiffAt ℝ ∞ coefficient point → ContDiffAt ℝ ∞ function point →
      orderedDerivative rank word (fun source =>
          conjugatedCoefficient sigma gamma scale output input coefficient source (function source)) point =
        ∑ allocation : Fin rank → Fin 3,
          selectedDerivative word (allocationFiber allocation 0) (weightRatio sigma gamma scale output input) point •
            ((selectedDerivative word (allocationFiber allocation 1) coefficient point)
              (selectedDerivative word (allocationFiber allocation 2) function point)))

def CoefficientBoundGoal (constant : ℕ → ℝ) : Prop :=
  ∀ (inputDimension outputDimension : ℕ) (sigma gamma scale : ℝ), 0 ≤ gamma → 0 ≤ scale →
    ∀ (output input : ℤ) (phaseRank coefficientRank inputRank : ℕ), 1 ≤ phaseRank →
      ∀ (phaseWord : Fin phaseRank → Fin 2) (coefficientWord : Fin coefficientRank → Fin 2)
        (inputWord : Fin inputRank → Fin 2)
        (coefficient : Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
        (function : Spatial → Grad.GenericCarriers.CellValues inputDimension) (point : Spatial),
        ‖orderedDerivative phaseRank phaseWord (weightRatio sigma gamma scale output input) point •
            ((orderedDerivative coefficientRank coefficientWord coefficient point)
              (orderedDerivative inputRank inputWord (fun source => function source input) point))‖ ≤
          constant phaseRank * weightCost phaseRank gamma scale * weightRatio sigma gamma scale output input point *
            ‖orderedDerivative coefficientRank coefficientWord coefficient point‖ *
              ∑ displacementOrder ∈ Finset.Icc 1 phaseRank,
                Grad.CellWeights.cellWeight (output - input) ^ displacementOrder *
                  ‖(Grad.CellWeights.cellWeight input ^ (phaseRank - displacementOrder)) •
                    orderedDerivative inputRank inputWord (fun source => function source input) point‖

def AllocationGoal : Prop :=
  (∀ (rank : ℕ) (allocation : Fin rank → Fin 3),
    (allocationFiber allocation 0).card + (allocationFiber allocation 1).card +
      (allocationFiber allocation 2).card = rank) ∧
  (∀ (phaseRank coefficientRank inputRank displacementOrder : ℕ),
    displacementOrder ∈ Finset.Icc 1 phaseRank →
      1 ≤ coefficientRank + displacementOrder ∧
      (coefficientRank + displacementOrder) + (inputRank + (phaseRank - displacementOrder)) =
        phaseRank + coefficientRank + inputRank) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
      (rank : ℕ) (output input : ℤ) (value : Value),
    ‖(Grad.CellWeights.cellWeight output ^ rank) • value‖ ≤
      ∑ displacementOrder ∈ Finset.range (rank + 1),
        (Nat.choose rank displacementOrder : ℝ) * |((output - input : ℤ) : ℝ)| ^ displacementOrder *
          ‖(Grad.CellWeights.cellWeight input ^ (rank - displacementOrder)) • value‖)

def AxisGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (output input : ℤ) (first second : Spatial),
    iteratedFDeriv ℝ 2 (phaseDifference sigma gamma scale output input) 0 ![first, second] =
      -gamma * scale ^ 2 * (Grad.CellWeights.cellWeight output ^ 2 - Grad.CellWeights.cellWeight input ^ 2) *
        inner ℝ first second ∧
    iteratedFDeriv ℝ 2 (weightRatio sigma gamma scale output input) 0 ![first, second] =
      weightRatio sigma gamma scale output input 0 *
        (-gamma * scale ^ 2 * (Grad.CellWeights.cellWeight output ^ 2 - Grad.CellWeights.cellWeight input ^ 2) *
          inner ℝ first second)

def ZeroScaleGoal : Prop :=
  ∀ (sigma gamma : ℝ) (rank : ℕ), 1 ≤ rank → ∀ (output input : ℤ) (point : Spatial),
    iteratedFDeriv ℝ rank (phaseDifference sigma gamma 0 output input) point = 0 ∧
    iteratedFDeriv ℝ rank (weightRatio sigma gamma 0 output input) point = 0 ∧
    iteratedFDeriv ℝ rank (physicalWeight sigma gamma 0 output) point = 0 ∧
    iteratedFDeriv ℝ rank (inverseWeight sigma gamma 0 output) point = 0

def BlockGoal : Prop :=
  CoordinateGoal.{valueUniverse} ∧ RankZeroGoal.{valueUniverse} ∧ CellGoal ∧ RatioGoal ∧
    DiagonalGoal.{valueUniverse} ∧ CoefficientGoal ∧ AllocationGoal.{valueUniverse} ∧ AxisGoal ∧ ZeroScaleGoal ∧
    ∃ constant : ℕ → ℝ, constant 0 = 1 ∧ (∀ rank, 0 < constant rank) ∧
      ProfileGoal constant ∧ PhaseGoal constant ∧ ExponentialGoal constant ∧ WeightGoal constant ∧
      DiagonalBoundGoal.{valueUniverse} constant ∧ CoefficientBoundGoal constant

end Grad.AnalyticWeights.Higher
