import QO16ChartNormalization
import QO17ScalarMean

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality

variable {parameters : PhaseParameters}

theorem tameScalarMultiplier_conjugate {dimension : ℕ} [Nontrivial (ComplexEuclidean dimension)]
    (family : TameCoefficient parameters) (real : ∀ cell, family.val (-cell) = conj (family.val cell))
    (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (tameScalarMultiplier dimension family field) =
      tameScalarMultiplier dimension family (cartesianCoreConjugation parameters field) := by
  apply smoothMultiplier_conjugate
  intro cell
  change operatorConjugation dimension dimension
    (family.val cell • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) =
      family.val (-cell) • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)
  rw [operatorConjugation_complex_smul, operatorConjugation_id, real]

theorem physicalBasis_real (dimension : ℕ) (index : Fin dimension) :
    cartesianPhysicalConjugation dimension (EuclideanSpace.single index 1) = EuclideanSpace.single index 1 := by
  apply PiLp.ext
  intro coordinate
  simp [cartesianPhysicalConjugation]

theorem tameCoordinateScalarField_real (coordinate : Fin 2) :
    cartesianCoreConjugation parameters (tameCoordinateScalarField parameters coordinate) =
      tameCoordinateScalarField parameters coordinate := by
  rw [tameCoordinateScalarField, singleton_coordinate]
  change cartesianCoreConjugation parameters
    (coordinateCore parameters coordinate (constantCore parameters (EuclideanSpace.single 0 1))) = _
  rw [coordinateCore_conjugate, constantCore_conjugate, physicalBasis_real]
  rfl

theorem tamePlanarCoordinateField_real :
    cartesianCoreConjugation parameters (tamePlanarCoordinateField parameters) = tamePlanarCoordinateField parameters := by
  rw [tamePlanarCoordinateField, singleton_coordinate, singleton_coordinate]
  change cartesianCoreConjugation parameters
    (coordinateCore parameters 0 (constantCore parameters (EuclideanSpace.single 0 1)) +
      coordinateCore parameters 1 (constantCore parameters (EuclideanSpace.single 1 1))) = _
  rw [map_add, coordinateCore_conjugate, coordinateCore_conjugate,
    constantCore_conjugate, constantCore_conjugate, physicalBasis_real, physicalBasis_real]
  rfl

theorem tamePlanarInclusion_real (vector : ComplexEuclidean 2) :
    cartesianPhysicalConjugation 3 (tamePlanarInclusion vector) =
      tamePlanarInclusion (cartesianPhysicalConjugation 2 vector) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · rfl
  · exact map_zero (starRingEnd ℂ)
  · rfl

theorem tameTangentInclusion_real (vector : ComplexEuclidean 1) :
    cartesianPhysicalConjugation 3 (tameTangentInclusion vector) =
      tameTangentInclusion (cartesianPhysicalConjugation 1 vector) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · exact map_zero (starRingEnd ℂ)
  · rfl
  · exact map_zero (starRingEnd ℂ)

theorem tameSeedField_real (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    cartesianCoreConjugation parameters (tameSeedField parameters seed inside) = tameSeedField parameters seed inside := by
  rw [tameSeedField, valueMapCore_conjugate tamePlanarInclusion tamePlanarInclusion_real,
    tameSeedPlanarField, seedMatrixCore_conjugate, tamePlanarCoordinateField_real]

theorem tameRadiusSquareField_real :
    cartesianCoreConjugation parameters (tameRadiusSquareField parameters) = tameRadiusSquareField parameters := by
  rw [tameRadiusSquareField, map_add, coordinateCore_conjugate, coordinateCore_conjugate,
    tameCoordinateScalarField_real, tameCoordinateScalarField_real]

theorem tameSeedEnergy_real (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    cartesianCoreConjugation parameters (tameSeedEnergy parameters seed inside) = tameSeedEnergy parameters seed inside := by
  have expression : tameSeedEnergy parameters seed inside =
      dotOperation parameters (rotationCore parameters (tameSeedField parameters seed inside))
        (rotationCore parameters (tameSeedField parameters seed inside)) - tameRadiusSquareField parameters := by
    rw [tameSeedEnergy, dotOperation, pairProductLinear_apply]
  rw [expression, map_sub, dotOperation_conjugate, rotationCore_conjugate,
    tameSeedField_real, tameRadiusSquareField_real]

theorem tameSeedScalar_real (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    cartesianCoreConjugation parameters (tameSeedScalar parameters seed inside) = tameSeedScalar parameters seed inside := by
  rw [tameSeedScalar, coreConjugation_complex_smul, rotationCore_conjugate, tameSeedEnergy_real]
  have scalar : conj (-(4 : ℂ)⁻¹) = -(4 : ℂ)⁻¹ := by
    rw [map_neg, map_inv₀]
    congr 2
    exact Complex.conj_ofReal (4 : ℝ)
  rw [scalar]

theorem normalizedChart_real (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (real : RealTangent state.1) (axis : ChartAxisCondition state)
    (vectorReal : cartesianCoreConjugation parameters state.2.1 = state.2.1)
    (scalarReal : cartesianCoreConjugation parameters state.2.2 = state.2.2) :
    cartesianCoreConjugation parameters (normalizedChart parameters seed inside state).1 =
        (normalizedChart parameters seed inside state).1 ∧
      cartesianCoreConjugation parameters (normalizedChart parameters seed inside state).2 =
        (normalizedChart parameters seed inside state).2 := by
  constructor
  · change cartesianCoreConjugation parameters
      (tameScalarMultiplier 3 (rootChart state.1) (tameSeedField parameters seed inside) +
        valueMapCore parameters tameTangentInclusion
          (tameScalarMultiplier 1 (tangentComponent state.1 0) (tameCoordinateScalarField parameters 0) +
            tameScalarMultiplier 1 (tangentComponent state.1 1) (tameCoordinateScalarField parameters 1)) +
        state.2.1) = _
    rw [map_add, map_add, tameScalarMultiplier_conjugate _ (rootChart_real state.1 real axis),
      tameSeedField_real, valueMapCore_conjugate tameTangentInclusion tameTangentInclusion_real,
      map_add, tameScalarMultiplier_conjugate _ (fun cell => real cell 0),
      tameScalarMultiplier_conjugate _ (fun cell => real cell 1),
      tameCoordinateScalarField_real, tameCoordinateScalarField_real, vectorReal]
    rfl
  · change cartesianCoreConjugation parameters (tameSeedScalar parameters seed inside + state.2.2) = _
    rw [map_add, tameSeedScalar_real, scalarReal]
    rfl

end Grad.NonlinearRange
