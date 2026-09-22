import QO10RadialReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped ComplexConjugate BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.CompletedReality

variable {parameters : PhaseParameters}

theorem valueMapCore_conjugate {inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension)
    (real : ∀ value, cartesianPhysicalConjugation outputDimension (mapping value) =
      mapping (cartesianPhysicalConjugation inputDimension value))
    (field : ACore parameters inputDimension) :
    cartesianCoreConjugation parameters (valueMapCore parameters mapping field) =
      valueMapCore parameters mapping (cartesianCoreConjugation parameters field) := by
  apply acore_ext
  intro cell point
  change cartesianPhysicalConjugation outputDimension
    (((valueMapCore parameters mapping field).val (-cell)).value point) = _
  rw [valueMapCore_value, valueMapCore_value]
  exact real _

theorem tangentGeneratorMap_conjugate (value : ComplexEuclidean 3) :
    cartesianPhysicalConjugation 3 (tangentGeneratorMap value) =
      tangentGeneratorMap (cartesianPhysicalConjugation 3 value) := by
  rw [tangentGeneratorMap_value, tangentGeneratorMap_value]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [Grad.NonlinearQuotient.complexTangentGenerator, cartesianPhysicalConjugation]

theorem eTConstantCore_conjugate :
    cartesianCoreConjugation parameters (eTConstantCore parameters) = eTConstantCore parameters := by
  change cartesianCoreConjugation parameters
    (constantCore parameters (EuclideanSpace.single 1 1)) = _
  rw [constantCore_conjugate]
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [cartesianPhysicalConjugation]

theorem affineStateCore_real (cellLength : ℝ) (state : QuotientState parameters)
    (scalarReal : conj (stateScalar state) = stateScalar state)
    (fieldReal : cartesianCoreConjugation parameters (stateField state) = stateField state) :
    cartesianCoreConjugation parameters (affineStateCore parameters cellLength state) =
      affineStateCore parameters cellLength state := by
  rw [affineStateCore, map_add, map_add, timeDerivativeCore_conjugate,
    coreConjugation_complex_smul, coreConjugation_complex_smul,
    valueMapCore_conjugate tangentGeneratorMap tangentGeneratorMap_conjugate,
    eTConstantCore_conjugate, fieldReal, scalarReal, Complex.conj_ofReal]

theorem quotientPolynomialRows_real (cellLength : ℝ) (state : QuotientState parameters)
    (scalarReal : conj (stateScalar state) = stateScalar state)
    (fieldReal : cartesianCoreConjugation parameters (stateField state) = stateField state)
    (potentialReal : cartesianCoreConjugation parameters (statePotential state) = statePotential state) :
    zCoreConjugation parameters (quotientPolynomialRows parameters cellLength state) =
      quotientPolynomialRows parameters cellLength state := by
  have affineReal := affineStateCore_real cellLength state scalarReal fieldReal
  have radialReal : cartesianCoreConjugation parameters
      (quotientDotCurried parameters (stateField state) (stateField state)) =
      quotientDotCurried parameters (stateField state) (stateField state) := by
    rw [quotientDotCurried_conjugate, fieldReal]
  funext coordinate
  fin_cases coordinate
  · change cartesianCoreConjugation parameters
      (quotientPolynomialRows parameters cellLength state 1) =
        quotientPolynomialRows parameters cellLength state 0
    simp only [quotientPolynomialRows, Matrix.cons_val_zero, Matrix.cons_val_one,
      negIStarZConstantCore, izConstantCore,
      map_add, map_sub]
    rw [partialMinusCore_conjugate, dotOperation_conjugate, partialMinusCore_conjugate,
      rotationCore_conjugate, starZMulCore_conjugate, scalarConstantCore_conjugate,
      starZMulCore_conjugate, fieldReal, potentialReal, radialReal]
    simp
  · change cartesianCoreConjugation parameters
      (quotientPolynomialRows parameters cellLength state 0) =
        quotientPolynomialRows parameters cellLength state 1
    simp only [quotientPolynomialRows, Matrix.cons_val_zero, Matrix.cons_val_one,
      negIStarZConstantCore, izConstantCore,
      map_add, map_sub]
    rw [partialPlusCore_conjugate, dotOperation_conjugate, partialPlusCore_conjugate,
      rotationCore_conjugate, zMulCore_conjugate, scalarConstantCore_conjugate,
      zMulCore_conjugate, fieldReal, potentialReal, radialReal]
    simp
  · change cartesianCoreConjugation parameters (removeAngularCore parameters
      (determinantOperation parameters (partialCore parameters 0 (stateField state))
        (partialCore parameters 1 (stateField state)) (affineStateCore parameters cellLength state))) = _
    rw [removeAngularCore_conjugate, determinantOperation_conjugate,
      partialCore_conjugate, partialCore_conjugate, fieldReal, affineReal]
    rfl
  · change cartesianCoreConjugation parameters (removeAngularCore parameters
      (dotOperation parameters (rotationCore parameters (stateField state))
        (affineStateCore parameters cellLength state) - timeDerivativeCore parameters (statePotential state))) = _
    rw [removeAngularCore_conjugate, map_sub, dotOperation_conjugate,
      rotationCore_conjugate, timeDerivativeCore_conjugate, fieldReal, potentialReal, affineReal]
    rfl

end Grad.NonlinearRange
