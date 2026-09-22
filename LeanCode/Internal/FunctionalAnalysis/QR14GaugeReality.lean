import QR13ValueReality

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.Constraints.Multipliers Grad.GaugeCoefficients.Algebra

theorem planarBasis_conjugate (coordinate : Fin 2) :
    cartesianPhysicalConjugation 2 (planarBasis coordinate) = planarBasis coordinate := by
  apply PiLp.ext
  intro index
  simp [cartesianPhysicalConjugation_apply, planarBasis_apply]

theorem operatorEntry_conjugate (mapping : OperatorValue 2 2) (row column : Fin 2) :
    operatorEntry (operatorConjugation 2 2 mapping) row column =
      conj (operatorEntry mapping row column) := by
  change (cartesianPhysicalConjugation 2 (mapping (cartesianPhysicalConjugation 2
    (planarBasis column)))) row = _
  rw [planarBasis_conjugate]
  rfl

theorem transposeOperator_conjugate (mapping : OperatorValue 2 2) :
    operatorConjugation 2 2 (transposeOperator mapping) =
      transposeOperator (operatorConjugation 2 2 mapping) := by
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [operator_apply_coordinates, operatorEntry_conjugate, transposeOperator_entry]

theorem seedTransposeCells_conjugate (parameter : Seed.Parameters) (cell : ℤ) :
    operatorConjugation 2 2 (seedTransposeCells parameter cell) =
      seedTransposeCells parameter (-cell) := by
  by_cases zero : cell = 0
  · subst cell
    simp [seedTransposeCells, map_add, operatorConjugation_id, transposeOperator_conjugate,
      actualCells_operatorConjugation]
  · simp [seedTransposeCells, zero, transposeOperator_conjugate,
      actualCells_operatorConjugation]

theorem seedTransposeCore_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (seedTransposeCore parameters parameter inside field) =
      seedTransposeCore parameters parameter inside (cartesianCoreConjugation parameters field) :=
  smoothMultiplier_conjugate parameters _ _ (seedTransposeCells_conjugate parameter) field

theorem coordinateCore_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (coordinateCore parameters coordinate field) =
      coordinateCore parameters coordinate (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation dimension
      (point.val coordinate • ((field.1 (-cell)).value point)) =
    point.val coordinate • cartesianPhysicalConjugation dimension ((field.1 (-cell)).value point)
  exact (cartesianPhysicalConjugation dimension).map_smul _ _

theorem planarComponentMap_conjugate (coordinate : Fin 2) :
    operatorConjugation 2 1 (planarComponentMap coordinate) = planarComponentMap coordinate := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 1
    (planarComponentMap coordinate (cartesianPhysicalConjugation 2 vector)) = _
  apply PiLp.ext
  intro index
  fin_cases index
  simp [planarComponentMap, cartesianPhysicalConjugation_apply]

theorem derivativeRowCoefficients_conjugate (parameter : Seed.Parameters)
    (coordinate : Fin 2) (cell : ℤ) :
    operatorConjugation 2 1 (derivativeRowCoefficients parameter coordinate cell) =
      derivativeRowCoefficients parameter coordinate (-cell) := by
  rw [derivativeRowCoefficients, operatorConjugation_comp, planarComponentMap_conjugate,
    transposeOperator_conjugate, actualCells_operatorConjugation]
  rfl

theorem derivativeDotCore_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (derivativeDotCore parameters parameter inside field) =
      derivativeDotCore parameters parameter inside (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (coordinateCore parameters 0 (smoothMultiplier parameters _ _ field) +
      coordinateCore parameters 1 (smoothMultiplier parameters _ _ field)) = _
  rw [map_add, coordinateCore_conjugate, coordinateCore_conjugate,
    smoothMultiplier_conjugate parameters _ _ (derivativeRowCoefficients_conjugate parameter 0),
    smoothMultiplier_conjugate parameters _ _ (derivativeRowCoefficients_conjugate parameter 1)]
  rfl

theorem poloidalCorrection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (poloidalCorrection parameters parameter inside field) =
      poloidalCorrection parameters parameter inside (cartesianCoreConjugation parameters field) := by
  rw [poloidalCorrection_apply, planarInclusionCore_conjugate, seedMatrixCore_conjugate,
    tangentialCore_conjugate, seedTransposeCore_conjugate, planarPartCore_conjugate,
    poloidalCorrection_apply]

theorem toroidalCorrection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (toroidalCorrection parameters parameter inside field) =
      toroidalCorrection parameters parameter inside (cartesianCoreConjugation parameters field) := by
  rw [toroidalCorrection_apply, toroidalInclusionCore_conjugate, angularCore_conjugate,
    neg_zero, map_add, coreConjugation_complex_smul, derivativeDotCore_conjugate,
    toroidalPartCore_conjugate, planarPartCore_conjugate]
  simp only [map_inv₀, Complex.conj_ofReal]
  rfl

theorem triangularGaugeProjection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (triangularGaugeProjection parameters parameter inside field) =
      triangularGaugeProjection parameters parameter inside (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    ((field - poloidalCorrection parameters parameter inside field) -
      toroidalCorrection parameters parameter inside (field - poloidalCorrection parameters parameter inside field)) = _
  rw [map_sub, map_sub, poloidalCorrection_conjugate, toroidalCorrection_conjugate,
    map_sub, poloidalCorrection_conjugate]
  rfl

end Grad.CompletedReality
