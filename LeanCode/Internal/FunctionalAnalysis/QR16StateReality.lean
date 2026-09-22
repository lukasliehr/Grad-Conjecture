import QR15BoundaryReality

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.BoundaryTrace Grad.BoundaryLift Grad.Cor18 Grad.SmoothingFamily Grad.AxisJet

theorem scalarInsertion_conjugate (coordinate : Fin 2) :
    operatorConjugation 1 2 (scalarInsertion coordinate) = scalarInsertion coordinate := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 2
    (scalarInsertion coordinate (cartesianPhysicalConjugation 1 vector)) = _
  apply PiLp.ext
  intro index
  simp [cartesianPhysicalConjugation_apply, scalarInsertion_apply, PiLp.single_apply]
  split_ifs <;> simp

theorem coordinateVector_conjugate (parameters : PhaseParameters) (field : ACore parameters 1) :
    cartesianCoreConjugation parameters (coordinateVector parameters field) =
      coordinateVector parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (valueMapCore (scalarInsertion 0) parameters (coordinateCore parameters 0 field) +
      valueMapCore (scalarInsertion 1) parameters (coordinateCore parameters 1 field)) = _
  rw [map_add, valueMapCore_conjugate, valueMapCore_conjugate,
    scalarInsertion_conjugate, scalarInsertion_conjugate,
    coordinateCore_conjugate, coordinateCore_conjugate]
  rfl

theorem collarCorrection_conjugate_of_coefficients (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (first second : BoundaryCore parameters 1)
    (coefficients : ∀ angular cell, second.1 (angular, cell) =
      cartesianPhysicalConjugation 1 (first.1 (-angular, -cell))) :
    cartesianCoreConjugation parameters (collarCorrection parameters parameter inside first) =
      collarCorrection parameters parameter inside second := by
  change cartesianCoreConjugation parameters (planarInclusionCore parameters
    (seedMatrixCore parameters parameter inside (coordinateVector parameters
      (boundaryLift parameters first)))) = _
  rw [planarInclusionCore_conjugate, seedMatrixCore_conjugate, coordinateVector_conjugate,
    boundaryLift_conjugate_of_coefficients parameters first second coefficients]
  rfl

theorem outerCorrection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (outerCorrection parameters parameter inside field) =
      outerCorrection parameters parameter inside (cartesianCoreConjugation parameters field) := by
  rw [outerCorrection_apply, map_sub,
    collarCorrection_conjugate_of_coefficients parameters parameter inside
      (physicalRow parameters parameter inside field)
      (physicalRow parameters parameter inside (cartesianCoreConjugation parameters field))
      (physicalRow_conjugate_coefficient parameters parameter inside field)]
  rfl

/-- Every actual N31 vector-projection factor commutes with ordinary real
conjugation, including the seed-dependent physical row and collar lift. -/
theorem vectorProjection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (vectorProjection parameters parameter inside field) =
      vectorProjection parameters parameter inside (cartesianCoreConjugation parameters field) := by
  rw [vectorProjection_apply, outerCorrection_conjugate, triangularGaugeProjection_conjugate,
    axisJetProjection_conjugate]
  rfl

/-- Literal smooth state commutation, on the actual free-axis/vector/scalar
product. This is the remaining density input of COR22. -/
theorem fullProjection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : StateCore parameters) :
    xCoreConjugation parameters (fullProjection parameters parameter inside field) =
      fullProjection parameters parameter inside (xCoreConjugation parameters field) := by
  simp only [fullProjection_apply, xCoreConjugation, LinearMap.prodMap_apply]
  rw [vectorProjection_conjugate, map_sub, angularCore_conjugate, neg_zero]

end Grad.CompletedReality
