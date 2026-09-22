import GaugeProjectionBounds

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

variable (phase : PhaseParameters) (parameter : Seed.Parameters)

theorem zeroJets_add {dimension : ℕ} {first second : ClosedJet dimension}
    (firstZero : ZeroCartesianFirstJets first) (secondZero : ZeroCartesianFirstJets second) :
    ZeroCartesianFirstJets (first + second) := by
  intro order orderBound word
  have expand := congrFun (congrArg ContinuousMap.toFun
    ((closedDerivativeLinear order word).map_add first second))
    ⟨0, by simp [closedUnitDisk]⟩
  change closedDerivative (first + second) order word ⟨0, by simp [closedUnitDisk]⟩ = 0
  rw [show closedDerivative (first + second) order word ⟨0, by simp [closedUnitDisk]⟩ =
    closedDerivative first order word ⟨0, by simp [closedUnitDisk]⟩ +
      closedDerivative second order word ⟨0, by simp [closedUnitDisk]⟩ from expand]
  rw [firstZero order orderBound word, secondZero order orderBound word, add_zero]

theorem zeroJets_smul {dimension : ℕ} (scalar : ℂ) {field : ClosedJet dimension}
    (fieldZero : ZeroCartesianFirstJets field) :
    ZeroCartesianFirstJets (scalar • field) := by
  intro order orderBound word
  have expand := congrFun (congrArg ContinuousMap.toFun
    ((closedDerivativeLinear order word).map_smul scalar field))
    ⟨0, by simp [closedUnitDisk]⟩
  change closedDerivative (scalar • field) order word ⟨0, by simp [closedUnitDisk]⟩ = 0
  rw [show closedDerivative (scalar • field) order word ⟨0, by simp [closedUnitDisk]⟩ =
    scalar • closedDerivative field order word ⟨0, by simp [closedUnitDisk]⟩ from expand]
  rw [fieldZero order orderBound word, smul_zero]

theorem zeroJets_neg {dimension : ℕ} {field : ClosedJet dimension}
    (fieldZero : ZeroCartesianFirstJets field) :
    ZeroCartesianFirstJets (-field) := by
  have := zeroJets_smul (-1 : ℂ) fieldZero
  rwa [neg_one_smul] at this

theorem zeroJets_sub {dimension : ℕ} {first second : ClosedJet dimension}
    (firstZero : ZeroCartesianFirstJets first) (secondZero : ZeroCartesianFirstJets second) :
    ZeroCartesianFirstJets (first - second) := by
  rw [sub_eq_add_neg]
  exact zeroJets_add firstZero (zeroJets_neg secondZero)

theorem valueMapCore_zero_first_jets {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore phase sourceDimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((valueMapCore mapping phase field).1 cell) := by
  intro cell order orderBound word
  exact valueMapJet_preserves_zero_derivatives mapping (field.1 cell)
    (fun innerWord => zeroJets cell order orderBound innerWord) word

theorem tangentialCore_zero_first_jets (field : ACore phase 2)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((tangentialCore phase field).1 cell) := by
  intro cell order orderBound word
  exact tangentialJet_preserves_zero_derivatives (field.1 cell)
    (fun innerWord => zeroJets cell order orderBound innerWord) word

theorem angularCore_zero_first_jets (mode : ℤ) {dimension : ℕ}
    (field : ACore phase dimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((angularCore phase mode field).1 cell) := by
  intro cell order orderBound word
  exact angularClosedJet_preserves_zero_derivatives mode (field.1 cell)
    (fun innerWord => zeroJets cell order orderBound innerWord) word

theorem seedTransposeCore_zero_first_jets (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((seedTransposeCore phase parameter inside field).1 cell) :=
  smoothMultiplier_preserves_zero_first_jets phase _
    (seedTransposeCells_envelope_summable phase parameter inside) field zeroJets

theorem seedMatrixCore_zero_first_jets (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((seedMatrixCore phase parameter inside field).1 cell) := by
  intro cell
  rw [seedMatrixCore_eq_full phase parameter inside field]
  exact smoothMultiplier_preserves_zero_first_jets phase _
    (seedMatrixCells_envelope_summable phase parameter inside) field zeroJets cell

theorem derivativeDotCore_zero_first_jets (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((derivativeDotCore phase parameter inside field).1 cell) := by
  intro cell
  change ZeroCartesianFirstJets ((coordinateCore phase 0 (smoothMultiplier phase _ _ field)).1 cell +
    (coordinateCore phase 1 (smoothMultiplier phase _ _ field)).1 cell)
  exact zeroJets_add
    (coordinateCore_zero_first_jets phase 0 _ (smoothMultiplier_preserves_zero_first_jets phase _
      (derivativeRowCoefficients_envelope_summable phase parameter inside 0) field zeroJets) cell)
    (coordinateCore_zero_first_jets phase 1 _ (smoothMultiplier_preserves_zero_first_jets phase _
      (derivativeRowCoefficients_envelope_summable phase parameter inside 1) field zeroJets) cell)

/-- Both gauge corrections preserve zero first Cartesian jets. -/
theorem poloidalCorrection_zero_first_jets (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets
      ((poloidalCorrection phase parameter inside field).1 cell) := by
  rw [poloidalCorrection_apply]
  exact valueMapCore_zero_first_jets phase planarInclusionMap _
    (seedMatrixCore_zero_first_jets phase parameter inside _
      (tangentialCore_zero_first_jets phase _
        (seedTransposeCore_zero_first_jets phase parameter inside _
          (valueMapCore_zero_first_jets phase planarPartMap field zeroJets))))

theorem toroidalCorrection_zero_first_jets (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets
      ((toroidalCorrection phase parameter inside field).1 cell) := by
  rw [toroidalCorrection_apply]
  apply valueMapCore_zero_first_jets phase toroidalInclusionMap
  apply angularCore_zero_first_jets phase 0
  intro cell
  change ZeroCartesianFirstJets ((toroidalPartCore phase field).1 cell +
    ((phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
      (planarPartCore phase field)).1 cell)
  apply zeroJets_add
  · exact valueMapCore_zero_first_jets phase toroidalPartMap field zeroJets cell
  · change ZeroCartesianFirstJets ((phase.length⁻¹ : ℂ) •
      (derivativeDotCore phase parameter inside (planarPartCore phase field)).1 cell)
    exact zeroJets_smul _ (derivativeDotCore_zero_first_jets phase parameter inside _
      (valueMapCore_zero_first_jets phase planarPartMap field zeroJets) cell)

/-- The full triangular projection preserves zero first Cartesian jets. -/
theorem triangularGaugeProjection_zero_first_jets (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets
      ((triangularGaugeProjection phase parameter inside field).1 cell) := by
  have firstStage : ∀ cell, ZeroCartesianFirstJets
      ((field - poloidalCorrection phase parameter inside field).1 cell) := by
    intro cell
    change ZeroCartesianFirstJets (field.1 cell -
      (poloidalCorrection phase parameter inside field).1 cell)
    exact zeroJets_sub (zeroJets cell)
      (poloidalCorrection_zero_first_jets phase parameter inside field zeroJets cell)
  intro cell
  change ZeroCartesianFirstJets
    (((field - poloidalCorrection phase parameter inside field) -
      toroidalCorrection phase parameter inside
        (field - poloidalCorrection phase parameter inside field)).1 cell)
  change ZeroCartesianFirstJets
    ((field - poloidalCorrection phase parameter inside field).1 cell -
      (toroidalCorrection phase parameter inside
        (field - poloidalCorrection phase parameter inside field)).1 cell)
  exact zeroJets_sub (firstStage cell)
    (toroidalCorrection_zero_first_jets phase parameter inside _ firstStage cell)

/-- The literal outer radial component against the polar radial direction,
with the paper's real pairing and no conjugation. -/
def radialComponentAt (angle : ℝ) (value : ComplexEuclidean 2) : ℂ :=
  (Real.cos angle : ℂ) * value 0 + (Real.sin angle : ℂ) * value 1

theorem radialComponentAt_sub (angle : ℝ) (first second : ComplexEuclidean 2) :
    radialComponentAt angle (first - second) =
      radialComponentAt angle first - radialComponentAt angle second := by
  unfold radialComponentAt
  simp only [PiLp.sub_apply]
  ring

/-- The tangential projection output has literally zero radial component at
every polar point: the exact first half of N15. -/
theorem tangentialCore_radial_component_zero (field : ACore phase 2) (cell : ℤ)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    radialComponentAt angle (((tangentialCore phase field).1 cell).value
      (polarClosedPoint radius bounded angle)) = 0 := by
  rw [tangentialCore_apply, tangentialJet_polar_axis_value]
  unfold radialComponentAt
  set scalar := (equivariantAverageJet (field.1 cell)).value (axisClosedPoint radius bounded) 1
  have firstCoordinate : (scalar • polarTangentialVector angle) 0 =
      scalar * (-(Real.sin angle : ℂ)) := by
    rw [PiLp.smul_apply, smul_eq_mul]
    rfl
  have secondCoordinate : (scalar • polarTangentialVector angle) 1 =
      scalar * (Real.cos angle : ℂ) := by
    rw [PiLp.smul_apply, smul_eq_mul]
    rfl
  rw [firstCoordinate, secondCoordinate]
  ring

/-- The planar part of the triangular projection differs from the identity
exactly by the poloidal correction. -/
theorem triangularGaugeProjection_planar_part (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    planarPartCore phase (triangularGaugeProjection phase parameter inside field) =
      planarPartCore phase field -
        seedMatrixCore phase parameter inside (tangentialCore phase
          (seedTransposeCore phase parameter inside (planarPartCore phase field))) := by
  change planarPartCore phase
    ((field - poloidalCorrection phase parameter inside field) -
      toroidalCorrection phase parameter inside
        (field - poloidalCorrection phase parameter inside field)) = _
  rw [map_sub, map_sub, toroidalCorrection_planar_part, sub_zero,
    poloidalCorrection_apply, planarPartCore_planarInclusionCore]

/-- The exact N15 radial-row neutrality: after the seed inverse, the outer
radial component of the projected field equals that of the original field at
every closed polar point and every cell.  This is an exact identity, not an
angular support estimate. -/
theorem triangularGaugeProjection_radial_row (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) (cell : ℤ) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    radialComponentAt angle (((seedInverseCore phase parameter inside
        (planarPartCore phase (triangularGaugeProjection phase parameter inside field))).1
          cell).value (polarClosedPoint radius bounded angle)) =
      radialComponentAt angle (((seedInverseCore phase parameter inside
        (planarPartCore phase field)).1 cell).value
          (polarClosedPoint radius bounded angle)) := by
  rw [triangularGaugeProjection_planar_part, map_sub,
    seedInverse_seedMatrix_core phase parameter inside]
  have valueSplit : ((seedInverseCore phase parameter inside
        (planarPartCore phase field) - tangentialCore phase
          (seedTransposeCore phase parameter inside (planarPartCore phase field))).1
            cell).value (polarClosedPoint radius bounded angle) =
      ((seedInverseCore phase parameter inside (planarPartCore phase field)).1 cell).value
          (polarClosedPoint radius bounded angle) -
        ((tangentialCore phase (seedTransposeCore phase parameter inside
          (planarPartCore phase field))).1 cell).value
            (polarClosedPoint radius bounded angle) := by
    change ((seedInverseCore phase parameter inside (planarPartCore phase field)).1 cell -
      (tangentialCore phase (seedTransposeCore phase parameter inside
        (planarPartCore phase field))).1 cell).value (polarClosedPoint radius bounded angle) = _
    rw [sub_eq_add_neg, closedJet_value_add, ContinuousMap.add_apply, closedJet_value_neg,
      ContinuousMap.neg_apply, ← sub_eq_add_neg]
  rw [valueSplit, radialComponentAt_sub,
    tangentialCore_radial_component_zero, sub_zero]

end Grad.Constraints.Gauges
