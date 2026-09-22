import AXB1CutoffBounds
import RootUnitTower

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.PhysicalCoordinates
open Grad.Constraints.Multipliers

variable {parameters : PhaseParameters}

/-- The literal first root derivative has the AL27 one-high form after the
exact Q12 bridge: one high direction, or one low direction paired with the
high base. -/
theorem rootDerivativeFamily_one_tangent_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base direction : TangentCoefficient parameters), RootAxisCondition base →
        coefficientEnvelope grade (rootDerivativeFamily 1 base (fun _ => direction)) ≤
          constant * (tangentNorm (grade + 1) direction +
            (1 + tangentNorm (grade + 1) base) * tangentNorm 1 direction) := by
  obtain ⟨rootConstant, rootNonnegative, rootBound⟩ :=
    rootDerivativeFamily_bound (parameters := parameters) grade 1
  let highBridge := Real.sqrt 2 ^ grade * axisConstant
  let bridgeConstant := (1 + highBridge) * axisConstant + highBridge
  have highBridgeNonnegative : 0 ≤ highBridge := by
    dsimp [highBridge]
    exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axisConstant_pos.le
  have bridgeNonnegative : 0 ≤ bridgeConstant := by
    dsimp [bridgeConstant]
    exact add_nonneg (mul_nonneg (by linarith) axisConstant_pos.le) highBridgeNonnegative
  refine ⟨rootConstant * bridgeConstant,
    mul_nonneg rootNonnegative bridgeNonnegative, ?_⟩
  intro base direction axis
  have raw := rootBound base (fun _ : Fin 1 => direction) axis
  have eraseEmpty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  rw [Fin.prod_univ_one, Fin.sum_univ_one, eraseEmpty, Finset.prod_empty, mul_one] at raw
  have baseBridge := tangentPlanarEnvelope_le grade base
  have directionHigh := tangentPlanarEnvelope_le grade direction
  have directionLow := tangentPlanarEnvelope_le 0 direction
  rw [pow_zero, one_mul] at directionLow
  have baseBridge' : tangentPlanarEnvelope grade base ≤
      highBridge * tangentNorm (grade + 1) base := by
    simpa only [highBridge, mul_assoc] using baseBridge
  have directionHigh' : tangentPlanarEnvelope grade direction ≤
      highBridge * tangentNorm (grade + 1) direction := by
    simpa only [highBridge, mul_assoc] using directionHigh
  have oneBase : 1 + tangentPlanarEnvelope grade base ≤
      (1 + highBridge) * (1 + tangentNorm (grade + 1) base) := by
    have baseNonnegative := tangentNorm_nonneg (grade + 1) base
    nlinarith [baseBridge']
  have lowNonnegative := tangentPlanarEnvelope_nonneg 0 direction
  have productBound :
      (1 + tangentPlanarEnvelope grade base) * tangentPlanarEnvelope 0 direction ≤
        ((1 + highBridge) * axisConstant) *
          ((1 + tangentNorm (grade + 1) base) * tangentNorm 1 direction) := by
    calc
      (1 + tangentPlanarEnvelope grade base) * tangentPlanarEnvelope 0 direction
          ≤ ((1 + highBridge) * (1 + tangentNorm (grade + 1) base)) *
              (axisConstant * tangentNorm 1 direction) :=
        mul_le_mul oneBase directionLow lowNonnegative
          (mul_nonneg (by positivity) (by linarith [tangentNorm_nonneg (grade + 1) base]))
      _ = ((1 + highBridge) * axisConstant) *
          ((1 + tangentNorm (grade + 1) base) * tangentNorm 1 direction) := by ring
  have bracketBound :
      (1 + tangentPlanarEnvelope grade base) * tangentPlanarEnvelope 0 direction +
          tangentPlanarEnvelope grade direction ≤
        bridgeConstant * (tangentNorm (grade + 1) direction +
          (1 + tangentNorm (grade + 1) base) * tangentNorm 1 direction) := by
    have highNormNonnegative := tangentNorm_nonneg (grade + 1) direction
    have lowNormNonnegative := tangentNorm_nonneg 1 direction
    have baseNormNonnegative := tangentNorm_nonneg (grade + 1) base
    have mainSum := add_le_add productBound directionHigh'
    have highExtra : 0 ≤ ((1 + highBridge) * axisConstant) *
        tangentNorm (grade + 1) direction :=
      mul_nonneg (mul_nonneg (by linarith) axisConstant_pos.le) highNormNonnegative
    have lowExtra : 0 ≤ highBridge *
        ((1 + tangentNorm (grade + 1) base) * tangentNorm 1 direction) :=
      mul_nonneg highBridgeNonnegative (mul_nonneg (by linarith) lowNormNonnegative)
    dsimp [bridgeConstant]
    nlinarith
  exact (raw.trans (mul_le_mul_of_nonneg_left bracketBound rootNonnegative)).trans_eq (by ring)

/-- Same-grade norm estimate for the exact cap chart remainder.  All cutoff
norms are fixed constants and the seed dependence is uniform on the supplied
compact admissible patch. -/
theorem capChartRemainder_bound_on_patch (radius : ℝ) (positive : 0 < radius)
    (grade : ℕ) (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
        (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters),
        originalGradeNorm grade
            (capChartRemainder parameters radius positive seed inside coefficient tangent) ≤
          constant * (coefficientEnvelope grade coefficient + tangentPlanarEnvelope grade tangent) := by
  obtain ⟨seedConstant, seedNonnegative, seedBound⟩ :=
    capSeedField_difference_bound_on_patch (parameters := parameters) radius positive grade
      seedPatch compact insidePatch
  let scalarDifference (coordinate : Fin 2) : ACore parameters 1 :=
    capScalarCoordinate parameters radius positive coordinate -
      tameCoordinateScalarField parameters coordinate
  let multiplier := multiplierConstant grade parameters.gamma
  let coefficientConstant := multiplier * seedConstant
  let tangentConstant := ‖tameTangentInclusion‖ * multiplier *
    (originalGradeNorm grade (scalarDifference 0) + originalGradeNorm grade (scalarDifference 1))
  have multiplierNonnegative : 0 ≤ multiplier := by
    dsimp [multiplier]
    exact multiplierConstant_nonnegative grade parameters.gamma parameters.gamma_pos.le
  have coefficientNonnegative : 0 ≤ coefficientConstant :=
    mul_nonneg multiplierNonnegative seedNonnegative
  have tangentNonnegative : 0 ≤ tangentConstant := by
    dsimp [tangentConstant]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) multiplierNonnegative)
      (add_nonneg (originalGradeNorm_nonnegative grade (scalarDifference 0))
        (originalGradeNorm_nonnegative grade (scalarDifference 1)))
  refine ⟨coefficientConstant + tangentConstant,
    add_nonneg coefficientNonnegative tangentNonnegative, ?_⟩
  intro seed member inside coefficient tangent
  rw [capChartRemainder_expansion radius positive seed inside coefficient tangent]
  have seedFieldBound := seedBound seed member inside
  have coefficientRaw := tameScalarMultiplier_bound 3 coefficient
    (capSeedField parameters radius positive seed inside - tameSeedField parameters seed inside) grade
  have coefficientBound : originalGradeNorm grade
      (tameScalarMultiplier 3 coefficient
        (capSeedField parameters radius positive seed inside - tameSeedField parameters seed inside)) ≤
      coefficientConstant * coefficientEnvelope grade coefficient := by
    exact (coefficientRaw.trans
      (mul_le_mul_of_nonneg_left seedFieldBound
        (mul_nonneg multiplierNonnegative (coefficientEnvelope_nonneg grade coefficient)))).trans_eq (by
          dsimp [coefficientConstant, multiplier]
          ring)
  have scalar0 := tameScalarMultiplier_bound 1 (tangentComponent tangent 0) (scalarDifference 0) grade
  have scalar1 := tameScalarMultiplier_bound 1 (tangentComponent tangent 1) (scalarDifference 1) grade
  have env0 := tangentComponent_envelope_le grade tangent 0
  have env1 := tangentComponent_envelope_le grade tangent 1
  have innerTriangle := originalGradeNorm_add_le grade
    (tameScalarMultiplier 1 (tangentComponent tangent 0) (scalarDifference 0))
    (tameScalarMultiplier 1 (tangentComponent tangent 1) (scalarDifference 1))
  have innerBound : originalGradeNorm grade
      (tameScalarMultiplier 1 (tangentComponent tangent 0) (scalarDifference 0) +
        tameScalarMultiplier 1 (tangentComponent tangent 1) (scalarDifference 1)) ≤
      multiplier * (originalGradeNorm grade (scalarDifference 0) +
        originalGradeNorm grade (scalarDifference 1)) * tangentPlanarEnvelope grade tangent := by
    have d0 := originalGradeNorm_nonnegative grade (scalarDifference 0)
    have d1 := originalGradeNorm_nonnegative grade (scalarDifference 1)
    have firstBound : originalGradeNorm grade
        (tameScalarMultiplier 1 (tangentComponent tangent 0) (scalarDifference 0)) ≤
        multiplier * originalGradeNorm grade (scalarDifference 0) *
          tangentPlanarEnvelope grade tangent := by
      calc
        _ ≤ multiplierConstant grade parameters.gamma *
              coefficientEnvelope grade (tangentComponent tangent 0) *
              originalGradeNorm grade (scalarDifference 0) := scalar0
        _ ≤ multiplierConstant grade parameters.gamma *
              tangentPlanarEnvelope grade tangent *
              originalGradeNorm grade (scalarDifference 0) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left env0 multiplierNonnegative) d0
        _ = _ := by dsimp [multiplier]; ring
    have secondBound : originalGradeNorm grade
        (tameScalarMultiplier 1 (tangentComponent tangent 1) (scalarDifference 1)) ≤
        multiplier * originalGradeNorm grade (scalarDifference 1) *
          tangentPlanarEnvelope grade tangent := by
      calc
        _ ≤ multiplierConstant grade parameters.gamma *
              coefficientEnvelope grade (tangentComponent tangent 1) *
              originalGradeNorm grade (scalarDifference 1) := scalar1
        _ ≤ multiplierConstant grade parameters.gamma *
              tangentPlanarEnvelope grade tangent *
              originalGradeNorm grade (scalarDifference 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left env1 multiplierNonnegative) d1
        _ = _ := by dsimp [multiplier]; ring
    exact innerTriangle.trans ((add_le_add firstBound secondBound).trans_eq (by ring))
  have outerRaw := valueMapCore_bound tameTangentInclusion
    (tameScalarMultiplier 1 (tangentComponent tangent 0) (scalarDifference 0) +
      tameScalarMultiplier 1 (tangentComponent tangent 1) (scalarDifference 1)) grade
  have tangentBound : originalGradeNorm grade
      (valueMapCore parameters tameTangentInclusion
        (tameScalarMultiplier 1 (tangentComponent tangent 0) (scalarDifference 0) +
          tameScalarMultiplier 1 (tangentComponent tangent 1) (scalarDifference 1))) ≤
      tangentConstant * tangentPlanarEnvelope grade tangent := by
    exact (outerRaw.trans
      (mul_le_mul_of_nonneg_left innerBound (norm_nonneg _))).trans_eq (by
        dsimp [tangentConstant, multiplier]
        ring)
  have totalTriangle := originalGradeNorm_add_le grade
    (tameScalarMultiplier 3 coefficient
      (capSeedField parameters radius positive seed inside - tameSeedField parameters seed inside))
    (valueMapCore parameters tameTangentInclusion
      (tameScalarMultiplier 1 (tangentComponent tangent 0) (scalarDifference 0) +
        tameScalarMultiplier 1 (tangentComponent tangent 1) (scalarDifference 1)))
  have coefficientEnvelopeNonnegative := coefficientEnvelope_nonneg grade coefficient
  have tangentEnvelopeNonnegative := tangentPlanarEnvelope_nonneg grade tangent
  nlinarith

/-- The scalar cap component is linear in the first axis datum, with a
same-grade bound by its planar coefficient envelope. -/
theorem capScalarAffine_bound (radius : ℝ) (positive : 0 < radius) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ sigma : TangentCoefficient parameters,
        originalGradeNorm grade (capScalarAffine parameters radius positive sigma) ≤
          constant * tangentPlanarEnvelope grade sigma := by
  let multiplier := multiplierConstant grade parameters.gamma
  let constant := multiplier *
    (originalGradeNorm grade (capScalarCoordinate parameters radius positive 0) +
      originalGradeNorm grade (capScalarCoordinate parameters radius positive 1))
  have multiplierNonnegative : 0 ≤ multiplier := by
    dsimp [multiplier]
    exact multiplierConstant_nonnegative grade parameters.gamma parameters.gamma_pos.le
  have constantNonnegative : 0 ≤ constant := by
    dsimp [constant]
    exact mul_nonneg multiplierNonnegative
      (add_nonneg
        (originalGradeNorm_nonnegative grade (capScalarCoordinate parameters radius positive 0))
        (originalGradeNorm_nonnegative grade (capScalarCoordinate parameters radius positive 1)))
  refine ⟨constant, constantNonnegative, ?_⟩
  intro sigma
  rw [capScalarAffine]
  have first := tameScalarMultiplier_bound 1 (tangentComponent sigma 0)
    (capScalarCoordinate parameters radius positive 0) grade
  have second := tameScalarMultiplier_bound 1 (tangentComponent sigma 1)
    (capScalarCoordinate parameters radius positive 1) grade
  have env0 := tangentComponent_envelope_le grade sigma 0
  have env1 := tangentComponent_envelope_le grade sigma 1
  have triangle := originalGradeNorm_add_le grade
    (tameScalarMultiplier 1 (tangentComponent sigma 0)
      (capScalarCoordinate parameters radius positive 0))
    (tameScalarMultiplier 1 (tangentComponent sigma 1)
      (capScalarCoordinate parameters radius positive 1))
  have norm0 := originalGradeNorm_nonnegative grade
    (capScalarCoordinate parameters radius positive 0)
  have norm1 := originalGradeNorm_nonnegative grade
    (capScalarCoordinate parameters radius positive 1)
  have firstBound : originalGradeNorm grade
      (tameScalarMultiplier 1 (tangentComponent sigma 0)
        (capScalarCoordinate parameters radius positive 0)) ≤
      multiplier * originalGradeNorm grade (capScalarCoordinate parameters radius positive 0) *
        tangentPlanarEnvelope grade sigma := by
    calc
      _ ≤ multiplierConstant grade parameters.gamma *
            coefficientEnvelope grade (tangentComponent sigma 0) *
            originalGradeNorm grade (capScalarCoordinate parameters radius positive 0) := first
      _ ≤ multiplierConstant grade parameters.gamma * tangentPlanarEnvelope grade sigma *
            originalGradeNorm grade (capScalarCoordinate parameters radius positive 0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left env0 multiplierNonnegative) norm0
      _ = _ := by dsimp [multiplier]; ring
  have secondBound : originalGradeNorm grade
      (tameScalarMultiplier 1 (tangentComponent sigma 1)
        (capScalarCoordinate parameters radius positive 1)) ≤
      multiplier * originalGradeNorm grade (capScalarCoordinate parameters radius positive 1) *
        tangentPlanarEnvelope grade sigma := by
    calc
      _ ≤ multiplierConstant grade parameters.gamma *
            coefficientEnvelope grade (tangentComponent sigma 1) *
            originalGradeNorm grade (capScalarCoordinate parameters radius positive 1) := second
      _ ≤ multiplierConstant grade parameters.gamma * tangentPlanarEnvelope grade sigma *
            originalGradeNorm grade (capScalarCoordinate parameters radius positive 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left env1 multiplierNonnegative) norm1
      _ = _ := by dsimp [multiplier]; ring
  exact triangle.trans ((add_le_add firstBound secondBound).trans_eq (by
    dsimp [constant]
    ring))

end Grad.ChartAxisLift
