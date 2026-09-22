import GaugeSandwichComposition

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

/-- The full literal seed matrix coefficient family `M = I + (M - I)`. -/
def seedMatrixCells (parameter : Seed.Parameters) (cell : ℤ) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
    Seed.actualCells 0 parameter cell

/-- The transposed full seed matrix coefficient family `Mᵀ`. -/
def seedTransposeCells (parameter : Seed.Parameters) (cell : ℤ) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
    transposeOperator (Seed.actualCells 0 parameter cell)

/-- The full literal seed inverse coefficient family `M⁻¹ = I + (M⁻¹ - I)`. -/
def seedInverseCells (parameter : Seed.Parameters) (cell : ℤ) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
    Seed.actualCells 1 parameter cell

theorem deltaIdentity_envelope_summable (phase : PhaseParameters) (grade : ℕ) :
    Summable (envelopeTerm phase grade (fun cell =>
      if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro cell outside
  have nonzero : cell ≠ 0 := by simpa using outside
  unfold envelopeTerm
  simp only [if_neg nonzero, norm_zero, mul_zero]

theorem envelopeTerm_add_le (phase : PhaseParameters) (grade : ℕ)
    (first second : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) (cell : ℤ) :
    envelopeTerm phase grade (fun index => first index + second index) cell ≤
      envelopeTerm phase grade first cell + envelopeTerm phase grade second cell := by
  unfold envelopeTerm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
    (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le cell)).le _))

theorem envelope_add_summable (phase : PhaseParameters) (grade : ℕ)
    (first second : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (firstSummable : Summable (envelopeTerm phase grade first))
    (secondSummable : Summable (envelopeTerm phase grade second)) :
    Summable (envelopeTerm phase grade (fun index => first index + second index)) :=
  Summable.of_nonneg_of_le (fun cell => envelopeTerm_nonnegative phase grade _ cell)
    (envelopeTerm_add_le phase grade first second) (firstSummable.add secondSummable)

theorem transpose_envelope_summable (phase : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (summable : Summable (envelopeTerm phase grade coefficients)) :
    Summable (envelopeTerm phase grade (fun cell => transposeOperator (coefficients cell))) := by
  apply Summable.of_nonneg_of_le (fun cell => envelopeTerm_nonnegative phase grade _ cell)
    (fun cell => ?_) (summable.mul_left 4)
  unfold envelopeTerm
  calc Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
      ‖transposeOperator (coefficients cell)‖
      ≤ Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
        (4 * ‖coefficients cell‖) :=
        mul_le_mul_of_nonneg_left (transposeOperator_norm_le _)
          (mul_nonneg (Real.exp_pos _).le
            (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le cell)).le _))
    _ = 4 * (Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
        ‖coefficients cell‖) := by ring

theorem seedMatrixCells_envelope_summable (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) :
    Summable (envelopeTerm phase grade (seedMatrixCells parameter)) :=
  envelope_add_summable phase grade _ _ (deltaIdentity_envelope_summable phase grade)
    (seedCells_all_summable phase parameter inside 0 grade)

theorem seedTransposeCells_envelope_summable (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) :
    Summable (envelopeTerm phase grade (seedTransposeCells parameter)) :=
  envelope_add_summable phase grade _ _ (deltaIdentity_envelope_summable phase grade)
    (transpose_envelope_summable phase grade _
      (seedCells_all_summable phase parameter inside 0 grade))

theorem seedInverseCells_envelope_summable (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) :
    Summable (envelopeTerm phase grade (seedInverseCells parameter)) :=
  envelope_add_summable phase grade _ _ (deltaIdentity_envelope_summable phase grade)
    (seedCells_all_summable phase parameter inside 1 grade)

theorem smoothMultiplier_add_coefficients (phase : PhaseParameters)
    (first second : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (firstSummable : ∀ grade, Summable (envelopeTerm phase grade first))
    (secondSummable : ∀ grade, Summable (envelopeTerm phase grade second))
    (field : ACore phase 2) :
    smoothMultiplier phase (fun index => first index + second index)
        (fun grade => envelope_add_summable phase grade first second
          (firstSummable grade) (secondSummable grade)) field =
      smoothMultiplier phase first firstSummable field +
        smoothMultiplier phase second secondSummable field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have combined := smoothMultiplier_value_hasSum phase _
    (fun grade => envelope_add_summable phase grade first second
      (firstSummable grade) (secondSummable grade)) field cell point
  have split : HasSum (fun shift : ℤ => (first shift + second shift)
      ((field.1 (cell - shift)).value point))
      (((smoothMultiplier phase first firstSummable field).1 cell).value point +
        ((smoothMultiplier phase second secondSummable field).1 cell).value point) := by
    exact (smoothMultiplier_value_hasSum phase first firstSummable field cell point).add
      (smoothMultiplier_value_hasSum phase second secondSummable field cell point)
  have equality := combined.unique split
  simpa using equality

theorem smoothMultiplier_delta_identity (phase : PhaseParameters) (field : ACore phase 2) :
    smoothMultiplier phase (fun cell =>
        if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)
      (fun grade => deltaIdentity_envelope_summable phase grade) field = field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have combined := smoothMultiplier_value_hasSum phase _
    (fun grade => deltaIdentity_envelope_summable phase grade) field cell point
  have pointTerm (shift : ℤ) : (if shift = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2)
      else 0) ((field.1 (cell - shift)).value point) =
      if shift = 0 then ((field.1 cell).value point) else 0 := by
    by_cases zeroShift : shift = 0
    · rw [if_pos zeroShift, if_pos zeroShift, zeroShift, sub_zero,
        ContinuousLinearMap.id_apply]
    · rw [if_neg zeroShift, if_neg zeroShift]
      rfl
  have deltaSum : HasSum (fun shift : ℤ => (if shift = 0 then
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)
        ((field.1 (cell - shift)).value point)) ((field.1 cell).value point) := by
    have base : HasSum (fun shift : ℤ => if shift = 0 then
        ((field.1 cell).value point) else 0) ((field.1 cell).value point) :=
      hasSum_ite_eq 0 _
    exact base.congr_fun pointTerm
  exact combined.unique deltaSum

/-- The accepted seed matrix core is literally the smooth multiplier of the
full matrix coefficient family. -/
theorem seedMatrixCore_eq_full (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    seedMatrixCore phase parameter inside field =
      smoothMultiplier phase (seedMatrixCells parameter)
        (seedMatrixCells_envelope_summable phase parameter inside) field := by
  refine Eq.symm ?_
  calc smoothMultiplier phase (seedMatrixCells parameter)
        (seedMatrixCells_envelope_summable phase parameter inside) field
      = smoothMultiplier phase (fun index =>
            (if index = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
              Seed.actualCells 0 parameter index)
          (fun grade => envelope_add_summable phase grade _ _
            (deltaIdentity_envelope_summable phase grade)
            (seedCells_all_summable phase parameter inside 0 grade)) field := rfl
    _ = smoothMultiplier phase (fun cell =>
            if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)
          (fun grade => deltaIdentity_envelope_summable phase grade) field +
        smoothMultiplier phase (Seed.actualCells 0 parameter)
          (fun grade => seedCells_all_summable phase parameter inside 0 grade) field :=
      smoothMultiplier_add_coefficients phase _ _ _ _ field
    _ = field + smoothMultiplier phase (Seed.actualCells 0 parameter)
          (fun grade => seedCells_all_summable phase parameter inside 0 grade) field := by
        rw [smoothMultiplier_delta_identity phase field]
    _ = seedMatrixCore phase parameter inside field := rfl

/-- The accepted seed inverse core is literally the smooth multiplier of the
full inverse coefficient family. -/
theorem seedInverseCore_eq_full (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    seedInverseCore phase parameter inside field =
      smoothMultiplier phase (seedInverseCells parameter)
        (seedInverseCells_envelope_summable phase parameter inside) field := by
  refine Eq.symm ?_
  calc smoothMultiplier phase (seedInverseCells parameter)
        (seedInverseCells_envelope_summable phase parameter inside) field
      = smoothMultiplier phase (fun index =>
            (if index = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
              Seed.actualCells 1 parameter index)
          (fun grade => envelope_add_summable phase grade _ _
            (deltaIdentity_envelope_summable phase grade)
            (seedCells_all_summable phase parameter inside 1 grade)) field := rfl
    _ = smoothMultiplier phase (fun cell =>
            if cell = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)
          (fun grade => deltaIdentity_envelope_summable phase grade) field +
        smoothMultiplier phase (Seed.actualCells 1 parameter)
          (fun grade => seedCells_all_summable phase parameter inside 1 grade) field :=
      smoothMultiplier_add_coefficients phase _ _ _ _ field
    _ = field + smoothMultiplier phase (Seed.actualCells 1 parameter)
          (fun grade => seedCells_all_summable phase parameter inside 1 grade) field := by
        rw [smoothMultiplier_delta_identity phase field]
    _ = seedInverseCore phase parameter inside field := rfl

/-- The actual smooth-core multiplication by the literal transposed seed `Mᵀ`. -/
def seedTransposeCore (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  smoothMultiplier phase (seedTransposeCells parameter)
    (seedTransposeCells_envelope_summable phase parameter inside)

end Grad.Constraints.Gauges
