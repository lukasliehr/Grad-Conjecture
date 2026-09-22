import QuotientTermConstructors

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial

variable {parameters : PhaseParameters}

@[simp] theorem linearEvaluation_apply {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (point : M) (mapping : M →ₗ[ℂ] N) :
    linearEvaluation point mapping = mapping point := rfl

/-- The literal `∂₊ = ∂₁ + i ∂₂` in the original coefficient core. -/
def partialPlusCore (parameters : PhaseParameters) {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  partialCore parameters 0 + Complex.I • partialCore parameters 1

/-- The literal `∂₋ = ∂₁ - i ∂₂` in the original coefficient core. -/
def partialMinusCore (parameters : PhaseParameters) {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  partialCore parameters 0 - Complex.I • partialCore parameters 1

/-- Multiplication by `z = y₁ + i y₂`. -/
def zMulCore (parameters : PhaseParameters) {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  coordinateCore parameters 0 + Complex.I • coordinateCore parameters 1

/-- Multiplication by `z̄ = y₁ - i y₂`. -/
def starZMulCore (parameters : PhaseParameters) {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  coordinateCore parameters 0 - Complex.I • coordinateCore parameters 1

/-- The literal `I - Π` at the zero angular mode. -/
def removeAngularCore (parameters : PhaseParameters) {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  LinearMap.id - angularCore parameters 0

theorem partialPlusCore_bound {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (partialPlusCore parameters field) ≤
      2 * partialGradeConstant grade * originalGradeNorm (grade + 1) field := by
  have expand : partialPlusCore parameters field =
      partialCore parameters 0 field + Complex.I • partialCore parameters 1 field := rfl
  rw [expand]
  apply (originalGradeNorm_add_le grade _ _).trans
  rw [originalGradeNorm_smul, Complex.norm_I, one_mul]
  have first := partialCore_bound parameters 0 field grade
  have second := partialCore_bound parameters 1 field grade
  linarith

theorem partialMinusCore_bound {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (partialMinusCore parameters field) ≤
      2 * partialGradeConstant grade * originalGradeNorm (grade + 1) field := by
  have expand : partialMinusCore parameters field =
      partialCore parameters 0 field - Complex.I • partialCore parameters 1 field := rfl
  rw [expand]
  apply (originalGradeNorm_sub_le grade _ _).trans
  rw [originalGradeNorm_smul, Complex.norm_I, one_mul]
  have first := partialCore_bound parameters 0 field grade
  have second := partialCore_bound parameters 1 field grade
  linarith

theorem zMulCore_bound {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (zMulCore parameters field) ≤
      2 * coordinateGradeConstant grade * originalGradeNorm grade field := by
  have expand : zMulCore parameters field =
      coordinateCore parameters 0 field + Complex.I • coordinateCore parameters 1 field := rfl
  rw [expand]
  apply (originalGradeNorm_add_le grade _ _).trans
  rw [originalGradeNorm_smul, Complex.norm_I, one_mul]
  have first := coordinateCore_bound parameters 0 field grade
  have second := coordinateCore_bound parameters 1 field grade
  linarith

theorem starZMulCore_bound {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (starZMulCore parameters field) ≤
      2 * coordinateGradeConstant grade * originalGradeNorm grade field := by
  have expand : starZMulCore parameters field =
      coordinateCore parameters 0 field - Complex.I • coordinateCore parameters 1 field := rfl
  rw [expand]
  apply (originalGradeNorm_sub_le grade _ _).trans
  rw [originalGradeNorm_smul, Complex.norm_I, one_mul]
  have first := coordinateCore_bound parameters 0 field grade
  have second := coordinateCore_bound parameters 1 field grade
  linarith

theorem angularCore_zero_bound {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (angularCore parameters 0 field) ≤
      orthogonalGradeConstant grade * originalGradeNorm grade field :=
  angularGradeCore_norm_le parameters 0 (GradeCore.ofCoreLinear field)

theorem removeAngularCore_bound {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (removeAngularCore parameters field) ≤
      (1 + orthogonalGradeConstant grade) * originalGradeNorm grade field := by
  have expand : removeAngularCore parameters field =
      field - angularCore parameters 0 field := rfl
  rw [expand]
  apply (originalGradeNorm_sub_le grade _ _).trans
  have angular := angularCore_zero_bound field grade
  linarith

theorem coe_smul_core {dimension : ℕ} (r : ℝ) (field : ACore parameters dimension) :
    ((r : ℂ)) • field = r • field := Complex.coe_smul r field

/-- The curried actual physical dot product. -/
def dotOperation (parameters : PhaseParameters) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 3 →ₗ[ℂ] ACore parameters 1 :=
  pairProductLinear parameters physicalDotProduct

/-- The curried actual column determinant product. -/
def determinantOperation (parameters : PhaseParameters) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 3 →ₗ[ℂ] ACore parameters 3 →ₗ[ℂ]
      ACore parameters 1 :=
  tripleProductLinear parameters determinantMultilinear

/-- The fixed linear tail `𝓘 Δ Π` of the radial correction. -/
def radialQuotientPost (parameters : PhaseParameters) :
    ACore parameters 1 →ₗ[ℂ] ACore parameters 1 :=
  ((radialCore parameters).comp (laplacianCore parameters)).comp (angularCore parameters 0)

/-- The curried literal radial correction `d(v₁, v₂) = 𝓘 Δ Π (D v₁ · R v₂)`. -/
def quotientDotCurried (parameters : PhaseParameters) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 3 →ₗ[ℂ] ACore parameters 1 :=
  (((dotOperation parameters).comp (eulerCore parameters)).compl₂
    (rotationCore parameters)).compr₂ (radialQuotientPost parameters)

theorem quotientDotCurried_apply (first second : ACore parameters 3) :
    quotientDotCurried parameters first second =
      bilinearRadialCore parameters physicalDotProduct first second := rfl

/-- The literal affine state derivative `V = v_ζ + ε A v + L e_T`. -/
def affineStateCore (parameters : PhaseParameters) (cellLength : ℝ)
    (state : QuotientState parameters) : ACore parameters 3 :=
  timeDerivativeCore parameters (stateField state) +
    stateScalar state • valueMapCore parameters tangentGeneratorMap (stateField state) +
      (cellLength : ℂ) • eTConstantCore parameters

/-- The literal constant `i z` in the scalar coefficient core. -/
def izConstantCore (parameters : PhaseParameters) : ACore parameters 1 :=
  zMulCore parameters (scalarConstantCore parameters Complex.I)

/-- The literal constant `-i z̄` in the scalar coefficient core. -/
def negIStarZConstantCore (parameters : PhaseParameters) : ACore parameters 1 :=
  starZMulCore parameters (scalarConstantCore parameters (-Complex.I))

/-- The literal O14 quotient rows `(g₊, g₋, g₃, h)`, assembled from the
actual constructed original-core operators. -/
def quotientPolynomialRows (parameters : PhaseParameters) (cellLength : ℝ)
    (state : QuotientState parameters) : QuotientRows parameters :=
  ![partialPlusCore parameters (statePotential state) -
      dotOperation parameters (partialPlusCore parameters (stateField state))
        (rotationCore parameters (stateField state)) +
      izConstantCore parameters +
      zMulCore parameters
        (quotientDotCurried parameters (stateField state) (stateField state)),
    partialMinusCore parameters (statePotential state) -
      dotOperation parameters (partialMinusCore parameters (stateField state))
        (rotationCore parameters (stateField state)) +
      negIStarZConstantCore parameters +
      starZMulCore parameters
        (quotientDotCurried parameters (stateField state) (stateField state)),
    removeAngularCore parameters (determinantOperation parameters
      (partialCore parameters 0 (stateField state))
      (partialCore parameters 1 (stateField state))
      (affineStateCore parameters cellLength state)),
    removeAngularCore parameters (dotOperation parameters
      (rotationCore parameters (stateField state))
      (affineStateCore parameters cellLength state) -
      timeDerivativeCore parameters (statePotential state))]

/-- Degree-zero homogeneous part: the two fixed constants. -/
def quotientDegreeZeroPart (parameters : PhaseParameters) :
    MultilinearMap ℂ (fun _ : Fin 0 => QuotientState parameters) (QuotientRows parameters) :=
  rowInsert 0 (stateConstantMultilinear (izConstantCore parameters)) +
    rowInsert 1 (stateConstantMultilinear (negIStarZConstantCore parameters))

/-- Degree-one homogeneous part. -/
def quotientDegreeOnePart (parameters : PhaseParameters) (cellLength : ℝ) :
    MultilinearMap ℂ (fun _ : Fin 1 => QuotientState parameters) (QuotientRows parameters) :=
  rowInsert 0 (stateLinearMultilinear ((partialPlusCore parameters).comp statePotential)) +
    rowInsert 1 (stateLinearMultilinear ((partialMinusCore parameters).comp statePotential)) +
      rowInsert 3 (stateLinearMultilinear
        ((removeAngularCore parameters).comp
            (((dotOperation parameters).flip
              ((cellLength : ℂ) • eTConstantCore parameters)).comp
              ((rotationCore parameters).comp stateField)) -
          (removeAngularCore parameters).comp
            ((timeDerivativeCore parameters).comp statePotential)))

/-- Degree-two homogeneous part. -/
def quotientDegreeTwoPart (parameters : PhaseParameters) (cellLength : ℝ) :
    MultilinearMap ℂ (fun _ : Fin 2 => QuotientState parameters) (QuotientRows parameters) :=
  rowInsert 0
    (-stateBilinearMultilinear (dotOperation parameters)
        ((partialPlusCore parameters).comp stateField)
        ((rotationCore parameters).comp stateField) +
      stateBilinearMultilinear
        ((quotientDotCurried parameters).compr₂ (zMulCore parameters))
        stateField stateField) +
    rowInsert 1
      (-stateBilinearMultilinear (dotOperation parameters)
          ((partialMinusCore parameters).comp stateField)
          ((rotationCore parameters).comp stateField) +
        stateBilinearMultilinear
          ((quotientDotCurried parameters).compr₂ (starZMulCore parameters))
          stateField stateField) +
      rowInsert 2 (stateBilinearMultilinear
          ((trilinearPost (determinantOperation parameters)
            (removeAngularCore parameters)).compr₂
              (linearEvaluation ((cellLength : ℂ) • eTConstantCore parameters)))
          ((partialCore parameters 0).comp stateField)
          ((partialCore parameters 1).comp stateField)) +
        rowInsert 3 (stateBilinearMultilinear
          ((dotOperation parameters).compr₂ (removeAngularCore parameters))
          ((rotationCore parameters).comp stateField)
          ((timeDerivativeCore parameters).comp stateField))

/-- Degree-three homogeneous part. -/
def quotientDegreeThreePart (parameters : PhaseParameters) :
    MultilinearMap ℂ (fun _ : Fin 3 => QuotientState parameters) (QuotientRows parameters) :=
  rowInsert 2 (stateTrilinearMultilinear
      (trilinearPost (determinantOperation parameters) (removeAngularCore parameters))
      ((partialCore parameters 0).comp stateField)
      ((partialCore parameters 1).comp stateField)
      ((timeDerivativeCore parameters).comp stateField)) +
    rowInsert 3 (stateScalarWrap (stateBilinearMultilinear
      ((dotOperation parameters).compr₂ (removeAngularCore parameters))
      ((rotationCore parameters).comp stateField)
      ((valueMapCore parameters tangentGeneratorMap).comp stateField)))

/-- Degree-four homogeneous part. -/
def quotientDegreeFourPart (parameters : PhaseParameters) :
    MultilinearMap ℂ (fun _ : Fin 4 => QuotientState parameters) (QuotientRows parameters) :=
  rowInsert 2 (stateScalarWrap (stateTrilinearMultilinear
    (trilinearPost (determinantOperation parameters) (removeAngularCore parameters))
    ((partialCore parameters 0).comp stateField)
    ((partialCore parameters 1).comp stateField)
    ((valueMapCore parameters tangentGeneratorMap).comp stateField)))

/-- The full iterated directional derivative family of the literal O14
polynomial: the exact sum of the five homogeneous diagonal derivatives. -/
def quotientRowsDerivative (parameters : PhaseParameters) (cellLength : ℝ) (order : ℕ)
    (base : QuotientState parameters) (directions : Fin order → QuotientState parameters) :
    QuotientRows parameters :=
  diagonalDerivative (quotientDegreeZeroPart parameters) order base directions +
    diagonalDerivative (quotientDegreeOnePart parameters cellLength) order base directions +
      diagonalDerivative (quotientDegreeTwoPart parameters cellLength) order base directions +
        diagonalDerivative (quotientDegreeThreePart parameters) order base directions +
          diagonalDerivative (quotientDegreeFourPart parameters) order base directions

/-- Every derivative of order above four is literally zero. -/
theorem quotientRowsDerivative_vanish (cellLength : ℝ) (order : ℕ)
    (base : QuotientState parameters) (directions : Fin order → QuotientState parameters)
    (exceeds : 4 < order) :
    quotientRowsDerivative parameters cellLength order base directions = 0 := by
  unfold quotientRowsDerivative
  rw [diagonalDerivative_zero_of_lt _ _ _ _ (by omega),
    diagonalDerivative_zero_of_lt _ _ _ _ (by omega),
    diagonalDerivative_zero_of_lt _ _ _ _ (by omega),
    diagonalDerivative_zero_of_lt _ _ _ _ (by omega),
    diagonalDerivative_zero_of_lt _ _ _ _ (by omega),
    add_zero, add_zero, add_zero, add_zero]

set_option linter.unusedSimpArgs false in
/-- The zeroth derivative is the literal O14 polynomial itself. -/
theorem quotientRowsDerivative_zeroth (cellLength : ℝ) (base : QuotientState parameters)
    (directions : Fin 0 → QuotientState parameters) :
    quotientRowsDerivative parameters cellLength 0 base directions =
      quotientPolynomialRows parameters cellLength base := by
  unfold quotientRowsDerivative
  rw [diagonalDerivative_zeroth, diagonalDerivative_zeroth, diagonalDerivative_zeroth,
    diagonalDerivative_zeroth, diagonalDerivative_zeroth]
  unfold quotientDegreeZeroPart quotientDegreeOnePart quotientDegreeTwoPart
    quotientDegreeThreePart quotientDegreeFourPart quotientPolynomialRows affineStateCore
  funext row
  fin_cases row <;>
    simp [rowInsert_apply, stateConstantMultilinear_apply, stateLinearMultilinear_apply,
      stateBilinearMultilinear_apply, stateTrilinearMultilinear_apply, stateScalarWrap_apply,
      Pi.add_apply, Pi.single_apply, Fin.ext_iff, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.compr₂_apply,
      LinearMap.compl₂_apply, trilinearPost_apply, linearEvaluation_apply, LinearMap.id_apply,
      map_add, map_sub, map_smul, coe_smul_core] <;>
    abel

end Grad.NonlinearQuotientBounds
