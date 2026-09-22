import AxisRowTraces

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### Planar complex pairs -/

/-- A planar complex value from its two components. -/
def planarPair (first second : ℂ) : ComplexEuclidean 2 :=
  WithLp.toLp 2 ![first, second]

@[simp] theorem planarPair_component_zero (first second : ℂ) :
    planarPair first second 0 = first := rfl

@[simp] theorem planarPair_component_one (first second : ℂ) :
    planarPair first second 1 = second := rfl

theorem planarPair_add (a b c d : ℂ) :
    planarPair a b + planarPair c d = planarPair (a + c) (b + d) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem planarPair_smul (scalar a b : ℂ) :
    scalar • planarPair a b = planarPair (scalar * a) (scalar * b) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem planarPair_eq_iff {a b c d : ℂ} :
    planarPair a b = planarPair c d ↔ a = c ∧ b = d := by
  constructor
  · intro equal
    exact ⟨by rw [← planarPair_component_zero a b, equal, planarPair_component_zero],
      by rw [← planarPair_component_one a b, equal, planarPair_component_one]⟩
  · intro ⟨firstEq, secondEq⟩
    rw [firstEq, secondEq]

/-- The planar rotation `J(x₁, x₂) = (-x₂, x₁)`. -/
def planarJPair (point : ComplexEuclidean 2) : ComplexEuclidean 2 :=
  planarPair (-(point 1)) (point 0)

theorem planarJPair_pair (a b : ℂ) :
    planarJPair (planarPair a b) = planarPair (-b) a := rfl

/-! ### The axis data of directions and sources -/

/-- The complex scalar gradient trace at the axis, cell by cell. -/
def scalarOriginGradient (field : ACore parameters 1) (cell : ℤ) : ComplexEuclidean 2 :=
  planarPair (originPartial 0 (field.val cell) 0) (originPartial 1 (field.val cell) 0)

/-- The tangential (second-component) gradient trace at the axis, cell by cell. -/
def tangentialOriginGradient (field : ACore parameters 3) (cell : ℤ) : ComplexEuclidean 2 :=
  planarPair (originPartial 0 (field.val cell) 1) (originPartial 1 (field.val cell) 1)

/-- AL10: the spin extraction `sigma(Z)` from the two spin source values. -/
def sigmaExtraction (Z : QuotientRows parameters) (cell : ℤ) : ComplexEuclidean 2 :=
  planarPair ((originValue ((Z 0).val cell) 0 + originValue ((Z 1).val cell) 0) / 2)
    ((originValue ((Z 0).val cell) 0 - originValue ((Z 1).val cell) 0) / (2 * Complex.I))

/-- AL10: the affine extraction `eta(Z) = L⁻¹ J (grad h(0) + ∂_ζ sigma(Z))`. -/
def etaExtraction (cellLength : ℝ) (Z : QuotientRows parameters) (cell : ℤ) :
    ComplexEuclidean 2 :=
  ((cellLength : ℂ)⁻¹) • planarJPair (scalarOriginGradient (Z 3) cell +
    ((cell : ℂ) * Complex.I) • sigmaExtraction Z cell)

/-- AL10: the full axis-data extraction `𝒥 Z = (sigma(Z), eta(Z))`. -/
def axisExtraction (cellLength : ℝ) (Z : QuotientRows parameters) :
    (ℤ → ComplexEuclidean 2) × (ℤ → ComplexEuclidean 2) :=
  (sigmaExtraction Z, etaExtraction cellLength Z)

/-- The direction extraction `kappa(dot x) = (grad S(0), eta)`: the scalar
first jet and the tangential first jet of the physical field. -/
def kappaDirection (direction : QuotientState parameters) :
    (ℤ → ComplexEuclidean 2) × (ℤ → ComplexEuclidean 2) :=
  (fun cell => scalarOriginGradient (statePotential direction) cell,
    fun cell => tangentialOriginGradient (stateField direction) cell)

/-! ### Componentwise evaluations -/

theorem euclidean_add_component {dimension : ℕ} (x y : ComplexEuclidean dimension)
    (coordinate : Fin dimension) : (x + y) coordinate = x coordinate + y coordinate := rfl

theorem euclidean_sub_component {dimension : ℕ} (x y : ComplexEuclidean dimension)
    (coordinate : Fin dimension) : (x - y) coordinate = x coordinate - y coordinate := rfl

theorem euclidean_smul_component {dimension : ℕ} (scalar : ℂ)
    (x : ComplexEuclidean dimension) (coordinate : Fin dimension) :
    (scalar • x) coordinate = scalar * x coordinate := rfl

theorem euclidean_zero_component {dimension : ℕ} (coordinate : Fin dimension) :
    (0 : ComplexEuclidean dimension) coordinate = 0 := rfl

/-- The spin-value decomposition of the `∂₊` trace. -/
theorem partialPlus_originValue_component (field : ACore parameters 1) (cell : ℤ) :
    originValue ((partialPlusCore parameters field).val cell) 0 =
      originPartial 0 (field.val cell) 0 + Complex.I * originPartial 1 (field.val cell) 0 := by
  have expand : (partialPlusCore parameters field).val cell =
      partialJet 0 (field.val cell) + Complex.I • partialJet 1 (field.val cell) := rfl
  rw [expand, originValue_add, originValue_smul, euclidean_add_component,
    euclidean_smul_component]
  rfl

theorem partialMinus_originValue_component (field : ACore parameters 1) (cell : ℤ) :
    originValue ((partialMinusCore parameters field).val cell) 0 =
      originPartial 0 (field.val cell) 0 - Complex.I * originPartial 1 (field.val cell) 0 := by
  have expand : (partialMinusCore parameters field).val cell =
      partialJet 0 (field.val cell) - Complex.I • partialJet 1 (field.val cell) := rfl
  rw [expand, originValue_sub, originValue_smul, euclidean_sub_component,
    euclidean_smul_component]
  rfl

/-- The tangential pairing with `e_T` extracts the second physical component. -/
theorem physicalDot_single_component (vector : ComplexEuclidean 3) :
    physicalDotProduct ![vector, EuclideanSpace.single 1 1] 0 = vector 1 := by
  rw [physicalDotProduct_value]
  unfold Grad.NonlinearQuotient.complexDot
  rw [Fin.sum_univ_three]
  have componentZero : (EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) 0 = 0 := by
    change Pi.single (M := fun _ : Fin 3 => ℂ) 1 1 0 = 0
    exact Pi.single_eq_of_ne (by decide) 1
  have componentOne : (EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) 1 = 1 := by
    change Pi.single (M := fun _ : Fin 3 => ℂ) 1 1 1 = 1
    exact Pi.single_eq_same 1 1
  have componentTwo : (EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) 2 = 0 := by
    change Pi.single (M := fun _ : Fin 3 => ℂ) 1 1 2 = 0
    exact Pi.single_eq_of_ne (by decide) 1
  rw [componentZero, componentOne, componentTwo, mul_zero, mul_zero, mul_one,
    zero_add, add_zero]

theorem dotOperation_originValue_eT (first : ACore parameters 3) (cell : ℤ) :
    originValue ((dotOperation parameters first (eTConstantCore parameters)).val cell) =
      physicalDotProduct ![originValue (first.val cell), EuclideanSpace.single 1 1] :=
  dotOperation_originValue_constant_right first (EuclideanSpace.single 1 1) cell

/-! ### AL11 at the coefficient-core level -/

/-- The spin half of AL11: the extraction of the first two linearized rows
is the scalar first jet of the direction, at every current state. -/
theorem sigmaExtraction_linearization (cellLength : ℝ)
    (base direction : QuotientState parameters) (cell : ℤ) :
    sigmaExtraction (quotientRowsDerivative parameters cellLength 1 base ![direction])
        cell =
      scalarOriginGradient (statePotential direction) cell := by
  unfold sigmaExtraction scalarOriginGradient
  rw [derivativeRows_row_zero_originValue, derivativeRows_row_one_originValue]
  rw [partialPlus_originValue_component, partialMinus_originValue_component]
  set firstComponent := originPartial 0 ((statePotential direction).val cell) 0
  set secondComponent := originPartial 1 ((statePotential direction).val cell) 0
  apply planarPair_eq_iff.mpr
  constructor
  · ring
  · have nonzero : (2 : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero two_ne_zero Complex.I_ne_zero
    rw [div_eq_iff nonzero]
    ring

/-- The affine half of AL11: the extraction of the linearized fourth row,
corrected by the cell derivative of the spin extraction, is the tangential
first jet of the direction. -/
theorem etaExtraction_linearization (cellLength : ℝ) (lengthPositive : 0 < cellLength)
    (base direction : QuotientState parameters)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (directionVanishes : ∀ cell : ℤ, originValue ((stateField direction).val cell) = 0)
    (cell : ℤ) :
    etaExtraction cellLength
        (quotientRowsDerivative parameters cellLength 1 base ![direction]) cell =
      tangentialOriginGradient (stateField direction) cell := by
  unfold etaExtraction
  rw [sigmaExtraction_linearization]
  set tangentialZero := originPartial 0 ((stateField direction).val cell) 1 with tangentialZeroDef
  set tangentialOne := originPartial 1 ((stateField direction).val cell) 1 with tangentialOneDef
  set scalarZero := originPartial 0 ((statePotential direction).val cell) 0 with scalarZeroDef
  set scalarOne := originPartial 1 ((statePotential direction).val cell) 0 with scalarOneDef
  have gradientRowThree : scalarOriginGradient
      ((quotientRowsDerivative parameters cellLength 1 base ![direction]) 3) cell =
      planarPair ((cellLength : ℂ) * tangentialOne - (cell : ℂ) * Complex.I * scalarZero)
        (-((cellLength : ℂ) * tangentialZero) - (cell : ℂ) * Complex.I * scalarOne) := by
    unfold scalarOriginGradient
    rw [derivativeRows_row_three_originPartial cellLength base direction baseVanishes
      directionVanishes 0 cell,
      derivativeRows_row_three_originPartial cellLength base direction baseVanishes
      directionVanishes 1 cell]
    rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1),
      if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl]
    rw [dotOperation_originValue_eT, dotOperation_originValue_eT]
    apply planarPair_eq_iff.mpr
    constructor
    · rw [euclidean_sub_component, euclidean_smul_component, euclidean_smul_component,
        euclidean_sub_component, euclidean_zero_component]
      rw [physicalDot_single_component]
      have partialValue : originValue ((partialCore parameters 1
          (stateField direction)).val cell) 1 = tangentialOne := rfl
      rw [partialValue]
      ring
    · rw [euclidean_sub_component, euclidean_smul_component, euclidean_smul_component,
        euclidean_sub_component, euclidean_zero_component]
      rw [physicalDot_single_component]
      have partialValue : originValue ((partialCore parameters 0
          (stateField direction)).val cell) 1 = tangentialZero := rfl
      rw [partialValue]
      ring
  rw [gradientRowThree]
  have sigmaValue : ((cell : ℂ) * Complex.I) •
      scalarOriginGradient (statePotential direction) cell =
      planarPair ((cell : ℂ) * Complex.I * scalarZero)
        ((cell : ℂ) * Complex.I * scalarOne) := by
    unfold scalarOriginGradient
    rw [planarPair_smul]
  rw [sigmaValue, planarPair_add]
  have innerSimplify : planarPair
      ((cellLength : ℂ) * tangentialOne - (cell : ℂ) * Complex.I * scalarZero +
        (cell : ℂ) * Complex.I * scalarZero)
      (-((cellLength : ℂ) * tangentialZero) - (cell : ℂ) * Complex.I * scalarOne +
        (cell : ℂ) * Complex.I * scalarOne) =
      planarPair ((cellLength : ℂ) * tangentialOne)
        (-((cellLength : ℂ) * tangentialZero)) := by
    apply planarPair_eq_iff.mpr
    exact ⟨by ring, by ring⟩
  rw [innerSimplify, planarJPair_pair, planarPair_smul]
  have lengthNonzero : (cellLength : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr lengthPositive.ne'
  unfold tangentialOriginGradient
  apply planarPair_eq_iff.mpr
  constructor
  · rw [neg_neg]
    rw [← mul_assoc, inv_mul_cancel₀ lengthNonzero, one_mul]
  · rw [← mul_assoc, inv_mul_cancel₀ lengthNonzero, one_mul]

/-- AL11 at the coefficient-core level: the axis extraction of the actual
first-order quotient linearization is the direction extraction `kappa`, at
every current state whose physical field vanishes on the axis and for every
direction whose physical field vanishes on the axis. -/
theorem axisExtraction_linearization (cellLength : ℝ) (lengthPositive : 0 < cellLength)
    (base direction : QuotientState parameters)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (directionVanishes : ∀ cell : ℤ, originValue ((stateField direction).val cell) = 0) :
    axisExtraction cellLength
        (quotientRowsDerivative parameters cellLength 1 base ![direction]) =
      kappaDirection direction := by
  unfold axisExtraction kappaDirection
  apply Prod.ext
  · funext cell
    exact sigmaExtraction_linearization cellLength base direction cell
  · funext cell
    exact etaExtraction_linearization cellLength lengthPositive base direction
      baseVanishes directionVanishes cell

end Grad.AxisSplit
