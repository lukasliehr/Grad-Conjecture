import AxisDataBundle

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### Direction linearity of the first-order linearization -/

theorem diagonalDerivative_one_sub {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup E] [Module ℂ E] {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (base first second : V) :
    diagonalDerivative W 1 base ![first - second] =
      diagonalDerivative W 1 base ![first] - diagonalDerivative W 1 base ![second] := by
  rw [diagonalDerivative_one, diagonalDerivative_one, diagonalDerivative_one,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro slot _
  exact W.map_update_sub (fun _ => base) slot first second

theorem diagonalDerivative_one_zero {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup E] [Module ℂ E] {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (base : V) :
    diagonalDerivative W 1 base ![0] = 0 := by
  rw [diagonalDerivative_one]
  apply Finset.sum_eq_zero
  intro slot _
  exact W.map_update_zero (fun _ => base) slot

/-- The linearization is subtractive in its direction. -/
theorem rowsDerivative_direction_sub (cellLength : ℝ)
    (base first second : QuotientState parameters) :
    quotientRowsDerivative parameters cellLength 1 base ![first - second] =
      quotientRowsDerivative parameters cellLength 1 base ![first] -
        quotientRowsDerivative parameters cellLength 1 base ![second] := by
  unfold quotientRowsDerivative
  rw [diagonalDerivative_one_sub, diagonalDerivative_one_sub, diagonalDerivative_one_sub,
    diagonalDerivative_one_sub, diagonalDerivative_one_sub]
  abel

/-- The linearization kills the zero direction. -/
theorem rowsDerivative_direction_zero (cellLength : ℝ)
    (base : QuotientState parameters) :
    quotientRowsDerivative parameters cellLength 1 base ![0] = 0 := by
  unfold quotientRowsDerivative
  rw [diagonalDerivative_one_zero, diagonalDerivative_one_zero, diagonalDerivative_one_zero,
    diagonalDerivative_one_zero, diagonalDerivative_one_zero]
  abel

/-! ### Subtractivity of the bundled extractions -/

theorem originValue_component_sub {dimension : ℕ} (first second : ClosedJet dimension)
    (coordinate : Fin dimension) :
    originValue (first - second) coordinate =
      originValue first coordinate - originValue second coordinate := by
  rw [originValue_sub]
  rfl

theorem originPartial_component_sub {dimension : ℕ} (direction : Fin 2)
    (first second : ClosedJet dimension) (coordinate : Fin dimension) :
    originPartial direction (first - second) coordinate =
      originPartial direction first coordinate -
        originPartial direction second coordinate := by
  rw [originPartial_sub direction]
  rfl

theorem planarPair_sub (a b c d : ℂ) :
    planarPair a b - planarPair c d = planarPair (a - c) (b - d) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem scalarOriginGradient_sub (first second : ACore parameters 1) (cell : ℤ) :
    scalarOriginGradient (first - second) cell =
      scalarOriginGradient first cell - scalarOriginGradient second cell := by
  unfold scalarOriginGradient
  rw [planarPair_sub]
  rw [show (first - second).val cell = first.val cell - second.val cell from rfl]
  rw [originPartial_component_sub, originPartial_component_sub]

theorem tangentialOriginGradient_sub (first second : ACore parameters 3) (cell : ℤ) :
    tangentialOriginGradient (first - second) cell =
      tangentialOriginGradient first cell - tangentialOriginGradient second cell := by
  unfold tangentialOriginGradient
  rw [planarPair_sub]
  rw [show (first - second).val cell = first.val cell - second.val cell from rfl]
  rw [originPartial_component_sub, originPartial_component_sub]

theorem kappaData_sub (first second : QuotientState parameters) :
    kappaData (parameters := parameters) (first - second) =
      kappaData first - kappaData second := by
  unfold kappaData
  apply Prod.ext
  · apply Subtype.ext
    funext cell
    have potentialSub : statePotential (first - second) =
        statePotential first - statePotential second :=
      map_sub statePotential first second
    change scalarOriginGradient (statePotential (first - second)) cell = _
    rw [potentialSub]
    exact scalarOriginGradient_sub _ _ cell
  · apply Subtype.ext
    funext cell
    have fieldSub : stateField (first - second) =
        stateField first - stateField second :=
      map_sub stateField first second
    change tangentialOriginGradient (stateField (first - second)) cell = _
    rw [fieldSub]
    exact tangentialOriginGradient_sub _ _ cell

theorem sigmaData_sub (first second : QuotientRows parameters) :
    sigmaData (first - second) = sigmaData first - sigmaData second := by
  apply Subtype.ext
  funext cell
  unfold sigmaData
  change sigmaExtraction (first - second) cell =
    sigmaExtraction first cell - sigmaExtraction second cell
  unfold sigmaExtraction
  rw [planarPair_sub]
  rw [show (first - second) 0 = first 0 - second 0 from rfl,
    show (first - second) 1 = first 1 - second 1 from rfl]
  rw [show ((first 0 - second 0)).val cell = (first 0).val cell - (second 0).val cell
      from rfl,
    show ((first 1 - second 1)).val cell = (first 1).val cell - (second 1).val cell
      from rfl]
  rw [originValue_component_sub, originValue_component_sub]
  congr 1
  · ring
  · ring

theorem planarJPair_sub (first second : ComplexEuclidean 2) :
    planarJPair (first - second) = planarJPair first - planarJPair second := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change -((first - second) 1) = -(first 1) - -(second 1)
    rw [euclidean_sub_component]
    ring
  · change (first - second) 0 = first 0 - second 0
    exact euclidean_sub_component first second 0

theorem etaData_sub (cellLength : ℝ) (first second : QuotientRows parameters) :
    etaData cellLength (first - second) =
      etaData cellLength first - etaData cellLength second := by
  apply Subtype.ext
  funext cell
  rw [show (etaData cellLength first - etaData cellLength second).val cell =
    (etaData cellLength first).val cell - (etaData cellLength second).val cell from rfl]
  rw [etaData_val, etaData_val, etaData_val]
  unfold etaExtraction
  rw [← smul_sub]
  congr 1
  rw [← planarJPair_sub]
  congr 1
  rw [show (first - second) 3 = first 3 - second 3 from rfl]
  rw [scalarOriginGradient_sub]
  have sigmaSub : sigmaExtraction (first - second) cell =
      sigmaExtraction first cell - sigmaExtraction second cell := by
    have bundled := congrArg (fun data => data.val cell) (sigmaData_sub first second)
    exact bundled
  rw [sigmaSub, smul_sub]
  abel

theorem extractionData_sub (cellLength : ℝ) (first second : QuotientRows parameters) :
    extractionData cellLength (first - second) =
      extractionData cellLength first - extractionData cellLength second := by
  unfold extractionData
  apply Prod.ext
  · exact sigmaData_sub first second
  · exact etaData_sub cellLength first second

/-! ### The configured split operators -/

variable (cellLength : ℝ) (interfaceRadius : ℝ)
variable (radiusPositive : 0 < interfaceRadius)
variable (base : QuotientState parameters)
variable (transverseMap : AxisData parameters → ACore parameters 3)

/-- AL15's lift with its data-dependent transverse slot. -/
def liftMap (data : AxisData parameters) : QuotientState parameters :=
  axisLiftDirection interfaceRadius radiusPositive (transverseMap data) data

/-- The compiled forward linearization at the current state. -/
def forwardMap (direction : QuotientState parameters) : QuotientRows parameters :=
  quotientRowsDerivative parameters cellLength 1 base ![direction]

/-- AL7's lifted source `T_b = A_b E_b`. -/
def sourceLift (data : AxisData parameters) : QuotientRows parameters :=
  forwardMap cellLength base (liftMap interfaceRadius radiusPositive transverseMap data)

/-- AL22's flat domain projection `P_X = I - E_b kappa`. -/
def domainProjection (direction : QuotientState parameters) : QuotientState parameters :=
  direction - liftMap interfaceRadius radiusPositive transverseMap (kappaData direction)

/-- AL22's flat range projection `P_Y = I - T_b 𝒥`. -/
def rangeProjection (source : QuotientRows parameters) : QuotientRows parameters :=
  source - sourceLift cellLength interfaceRadius radiusPositive base transverseMap
    (extractionData cellLength source)

end Grad.AxisSplit
