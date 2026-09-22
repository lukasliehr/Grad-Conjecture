import AxisCutoff

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### The fixed radial cap cutoff -/

/-- AL6: the fixed radial cutoff, equal to one on radius `r*/4` and
supported in radius `r*/2`. -/
def capBump (interfaceRadius : ℝ) (radiusPositive : 0 < interfaceRadius) :
    ContDiffBump (0 : SpatialPlane) :=
  ⟨interfaceRadius / 4, interfaceRadius / 2, by linarith, by linarith⟩

theorem capBump_at_origin (interfaceRadius : ℝ) (radiusPositive : 0 < interfaceRadius) :
    capBump interfaceRadius radiusPositive (0 : SpatialPlane) = 1 :=
  (capBump interfaceRadius radiusPositive).one_of_mem_closedBall
    (Metric.mem_closedBall_self (by
      change (0 : ℝ) ≤ interfaceRadius / 4
      linarith))

/-- One cutoff coordinate-linear profile `y ↦ χ(y) y_j v`. -/
def cutoffLinearField {dimension : ℕ} (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) : SpatialPlane → ComplexEuclidean dimension :=
  fun point => (capBump interfaceRadius radiusPositive point *
    coordinateLinear coordinate point) • vector

theorem cutoffLinearField_smooth {dimension : ℕ} (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (cutoffLinearField interfaceRadius radiusPositive coordinate vector) :=
  (((capBump interfaceRadius radiusPositive).contDiff).mul
    (coordinateLinear coordinate).contDiff).smul contDiff_const

/-- The cutoff coordinate profile as an actual closed jet. -/
def cutoffJet {dimension : ℕ} (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) : ClosedJet dimension :=
  globalClosedJet (cutoffLinearField interfaceRadius radiusPositive coordinate vector)
    (cutoffLinearField_smooth interfaceRadius radiusPositive coordinate vector)

theorem cutoffJet_originValue {dimension : ℕ} (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) :
    originValue (cutoffJet interfaceRadius radiusPositive coordinate vector) = 0 := by
  unfold originValue cutoffJet
  rw [globalClosedJet_value]
  unfold cutoffLinearField
  rw [originPoint_val]
  have coordinateZero : coordinateLinear coordinate (0 : SpatialPlane) = 0 := rfl
  rw [coordinateZero, mul_zero, zero_smul]

theorem cutoffJet_originPartial {dimension : ℕ} (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (direction coordinate : Fin 2)
    (vector : ComplexEuclidean dimension) :
    originPartial direction (cutoffJet interfaceRadius radiusPositive coordinate vector) =
      if direction = coordinate then vector else 0 := by
  rw [originPartial_eq_closedDerivative]
  unfold cutoffJet
  rw [globalClosedJet_derivative, ← spatialPartial_eq_ordered]
  change fderiv ℝ (cutoffLinearField interfaceRadius radiusPositive coordinate vector)
    originPoint.val (spatialBasis direction) = _
  have scalarSmooth : ContDiff ℝ ∞ (fun point =>
      capBump interfaceRadius radiusPositive point * coordinateLinear coordinate point) :=
    ((capBump interfaceRadius radiusPositive).contDiff).mul
      (coordinateLinear coordinate).contDiff
  have scalarDifferentiable : DifferentiableAt ℝ
      (fun point => capBump interfaceRadius radiusPositive point *
        coordinateLinear coordinate point) originPoint.val :=
    (scalarSmooth.differentiable (by simp)).differentiableAt
  have smulForm : cutoffLinearField interfaceRadius radiusPositive coordinate vector =
      fun point => (capBump interfaceRadius radiusPositive point *
        coordinateLinear coordinate point) • vector := rfl
  rw [smulForm, fderiv_smul_const scalarDifferentiable vector]
  rw [ContinuousLinearMap.smulRight_apply]
  have productDerivative : fderiv ℝ (fun point =>
      capBump interfaceRadius radiusPositive point *
        coordinateLinear coordinate point) originPoint.val (spatialBasis direction) =
      spatialBasis direction coordinate := by
    have bumpSmooth : ContDiff ℝ ∞
        (fun point : SpatialPlane => capBump interfaceRadius radiusPositive point) :=
      (capBump interfaceRadius radiusPositive).contDiff
    have projSmooth : ContDiff ℝ ∞
        (fun point : SpatialPlane => coordinateLinear coordinate point) :=
      (coordinateLinear coordinate).contDiff
    rw [fderiv_fun_mul ((bumpSmooth.differentiable (by simp)).differentiableAt)
      ((projSmooth.differentiable (by simp)).differentiableAt)]
    rw [add_apply, smul_apply,
      smul_apply]
    rw [originPoint_val, capBump_at_origin, (coordinateLinear coordinate).fderiv]
    have coordinateZero : coordinateLinear coordinate (0 : SpatialPlane) = 0 := rfl
    rw [coordinateZero, one_smul, zero_smul, add_zero]
    rfl
  rw [productDerivative]
  have basisComponent : spatialBasis direction coordinate =
      if direction = coordinate then (1 : ℝ) else 0 := by
    change Pi.single (M := fun _ : Fin 2 => ℝ) direction 1 coordinate = _
    by_cases equal : direction = coordinate
    · rw [if_pos equal, ← equal]
      exact Pi.single_eq_same direction 1
    · rw [if_neg equal]
      exact Pi.single_eq_of_ne (fun collide => equal collide.symm) 1
  rw [basisComponent]
  by_cases equal : direction = coordinate
  · rw [if_pos equal, if_pos equal, one_smul]
  · rw [if_neg equal, if_neg equal, zero_smul]

/-! ### Insertion of axis data against two fixed jets -/

/-- The raw coefficients of an axis-data insertion. -/
def axisInsertionCoefficients {dimension : ℕ} (data : TCore parameters)
    (firstJet secondJet : ClosedJet dimension) : ℤ → ClosedJet dimension :=
  fun cell => (data.val cell 0) • firstJet + (data.val cell 1) • secondJet

theorem axisInsertion_row_le {dimension : ℕ} (data : TCore parameters)
    (firstJet secondJet : ClosedJet dimension) (grade : ℕ) (cell : ℤ)
    {firstConstant secondConstant : ℝ}
    (firstRow : ∀ innerCell : ℤ, ‖cellGradeRowLinear (grade := grade) parameters innerCell
      firstJet‖ ≤ firstConstant * axisWeight parameters grade innerCell)
    (secondRow : ∀ innerCell : ℤ, ‖cellGradeRowLinear (grade := grade) parameters innerCell
      secondJet‖ ≤ secondConstant * axisWeight parameters grade innerCell) :
    ‖cellGradeRowLinear (grade := grade) parameters cell
        (axisInsertionCoefficients data firstJet secondJet cell)‖ ≤
      (firstConstant + secondConstant) *
        ‖axisCoordinates parameters grade data.val cell‖ := by
  unfold axisInsertionCoefficients
  rw [map_add, map_smul, map_smul]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul]
  have firstComponent : ‖data.val cell 0‖ ≤ ‖data.val cell‖ :=
    PiLp.norm_apply_le (data.val cell) 0
  have secondComponent : ‖data.val cell 1‖ ≤ ‖data.val cell‖ :=
    PiLp.norm_apply_le (data.val cell) 1
  have coordinateNorm : ‖axisCoordinates parameters grade data.val cell‖ =
      axisWeight parameters grade cell * ‖data.val cell‖ := by
    unfold axisCoordinates
    rw [norm_smul, Real.norm_of_nonneg (axisWeight_pos parameters grade cell).le]
  rw [coordinateNorm]
  calc ‖data.val cell 0‖ * ‖cellGradeRowLinear (grade := grade) parameters cell firstJet‖ +
      ‖data.val cell 1‖ * ‖cellGradeRowLinear (grade := grade) parameters cell secondJet‖ ≤
      ‖data.val cell‖ * (firstConstant * axisWeight parameters grade cell) +
        ‖data.val cell‖ * (secondConstant * axisWeight parameters grade cell) := by
        apply add_le_add
        · exact mul_le_mul firstComponent (firstRow cell) (norm_nonneg _) (norm_nonneg _)
        · exact mul_le_mul secondComponent (secondRow cell) (norm_nonneg _) (norm_nonneg _)
    _ = (firstConstant + secondConstant) *
        (axisWeight parameters grade cell * ‖data.val cell‖) := by ring

theorem axisInsertion_mem {dimension : ℕ} (data : TCore parameters)
    (firstJet secondJet : ClosedJet dimension) :
    axisInsertionCoefficients data firstJet secondJet ∈
      originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨firstConstant, firstNonneg, firstRow⟩ :=
    fixedJet_row_bound parameters firstJet grade
  obtain ⟨secondConstant, secondNonneg, secondRow⟩ :=
    fixedJet_row_bound parameters secondJet grade
  apply ((data.property grade).const_smul
    ((firstConstant + secondConstant : ℝ) : ℂ)).mono'
  intro cell
  have rowBound := axisInsertion_row_le data firstJet secondJet grade cell firstRow secondRow
  change ‖cellGradeRowLinear (grade := grade) parameters cell
    (axisInsertionCoefficients data firstJet secondJet cell)‖ ≤ _
  apply rowBound.trans
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (by positivity : (0 : ℝ) ≤ firstConstant + secondConstant)]

/-- The axis-data insertion against two fixed jets, as an actual original
coefficient-core field. -/
def axisInsertion {dimension : ℕ} (data : TCore parameters)
    (firstJet secondJet : ClosedJet dimension) : ACore parameters dimension :=
  ⟨axisInsertionCoefficients data firstJet secondJet,
    axisInsertion_mem data firstJet secondJet⟩

theorem axisInsertion_val {dimension : ℕ} (data : TCore parameters)
    (firstJet secondJet : ClosedJet dimension) (cell : ℤ) :
    (axisInsertion data firstJet secondJet).val cell =
      (data.val cell 0) • firstJet + (data.val cell 1) • secondJet := rfl

/-- AL27's fixed-cutoff skeleton: the insertion is bounded by the exact
`T^q` norm of the inserted data, with a constant from the two fixed jets. -/
theorem axisInsertion_grade_bound {dimension : ℕ} (data : TCore parameters)
    (firstJet secondJet : ClosedJet dimension) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      originalGradeNorm grade (axisInsertion data firstJet secondJet) ≤
        constant * axisGradeNorm parameters grade data := by
  obtain ⟨firstConstant, firstNonneg, firstRow⟩ :=
    fixedJet_row_bound parameters firstJet grade
  obtain ⟨secondConstant, secondNonneg, secondRow⟩ :=
    fixedJet_row_bound parameters secondJet grade
  refine ⟨firstConstant + secondConstant, by positivity, ?_⟩
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply]
  have packSmul : (firstConstant + secondConstant) * axisGradeNorm parameters grade data =
      ‖((firstConstant + secondConstant : ℝ) : ℂ) •
        (⟨axisCoordinates parameters grade data.val, data.property grade⟩ :
          lp (fun _ : ℤ => ComplexEuclidean 2) 2)‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rfl
  rw [packSmul]
  apply lp.norm_mono (by norm_num)
  intro cell
  have rowBound := axisInsertion_row_le data firstJet secondJet grade cell firstRow secondRow
  change ‖cellGradeRowLinear (grade := grade) parameters cell
    (axisInsertionCoefficients data firstJet secondJet cell)‖ ≤ _
  apply rowBound.trans
  rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ firstConstant + secondConstant)]

/-! ### The constraint-shaped axis lift -/

/-- The tangential constant vector `e_T`. -/
def tangentVector : ComplexEuclidean 3 := EuclideanSpace.single 1 1

/-- The scalar unit value. -/
def scalarVector : ComplexEuclidean 1 := EuclideanSpace.single 0 1

/-- AL15's physical vector lift `chi Q(eta) y` with the transverse part
supplied as an explicit field: the tangential summand is the literal
`chi (eta · y) e_T` insertion. -/
def liftPhysicalField (interfaceRadius : ℝ) (radiusPositive : 0 < interfaceRadius)
    (transverse : ACore parameters 3) (tangential : TCore parameters) :
    ACore parameters 3 :=
  transverse + axisInsertion tangential
    (cutoffJet interfaceRadius radiusPositive 0 tangentVector)
    (cutoffJet interfaceRadius radiusPositive 1 tangentVector)

/-- AL15's scalar lift `chi (sigma · y)`. -/
def liftScalarField (interfaceRadius : ℝ) (radiusPositive : 0 < interfaceRadius)
    (spin : TCore parameters) : ACore parameters 1 :=
  axisInsertion spin
    (cutoffJet interfaceRadius radiusPositive 0 scalarVector)
    (cutoffJet interfaceRadius radiusPositive 1 scalarVector)

/-- The full lifted direction `E d` in the quotient state carrier. -/
def axisLiftDirection (interfaceRadius : ℝ) (radiusPositive : 0 < interfaceRadius)
    (transverse : ACore parameters 3) (data : AxisData parameters) :
    QuotientState parameters :=
  (0, liftPhysicalField interfaceRadius radiusPositive transverse data.2,
    liftScalarField interfaceRadius radiusPositive data.1)

theorem axisLiftDirection_stateField (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (transverse : ACore parameters 3)
    (data : AxisData parameters) :
    stateField (axisLiftDirection interfaceRadius radiusPositive transverse data) =
      liftPhysicalField interfaceRadius radiusPositive transverse data.2 := rfl

theorem axisLiftDirection_statePotential (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (transverse : ACore parameters 3)
    (data : AxisData parameters) :
    statePotential (axisLiftDirection interfaceRadius radiusPositive transverse data) =
      liftScalarField interfaceRadius radiusPositive data.1 := rfl

theorem euclidean_pair_eta (point : ComplexEuclidean 2) :
    planarPair (point 0) (point 1) = point := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem tangentVector_component_one : tangentVector 1 = 1 := by
  change Pi.single (M := fun _ : Fin 3 => ℂ) 1 1 1 = 1
  exact Pi.single_eq_same 1 1

theorem scalarVector_component_zero : scalarVector 0 = 1 := by
  change Pi.single (M := fun _ : Fin 1 => ℂ) 0 1 0 = 1
  exact Pi.single_eq_same 0 1

/-- The lifted direction's physical field vanishes on the axis, cell by cell. -/
theorem axisLift_field_originValue (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (transverse : ACore parameters 3)
    (data : AxisData parameters)
    (transverseValue : ∀ cell : ℤ, originValue (transverse.val cell) = 0) (cell : ℤ) :
    originValue ((stateField (axisLiftDirection interfaceRadius radiusPositive
      transverse data)).val cell) = 0 := by
  rw [axisLiftDirection_stateField]
  unfold liftPhysicalField
  rw [acore_val_add, originValue_add, transverseValue, zero_add, axisInsertion_val,
    originValue_add, originValue_smul, originValue_smul, cutoffJet_originValue,
    cutoffJet_originValue, smul_zero, smul_zero, add_zero]

/-- The spin half of AL19: the scalar gradient trace of the lifted scalar
field returns the inserted spin data. -/
theorem scalarGradient_axisLift (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (spin : TCore parameters) (cell : ℤ) :
    scalarOriginGradient (liftScalarField interfaceRadius radiusPositive spin) cell =
      spin.val cell := by
  unfold scalarOriginGradient liftScalarField
  have componentValue : ∀ direction : Fin 2,
      originPartial direction ((axisInsertion spin
        (cutoffJet interfaceRadius radiusPositive 0 scalarVector)
        (cutoffJet interfaceRadius radiusPositive 1 scalarVector)).val cell) 0 =
      spin.val cell direction := by
    intro direction
    rw [axisInsertion_val, originPartial_add, originPartial_smul, originPartial_smul,
      cutoffJet_originPartial, cutoffJet_originPartial]
    fin_cases direction
    · rw [show ((⟨0, by omega⟩ : Fin 2) = (0 : Fin 2)) from rfl]
      rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), smul_zero,
        add_zero, euclidean_smul_component, scalarVector_component_zero, mul_one]
    · rw [show ((⟨1, by omega⟩ : Fin 2) = (1 : Fin 2)) from rfl]
      rw [if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, smul_zero,
        zero_add, euclidean_smul_component, scalarVector_component_zero, mul_one]
  rw [componentValue 0, componentValue 1]
  exact euclidean_pair_eta (spin.val cell)

/-- The affine half of AL19: the tangential gradient trace of the lifted
physical field returns the inserted affine data. -/
theorem tangentialGradient_axisLift (interfaceRadius : ℝ)
    (radiusPositive : 0 < interfaceRadius) (transverse : ACore parameters 3)
    (tangential : TCore parameters)
    (transverseTangential : ∀ (cell : ℤ) (direction : Fin 2),
      originPartial direction (transverse.val cell) 1 = 0) (cell : ℤ) :
    tangentialOriginGradient
        (liftPhysicalField interfaceRadius radiusPositive transverse tangential) cell =
      tangential.val cell := by
  unfold tangentialOriginGradient liftPhysicalField
  have componentValue : ∀ direction : Fin 2,
      originPartial direction ((transverse + axisInsertion tangential
        (cutoffJet interfaceRadius radiusPositive 0 tangentVector)
        (cutoffJet interfaceRadius radiusPositive 1 tangentVector)).val cell) 1 =
      tangential.val cell direction := by
    intro direction
    rw [acore_val_add, originPartial_add, euclidean_add_component,
      transverseTangential cell direction, zero_add, axisInsertion_val,
      originPartial_add, originPartial_smul, originPartial_smul,
      cutoffJet_originPartial, cutoffJet_originPartial]
    fin_cases direction
    · rw [show ((⟨0, by omega⟩ : Fin 2) = (0 : Fin 2)) from rfl]
      rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), smul_zero,
        add_zero, euclidean_smul_component, tangentVector_component_one, mul_one]
    · rw [show ((⟨1, by omega⟩ : Fin 2) = (1 : Fin 2)) from rfl]
      rw [if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, smul_zero,
        zero_add, euclidean_smul_component, tangentVector_component_one, mul_one]
  rw [componentValue 0, componentValue 1]
  exact euclidean_pair_eta (tangential.val cell)

/-- AL19 at the coefficient-core level: the direction extraction of the
axis lift returns exactly the inserted axis data. -/
theorem kappa_axisLift (interfaceRadius : ℝ) (radiusPositive : 0 < interfaceRadius)
    (transverse : ACore parameters 3) (data : AxisData parameters)
    (transverseTangential : ∀ (cell : ℤ) (direction : Fin 2),
      originPartial direction (transverse.val cell) 1 = 0) :
    kappaDirection (axisLiftDirection interfaceRadius radiusPositive transverse data) =
      (data.1.val, data.2.val) := by
  unfold kappaDirection
  apply Prod.ext
  · funext cell
    exact scalarGradient_axisLift interfaceRadius radiusPositive data.1 cell
  · funext cell
    exact tangentialGradient_axisLift interfaceRadius radiusPositive transverse data.2
      transverseTangential cell

end Grad.AxisSplit
