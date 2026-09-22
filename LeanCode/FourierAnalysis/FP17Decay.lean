import FP17Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

set_option maxHeartbeats 500000

open Filter Set MeasureTheory
open scoped ContDiff Topology Interval

namespace Grad.CartesianState

open Grad.ClosedJets

local instance fp17DecayCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- Prepend one actual cell-coordinate derivative to a mixed word. -/
def prependCellCoordinate {order : ℕ} (word : MixedCartesianWord order) :
    MixedCartesianWord (order + 1) :=
  Fin.cons 2 word

private def fp17CellEmbeddingLinear : ℝ →ₗ[ℝ] SpatialCell where
  toFun cell := assembleSpatialCell 0 cell
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [assembleSpatialCell]
  map_smul' scalar cell := by
    ext coordinate
    fin_cases coordinate <;> simp [assembleSpatialCell]

private noncomputable def fp17CellEmbeddingCLM : ℝ →L[ℝ] SpatialCell :=
  fp17CellEmbeddingLinear.toContinuousLinearMap

@[simp] private theorem fp17CellEmbeddingCLM_apply (cell : ℝ) :
    fp17CellEmbeddingCLM cell = assembleSpatialCell 0 cell := rfl

@[simp] private theorem fp17CellEmbeddingCLM_one :
    fp17CellEmbeddingCLM 1 = spatialCellBasis 2 := by
  ext coordinate
  fin_cases coordinate <;> rfl

private theorem assembleSpatialCell_cell_hasFDerivAt
    (point : SpatialPlane) (cell : ℝ) :
    HasFDerivAt (fun candidate : ℝ => assembleSpatialCell point candidate)
      fp17CellEmbeddingCLM cell := by
  have functionIdentity :
      (fun candidate : ℝ => assembleSpatialCell point candidate) =
        fun candidate => fp17CellEmbeddingCLM candidate +
          assembleSpatialCell point 0 := by
    funext candidate
    ext coordinate
    fin_cases coordinate <;> simp [assembleSpatialCell]
  rw [functionIdentity]
  exact fp17CellEmbeddingCLM.hasFDerivAt.add_const _

/-- The next cell-coordinate extension is the actual derivative, on every
interior disk fibre and every real representative of the circle. -/
private theorem actualMixedDerivative_cell_hasDerivAt
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) (cell : ℝ) :
    HasDerivAt
      (fun candidate => mixedCartesianDerivative order word
        (diskCellLift field.value) (assembleSpatialCell point candidate))
      (mixedCartesianDerivative (order + 1) (prependCellCoordinate word)
        (diskCellLift field.value) (assembleSpatialCell point cell)) cell := by
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  have smoothAt := (field.smoothInterior _ cylinderMembership).contDiffAt
    (openUnitCylinder_isOpen.mem_nhds cylinderMembership)
  have tensorDifferentiable := smoothAt.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
  have evaluatedDifferentiable : DifferentiableAt ℝ
      (fun ambient => mixedCartesianDerivative order word
        (diskCellLift field.value) ambient)
      (assembleSpatialCell point cell) :=
    tensorDifferentiable.continuousMultilinear_apply_const
      (fun position => spatialCellBasis (word position))
  have composed := evaluatedDifferentiable.hasFDerivAt.comp cell
    (assembleSpatialCell_cell_hasFDerivAt point cell)
  have derivativeValue :
      ((fderiv ℝ
          (fun ambient => mixedCartesianDerivative order word
            (diskCellLift field.value) ambient)
          (assembleSpatialCell point cell)).comp fp17CellEmbeddingCLM) 1 =
        mixedCartesianDerivative (order + 1) (prependCellCoordinate word)
          (diskCellLift field.value) (assembleSpatialCell point cell) := by
    rw [ContinuousLinearMap.comp_apply, fp17CellEmbeddingCLM_one]
    have successor := tensorDifferentiable.iteratedFDeriv_succ_apply_left'
      (m := Fin.cons (spatialCellBasis 2)
        (fun position => spatialCellBasis (word position)))
    exact successor.symm
  exact composed.hasDerivAt.congr_deriv derivativeValue

private theorem closedMixedDerivative_assembleSpatialCell
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) (cell : ℝ) :
    closedMixedDerivative field order word
        (ambientClosedDisk point, (cell : CellCircle)) =
      mixedCartesianDerivative order word (diskCellLift field.value)
        (assembleSpatialCell point cell) := by
  have cylinderMembership :
      assembleSpatialCell point cell ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point cell)‖ < 1
    simpa [openUnitDisk] using membership
  rw [← closedMixedDerivative_spec field order word _ cylinderMembership]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    change (ambientClosedDisk point).val =
      planarPart (assembleSpatialCell point cell)
    rw [planarPart_assembleSpatialCell,
      ambientClosedDisk_val_of_mem
        (openDiskMembershipClosed point membership)]
  · rfl

private theorem closedMixedDerivative_cell_hasDerivAt
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) (cell : ℝ) :
    HasDerivAt
      (fun candidate : ℝ => closedMixedDerivative field order word
        (ambientClosedDisk point, (candidate : CellCircle)))
      (closedMixedDerivative field (order + 1) (prependCellCoordinate word)
        (ambientClosedDisk point, (cell : CellCircle))) cell := by
  have actual := actualMixedDerivative_cell_hasDerivAt field word point
    membership cell
  convert actual using 1
  · funext candidate
    exact closedMixedDerivative_assembleSpatialCell field word point membership
      candidate
  · exact (closedMixedDerivative_assembleSpatialCell field
      (prependCellCoordinate word) point membership cell)

/-- One integration by parts in the actual periodic cell variable.  This is
proved first on the open disk; continuity will extend it to the closed disk. -/
private theorem fourierCoeff_closedMixedDerivative_cell_open
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) (point : SpatialPlane)
    (membership : point ∈ openUnitDisk) :
    fourierCoeff (T := 2 * Real.pi)
        (fun circle : CellCircle =>
          closedMixedDerivative field (order + 1) (prependCellCoordinate word)
            (ambientClosedDisk point, circle)) cell =
      (Complex.I * (cell : ℂ)) •
        fourierCoeff (T := 2 * Real.pi)
          (fun circle : CellCircle =>
            closedMixedDerivative field order word
              (ambientClosedDisk point, circle)) cell := by
  let oldValue : ℝ → ComplexEuclidean dimension := fun coordinate =>
    closedMixedDerivative field order word
      (ambientClosedDisk point, (coordinate : CellCircle))
  let newValue : ℝ → ComplexEuclidean dimension := fun coordinate =>
    closedMixedDerivative field (order + 1) (prependCellCoordinate word)
      (ambientClosedDisk point, (coordinate : CellCircle))
  let character : ℝ → ℂ := fun coordinate =>
    fourier (-cell) (coordinate : CellCircle)
  let characterDerivative : ℝ → ℂ := fun coordinate =>
    (-2 * Real.pi * Complex.I * (cell : ℂ) / (2 * Real.pi)) *
      character coordinate
  have oldDerivative : ∀ coordinate : ℝ,
      HasDerivAt oldValue (newValue coordinate) coordinate := by
    intro coordinate
    exact closedMixedDerivative_cell_hasDerivAt field word point membership
      coordinate
  have characterHasDerivative : ∀ coordinate : ℝ,
      HasDerivAt character (characterDerivative coordinate) coordinate := by
    intro coordinate
    simpa [character, characterDerivative] using
      (hasDerivAt_fourier_neg (2 * Real.pi) cell coordinate)
  have oldContinuous : Continuous oldValue :=
    (closedMixedDerivative field order word).continuous.comp
      (continuous_const.prodMk
        (AddCircle.continuous_mk' (2 * Real.pi)))
  have newContinuous : Continuous newValue :=
    (closedMixedDerivative field (order + 1)
      (prependCellCoordinate word)).continuous.comp
        (continuous_const.prodMk
          (AddCircle.continuous_mk' (2 * Real.pi)))
  have characterContinuous : Continuous character :=
    (fourier (-cell)).continuous.comp
      (AddCircle.continuous_mk' (2 * Real.pi))
  have characterDerivativeContinuous : Continuous characterDerivative := by
    dsimp [characterDerivative]
    fun_prop
  have parts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := 0) (b := 2 * Real.pi)
    (fun coordinate _ => characterHasDerivative coordinate)
    (fun coordinate _ => oldDerivative coordinate)
    (characterDerivativeContinuous.intervalIntegrable _ _)
    (newContinuous.intervalIntegrable _ _)
  have endpointCircle :
      ((2 * Real.pi : ℝ) : CellCircle) = ((0 : ℝ) : CellCircle) := by
    simpa only [zero_add] using
      AddCircle.coe_add_period (2 * Real.pi) (0 : ℝ)
  have integralIdentity :
      (∫ coordinate in (0 : ℝ)..2 * Real.pi,
          character coordinate • newValue coordinate) =
        (Complex.I * (cell : ℂ)) •
          (∫ coordinate in (0 : ℝ)..2 * Real.pi,
            character coordinate • oldValue coordinate) := by
    have oldEndpoint : oldValue (2 * Real.pi) = oldValue 0 := by
      simp only [oldValue, endpointCircle]
    have characterEndpoint : character (2 * Real.pi) = character 0 := by
      simp only [character, endpointCircle]
    rw [oldEndpoint, characterEndpoint] at parts
    have scalarIdentity :
        (-2 * Real.pi * Complex.I * (cell : ℂ) / (2 * Real.pi)) =
          -(Complex.I * (cell : ℂ)) := by
      field_simp [Real.pi_ne_zero]
    simp only [sub_self, zero_sub] at parts
    have characterDerivativeIdentity : characterDerivative = fun coordinate =>
        -(Complex.I * (cell : ℂ)) * character coordinate := by
      funext coordinate
      simp only [characterDerivative, scalarIdentity]
    rw [characterDerivativeIdentity] at parts
    have integralCharacterDerivativeIdentity :
        (∫ coordinate in (0 : ℝ)..2 * Real.pi,
        (-(Complex.I * (cell : ℂ)) * character coordinate) •
          oldValue coordinate) =
        -(Complex.I * (cell : ℂ)) •
          (∫ coordinate in (0 : ℝ)..2 * Real.pi,
            character coordinate • oldValue coordinate) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro coordinate _membership
      simp only [mul_smul]
    rw [integralCharacterDerivativeIdentity] at parts
    simpa only [neg_smul, neg_neg] using parts
  rw [fourierCoeff_eq_intervalIntegral _ _ 0,
    fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add]
  change (1 / (2 * Real.pi)) •
      (∫ coordinate in (0 : ℝ)..2 * Real.pi,
        character coordinate • newValue coordinate) = _
  rw [integralIdentity]
  exact smul_comm _ _ _

/-- The periodic cell integration-by-parts identity as an equality of
continuous maps on the whole closed disk. -/
theorem diskCellFourierValue_prependCell
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) :
    diskCellFourierValue
        (closedMixedDerivative field (order + 1) (prependCellCoordinate word))
        cell =
      (Complex.I * (cell : ℂ)) •
        diskCellFourierValue (closedMixedDerivative field order word) cell := by
  apply continuousMap_eq_of_openDisk
  intro point membership
  change diskCellFourierValue
      (closedMixedDerivative field (order + 1) (prependCellCoordinate word))
        cell point =
    (Complex.I * (cell : ℂ)) •
      diskCellFourierValue (closedMixedDerivative field order word) cell point
  rw [diskCellFourierValue_apply, diskCellFourierValue_apply]
  have ambientIdentity : ambientClosedDisk point.val = point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem
      (openDiskMembershipClosed point.val membership)
  simpa only [ambientIdentity] using
    (fourierCoeff_closedMixedDerivative_cell_open field word cell point.val
      membership)

/-- A mixed derivative word obtained by prepending `cellOrder` copies of the
actual cell coordinate to the prescribed word. -/
def repeatedCellDerivativeWord {order : ℕ}
    (word : MixedCartesianWord order) (cellOrder : ℕ) :
    MixedCartesianWord (order + cellOrder) := fun position =>
  if membership : position.val < cellOrder then 2 else
    word ⟨position.val - cellOrder, by omega⟩

@[simp] theorem repeatedCellDerivativeWord_zero {order : ℕ}
    (word : MixedCartesianWord order) :
    repeatedCellDerivativeWord word 0 = word := by
  funext position
  simp [repeatedCellDerivativeWord]

theorem repeatedCellDerivativeWord_succ {order : ℕ}
    (word : MixedCartesianWord order) (cellOrder : ℕ) :
    repeatedCellDerivativeWord word (cellOrder + 1) =
      prependCellCoordinate (repeatedCellDerivativeWord word cellOrder) := by
  funext position
  refine Fin.cases ?_ (fun tail => ?_) position
  · simp [repeatedCellDerivativeWord, prependCellCoordinate]
  · by_cases membership : tail.val < cellOrder
    · simp [repeatedCellDerivativeWord, prependCellCoordinate, membership]
    · simp [repeatedCellDerivativeWord, prependCellCoordinate, membership]

/-- Iterating the exact periodic identity gives the literal Fourier
multiplier `(i n)^b`. -/
theorem diskCellFourierValue_repeatedCell
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) (cellOrder : ℕ) :
    diskCellFourierValue
        (closedMixedDerivative field
          (order + cellOrder)
          (repeatedCellDerivativeWord word cellOrder)) cell =
      cellDerivativeFactor cell cellOrder •
        diskCellFourierValue (closedMixedDerivative field order word) cell := by
  induction cellOrder with
  | zero =>
      simp [cellDerivativeFactor]
  | succ cellOrder inductionHypothesis =>
      rw [repeatedCellDerivativeWord_succ]
      change diskCellFourierValue
          (closedMixedDerivative field ((order + cellOrder) + 1)
            (prependCellCoordinate
              (repeatedCellDerivativeWord word cellOrder))) cell = _
      rw [diskCellFourierValue_prependCell, inductionHypothesis]
      simp only [cellDerivativeFactor, smul_smul]
      rw [pow_succ]
      congr 1
      ring

theorem diskCellFourierFamily_norm_le {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ)
    (circle : CellCircle) :
    ‖diskCellFourierFamily value cell circle‖ ≤ ‖value‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg value)]
  intro point
  change ‖fourier (-cell) circle • value (point, circle)‖ ≤ ‖value‖
  rw [norm_smul, show ‖fourier (-cell) circle‖ = 1 by
    simpa only [cellCharacter] using cellCharacter_apply_norm (-cell) circle,
    one_mul]
  exact value.norm_coe_le_norm (point, circle)

/-- A Bochner cell Fourier coefficient is bounded by the exact uniform norm
of its continuous disk×circle source. -/
theorem diskCellFourierValue_norm_le {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension)) (cell : ℤ) :
    ‖diskCellFourierValue value cell‖ ≤ ‖value‖ := by
  unfold diskCellFourierValue
  calc
    ‖∫ circle : CellCircle, diskCellFourierFamily value cell circle
        ∂AddCircle.haarAddCircle‖ ≤
        ‖value‖ * AddCircle.haarAddCircle.real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (diskCellFourierFamily_norm_le value cell))
    _ = ‖value‖ := by simp

/-- Exact norm identity behind arbitrary-order cell Fourier decay. -/
theorem cellPower_mul_diskCellFourierValue_norm
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) (cellOrder : ℕ) :
    |(cell : ℝ)| ^ cellOrder *
        ‖diskCellFourierValue (closedMixedDerivative field order word) cell‖ =
      ‖diskCellFourierValue
        (closedMixedDerivative field
          (order + cellOrder)
          (repeatedCellDerivativeWord word cellOrder)) cell‖ := by
  rw [diskCellFourierValue_repeatedCell field word cell cellOrder,
    norm_smul, cellDerivativeFactor_norm]

/-- The exact closed-disk Fourier coefficient has arbitrary polynomial decay,
measured against an actual higher cell derivative of the input closed jet. -/
theorem cellPower_mul_diskCellFourierValue_norm_le
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (cell : ℤ) (cellOrder : ℕ) :
    |(cell : ℝ)| ^ cellOrder *
        ‖diskCellFourierValue (closedMixedDerivative field order word) cell‖ ≤
      ‖closedMixedDerivative field
        (order + cellOrder)
        (repeatedCellDerivativeWord word cellOrder)‖ := by
  rw [cellPower_mul_diskCellFourierValue_norm]
  exact diskCellFourierValue_norm_le _ _

/-- The derivative selected by the coefficient closed jet is exactly the
continuous coefficient of the corresponding actual mixed derivative. -/
theorem closedDerivative_diskCellFourierCoefficientJet
    {dimension order : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ)
    (word : CartesianWord order) :
    closedDerivative (diskCellFourierCoefficientJet field cell) order word =
      diskCellFourierDerivativeExtension field cell word := by
  symm
  apply cartesianExtension_unique
  exact diskCellFourierDerivativeExtension_spec field cell word

theorem closedMultiDerivative_diskCellFourierCoefficientJet
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ)
    (index : CartesianMultiIndex) :
    closedMultiDerivative (diskCellFourierCoefficientJet field cell) index =
      diskCellFourierDerivativeExtension field cell
        (cartesianMultiIndexWord index) := by
  exact closedDerivative_diskCellFourierCoefficientJet field cell
    (cartesianMultiIndexWord index)

/-- Passing a continuous closed-disk field to its literal disk `L²`
representative costs only the finite disk measure. -/
theorem closedContinuousToDiskL2_norm_sq_le {dimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 field‖ ^ 2 ≤
      (volume.restrict openUnitDisk).real Set.univ * ‖field‖ ^ 2 := by
  rw [closedContinuousToDiskL2_norm_sq]
  have fieldIntegrable : Integrable (fun point : SpatialPlane =>
      ‖closedDiskLift field point‖ ^ 2)
      (volume.restrict openUnitDisk) := by
    exact (memLp_two_iff_integrable_sq_norm
      (closedContinuous_memLp field).1).mp (closedContinuous_memLp field)
  have constantIntegrable : Integrable (fun _point : SpatialPlane =>
      ‖field‖ ^ 2) (volume.restrict openUnitDisk) := integrable_const _
  calc
    (∫ point : SpatialPlane, ‖closedDiskLift field point‖ ^ 2
        ∂volume.restrict openUnitDisk) ≤
        ∫ _point : SpatialPlane, ‖field‖ ^ 2
          ∂volume.restrict openUnitDisk := by
      apply integral_mono_ae fieldIntegrable constantIntegrable
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet]
        with point membership
      have valueBound :
          ‖closedDiskLift field point‖ ≤ ‖field‖ := by
        rw [closedDiskLift, dif_pos
          (openDiskMembershipClosed point membership)]
        exact field.norm_coe_le_norm _
      gcongr
    _ = (volume.restrict openUnitDisk).real Set.univ * ‖field‖ ^ 2 := by
      rw [integral_const]
      rfl

/-- An exact one-dimensional comparison: arbitrary `|n|^(k+1)` decay
implies square summability with the literal inhomogeneous cell frequency. -/
theorem cellFrequency_weighted_sq_summable_of_decay
    {Value : Type*} [NormedAddCommGroup Value]
    (values : ℤ → Value) (weightOrder : ℕ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (decay : ∀ cell : ℤ, cell ≠ 0 →
      |(cell : ℝ)| ^ (weightOrder + 1) * ‖values cell‖ ≤ bound) :
    Summable (fun cell : ℤ =>
      cellFrequency cell ^ (2 * weightOrder) * ‖values cell‖ ^ 2) := by
  let zeroTerm := cellFrequency 0 ^ (2 * weightOrder) * ‖values 0‖ ^ 2
  let scale := ((2 : ℝ) ^ (weightOrder + 1) * bound) ^ 2
  let majorant : ℤ → ℝ := fun cell =>
    (zeroTerm + scale) * Grad.FourierGrade.integerSquareDecay cell
  have zeroTermNonnegative : 0 ≤ zeroTerm := by
    dsimp [zeroTerm]
    exact mul_nonneg (pow_nonneg (cellFrequency_pos 0).le _)
      (sq_nonneg ‖values 0‖)
  have scaleNonnegative : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have majorantSummable : Summable majorant := by
    exact Grad.FourierGrade.integerSquareDecay_summable.mul_left
      (zeroTerm + scale)
  apply Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _)
      (sq_nonneg ‖values cell‖)) _ majorantSummable
  intro cell
  by_cases cellZero : cell = 0
  · subst cell
    have decayAtZero : Grad.FourierGrade.integerSquareDecay 0 = 1 := by
      norm_num [Grad.FourierGrade.integerSquareDecay]
    change zeroTerm ≤ majorant 0
    rw [show majorant 0 = (zeroTerm + scale) *
        Grad.FourierGrade.integerSquareDecay 0 by rfl, decayAtZero, mul_one]
    exact le_add_of_nonneg_right scaleNonnegative
  · have integerAbsOne : (1 : ℝ) ≤ |(cell : ℝ)| := by
      exact_mod_cast Int.one_le_abs cellZero
    have frequencySquare : cellFrequency cell ^ 2 =
        1 + |(cell : ℝ)| ^ 2 := by
      rw [cellFrequency_formula, Real.sq_sqrt]
      · rw [sq_abs]
      · positivity
    have frequencyUpper :
        cellFrequency cell ≤ 2 * |(cell : ℝ)| := by
      have frequencyNonnegative := (cellFrequency_pos cell).le
      have absNonnegative := abs_nonneg (cell : ℝ)
      nlinarith [sq_nonneg |(cell : ℝ)|]
    have weightedDecay :
        cellFrequency cell ^ (weightOrder + 1) * ‖values cell‖ ≤
          (2 : ℝ) ^ (weightOrder + 1) * bound := by
      calc
        cellFrequency cell ^ (weightOrder + 1) * ‖values cell‖ ≤
            (2 * |(cell : ℝ)|) ^ (weightOrder + 1) *
              ‖values cell‖ := by
          gcongr
          exact (cellFrequency_pos cell).le
        _ = (2 : ℝ) ^ (weightOrder + 1) *
              (|(cell : ℝ)| ^ (weightOrder + 1) * ‖values cell‖) := by
          rw [mul_pow]
          ring
        _ ≤ (2 : ℝ) ^ (weightOrder + 1) * bound := by
          exact mul_le_mul_of_nonneg_left (decay cell cellZero)
            (pow_nonneg (by norm_num) _)
    have squareBound :
        (cellFrequency cell ^ (weightOrder + 1) * ‖values cell‖) ^ 2 ≤
          scale := by
      dsimp [scale]
      have leftNonnegative :
          0 ≤ cellFrequency cell ^ (weightOrder + 1) * ‖values cell‖ :=
        mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)
      have rightNonnegative :
          0 ≤ (2 : ℝ) ^ (weightOrder + 1) * bound :=
        mul_nonneg (pow_nonneg (by norm_num) _) boundNonnegative
      nlinarith [mul_nonneg (sub_nonneg.mpr weightedDecay)
        (add_nonneg rightNonnegative leftNonnegative)]
    have frequencyDecayIdentity :
        Grad.FourierGrade.integerSquareDecay cell =
          (cellFrequency cell ^ 2)⁻¹ := by
      rw [Grad.FourierGrade.integerSquareDecay, cellFrequency_formula]
      have radicandNonnegative : 0 ≤ 1 + (cell : ℝ) ^ 2 := by
        positivity
      rw [Real.sq_sqrt radicandNonnegative]
    have mainBound :
        cellFrequency cell ^ (2 * weightOrder) * ‖values cell‖ ^ 2 ≤
          scale * Grad.FourierGrade.integerSquareDecay cell := by
      rw [frequencyDecayIdentity]
      apply (le_mul_inv_iff₀ (sq_pos_of_pos (cellFrequency_pos cell))).2
      calc
        cellFrequency cell ^ (2 * weightOrder) * ‖values cell‖ ^ 2 *
              cellFrequency cell ^ 2 =
            (cellFrequency cell ^ (weightOrder + 1) * ‖values cell‖) ^ 2 := by
          ring
        _ ≤ scale := squareBound
    change cellFrequency cell ^ (2 * weightOrder) * ‖values cell‖ ^ 2 ≤
      (zeroTerm + scale) * Grad.FourierGrade.integerSquareDecay cell
    calc
      cellFrequency cell ^ (2 * weightOrder) * ‖values cell‖ ^ 2 ≤
          scale * Grad.FourierGrade.integerSquareDecay cell := mainBound
      _ ≤ (zeroTerm + scale) *
          Grad.FourierGrade.integerSquareDecay cell := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zeroTermNonnegative)
          (Grad.FourierGrade.integerSquareDecay_nonneg cell)

/-- Every requested planar Fourier-coefficient extension decays rapidly in
the exact uniform closed-disk norm. -/
theorem diskCellFourierDerivativeExtension_weighted_sq_summable
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : CartesianWord order) (weightOrder : ℕ) :
    Summable (fun cell : ℤ =>
      cellFrequency cell ^ (2 * weightOrder) *
        ‖diskCellFourierDerivativeExtension field cell word‖ ^ 2) := by
  let derivativeWord := repeatedCellDerivativeWord
    (fp17LiftPlanarWord word) (weightOrder + 1)
  let bound := ‖closedMixedDerivative field (order + (weightOrder + 1))
    derivativeWord‖
  apply cellFrequency_weighted_sq_summable_of_decay
    (fun cell : ℤ => diskCellFourierDerivativeExtension field cell word)
    weightOrder bound (norm_nonneg _)
  intro cell cellNonzero
  change |(cell : ℝ)| ^ (weightOrder + 1) *
      ‖diskCellFourierValue
        (closedMixedDerivative field order (fp17LiftPlanarWord word)) cell‖ ≤
    bound
  exact cellPower_mul_diskCellFourierValue_norm_le field
    (fp17LiftPlanarWord word) cell (weightOrder + 1)

/-- Rapid closed-disk decay implies the exact weighted `L²(D)` coefficient
summability used by every ordinary Cartesian grade. -/
theorem diskCellFourierDerivativeL2_weighted_sq_summable
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : CartesianWord order) (weightOrder : ℕ) :
    Summable (fun cell : ℤ =>
      cellFrequency cell ^ (2 * weightOrder) *
        ‖closedContinuousToDiskL2
          (diskCellFourierDerivativeExtension field cell word)‖ ^ 2) := by
  let diskMass := (volume.restrict openUnitDisk).real Set.univ
  have diskMassNonnegative : 0 ≤ diskMass := by
    dsimp [diskMass]
    exact ENNReal.toReal_nonneg
  have uniformSummable :=
    diskCellFourierDerivativeExtension_weighted_sq_summable field word
      weightOrder
  have majorantSummable : Summable (fun cell : ℤ =>
      diskMass * (cellFrequency cell ^ (2 * weightOrder) *
        ‖diskCellFourierDerivativeExtension field cell word‖ ^ 2)) :=
    uniformSummable.mul_left diskMass
  apply Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _)
      (sq_nonneg _)) _ majorantSummable
  intro cell
  have l2Bound := closedContinuousToDiskL2_norm_sq_le
    (diskCellFourierDerivativeExtension field cell word)
  change cellFrequency cell ^ (2 * weightOrder) *
      ‖closedContinuousToDiskL2
        (diskCellFourierDerivativeExtension field cell word)‖ ^ 2 ≤
    diskMass * (cellFrequency cell ^ (2 * weightOrder) *
      ‖diskCellFourierDerivativeExtension field cell word‖ ^ 2)
  calc
    cellFrequency cell ^ (2 * weightOrder) *
          ‖closedContinuousToDiskL2
            (diskCellFourierDerivativeExtension field cell word)‖ ^ 2 ≤
        cellFrequency cell ^ (2 * weightOrder) *
          (diskMass *
            ‖diskCellFourierDerivativeExtension field cell word‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left l2Bound
        (pow_nonneg (cellFrequency_pos cell).le _)
    _ = diskMass * (cellFrequency cell ^ (2 * weightOrder) *
          ‖diskCellFourierDerivativeExtension field cell word‖ ^ 2) := by
      ring

theorem ordinaryFourierCoefficient_gradeCoordinate_summable
    {dimension grade : ℕ} (field : DiskCellClosedJet dimension)
    (index : GradeMultiIndex grade) :
    Summable (fun cell : ℤ =>
      ‖ordinaryRawGradeCoordinates grade
        (fun mode => diskCellFourierCoefficientJet field mode) cell index‖ ^ 2) := by
  let weightOrder := grade - cartesianOrder index.toCartesian
  have source := diskCellFourierDerivativeL2_weighted_sq_summable field
    (cartesianMultiIndexWord index.toCartesian) weightOrder
  apply source.congr
  intro cell
  rw [show ordinaryRawGradeCoordinates grade
      (fun mode => diskCellFourierCoefficientJet field mode) cell index =
        (cellFrequency cell : ℂ) ^ weightOrder •
          closedContinuousToDiskL2
            (closedMultiDerivative
              (diskCellFourierCoefficientJet field cell)
              index.toCartesian) by rfl,
    closedMultiDerivative_diskCellFourierCoefficientJet,
    norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell)]
  ring

/-- The actual cell Fourier coefficients of every ordinary disk-cell closed
jet lie in every literal phase-zero Cartesian grade. -/
theorem ordinaryFourierCoefficient_mem_all_grades
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    Memℓp (ordinaryRawGradeCoordinates grade
      (fun cell => diskCellFourierCoefficientJet field cell)) 2 := by
  apply (memlp_iff_summable_sq _).2
  have eachCoordinate : ∀ index : GradeMultiIndex grade,
      Summable (fun cell : ℤ =>
        ‖ordinaryRawGradeCoordinates grade
          (fun mode => diskCellFourierCoefficientJet field mode) cell index‖ ^ 2) :=
    ordinaryFourierCoefficient_gradeCoordinate_summable field
  have finiteCoordinateSum : ∀ indices : Finset (GradeMultiIndex grade),
      Summable (fun cell : ℤ => ∑ index ∈ indices,
        ‖ordinaryRawGradeCoordinates grade
          (fun mode => diskCellFourierCoefficientJet field mode) cell index‖ ^ 2) := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices fresh inductionHypothesis =>
        simpa [Finset.sum_insert, fresh] using
          (eachCoordinate index).add inductionHypothesis
  have allCoordinates := finiteCoordinateSum Finset.univ
  apply allCoordinates.congr
  intro cell
  exact (PiLp.norm_sq_eq_of_L2
    (fun _ : GradeMultiIndex grade => DiskL2 dimension)
    (ordinaryRawGradeCoordinates grade
      (fun mode => diskCellFourierCoefficientJet field mode) cell)).symm

/-- Fourier integration maps an arbitrary ordinary disk-cell closed jet into
the literal all-grade phase-zero coefficient core. -/
def ordinaryFourierCoefficientCore {dimension : ℕ}
    (field : DiskCellClosedJet dimension) : OrdinaryCoefficientCore dimension :=
  ⟨fun cell => diskCellFourierCoefficientJet field cell,
    ordinaryFourierCoefficient_mem_all_grades field⟩

@[simp] theorem ordinaryFourierCoefficientCore_apply
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (cell : ℤ) :
    (ordinaryFourierCoefficientCore field).1 cell =
      diskCellFourierCoefficientJet field cell := rfl

/-- Fourier integration recovers every prescribed coefficient closed jet of
the uniform all-derivative reconstruction. -/
theorem diskCellFourierCoefficientJet_ordinaryReconstructedClosedJet
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (cell : ℤ) :
    diskCellFourierCoefficientJet
        (ordinaryReconstructedClosedJet coefficients) cell =
      coefficients.1 cell := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [diskCellFourierCoefficientJet_value,
    diskCellFourierValue_apply]
  exact fourierCoeff_ordinaryReconstructedValue coefficients point cell

theorem ordinaryFourierCoefficientCore_reconstruction_left
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension) :
    ordinaryFourierCoefficientCore
        (ordinaryReconstructedClosedJet coefficients) = coefficients := by
  apply Subtype.ext
  funext cell
  exact diskCellFourierCoefficientJet_ordinaryReconstructedClosedJet
    coefficients cell

/-- One scalar value coordinate of a disk-cell closed jet on a fixed disk
fibre, bundled as a continuous cell-circle function. -/
def diskCellComponent {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : ClosedDisk) (coordinate : Fin dimension) : C(CellCircle, ℂ) where
  toFun circle := field.value (point, circle) coordinate
  continuous_toFun := by fun_prop

theorem diskCellComponent_fourierCoeff
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : ClosedDisk) (coordinate : Fin dimension) (cell : ℤ) :
    fourierCoeff (T := 2 * Real.pi)
        (diskCellComponent field point coordinate) cell =
      (diskCellFourierCoefficientJet field cell).value point coordinate := by
  rw [diskCellFourierCoefficientJet_value,
    diskCellFourierValue_apply]
  unfold fourierCoeff
  have integrableCoordinates : ∀ index : Fin dimension,
      Integrable (fun circle : CellCircle =>
        (fourier (-cell) circle • field.value (point, circle)) index)
        AddCircle.haarAddCircle := by
    intro index
    have continuousIntegrand : Continuous (fun circle : CellCircle =>
        (fourier (-cell) circle • field.value (point, circle)) index) := by
      fun_prop
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        continuousIntegrand.continuousOn)
  rw [MeasureTheory.eval_integral_piLp integrableCoordinates coordinate]
  rfl

theorem diskCellComponent_fourierCoeff_summable
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : ClosedDisk) (coordinate : Fin dimension) :
    Summable (fourierCoeff (T := 2 * Real.pi)
      (diskCellComponent field point coordinate)) := by
  let coefficients := ordinaryFourierCoefficientCore field
  have coefficientSupNorms : Summable (fun cell : ℤ =>
      ‖(coefficients.1 cell).value‖) := by
    simpa [closedDerivative_zero_order] using
      physicalDerivative_series_summable coefficients
        emptyCartesianWord 0
  have componentNorms : Summable (fun cell : ℤ =>
      ‖fourierCoeff (T := 2 * Real.pi)
        (diskCellComponent field point coordinate) cell‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ coefficientSupNorms
    intro cell
    rw [diskCellComponent_fourierCoeff]
    calc
      ‖(diskCellFourierCoefficientJet field cell).value point coordinate‖ ≤
          ‖(diskCellFourierCoefficientJet field cell).value point‖ :=
        PiLp.norm_apply_le _ coordinate
      _ ≤ ‖(diskCellFourierCoefficientJet field cell).value‖ :=
        (diskCellFourierCoefficientJet field cell).value.norm_coe_le_norm point
      _ = ‖(coefficients.1 cell).value‖ := rfl
  exact componentNorms.of_norm

/-- Fourier synthesis of the actual coefficient core returns the original
continuous disk×circle value, coordinatewise by scalar Fourier inversion. -/
theorem ordinaryReconstructedValue_ordinaryFourierCoefficientCore
    {dimension : ℕ} (field : DiskCellClosedJet dimension) :
    ordinaryReconstructedValue (ordinaryFourierCoefficientCore field) =
      field.value := by
  apply ContinuousMap.ext
  rintro ⟨point, circle⟩
  apply PiLp.ext
  intro coordinate
  rw [ordinaryReconstructedValue_apply]
  let coefficients := ordinaryFourierCoefficientCore field
  have coefficientSupNorms : Summable (fun cell : ℤ =>
      ‖(coefficients.1 cell).value‖) := by
    simpa [closedDerivative_zero_order] using
      physicalDerivative_series_summable coefficients
        emptyCartesianWord 0
  have vectorSeriesSummable : Summable (fun cell : ℤ =>
      cellCharacter cell circle • (coefficients.1 cell).value point) := by
    apply Summable.of_norm_bounded coefficientSupNorms
    intro cell
    rw [norm_smul, cellCharacter_apply_norm, one_mul]
    exact (coefficients.1 cell).value.norm_coe_le_norm point
  let projection : ComplexEuclidean dimension →L[ℂ] ℂ :=
    PiLp.proj 2 (fun _ : Fin dimension => ℂ) coordinate
  have projected := projection.map_tsum vectorSeriesSummable
  change (∑' cell : ℤ,
      cellCharacter cell circle • (coefficients.1 cell).value point) coordinate =
    field.value (point, circle) coordinate
  rw [show (∑' cell : ℤ,
        cellCharacter cell circle • (coefficients.1 cell).value point) coordinate =
      ∑' cell : ℤ,
        (cellCharacter cell circle •
          (coefficients.1 cell).value point) coordinate by
    exact projected]
  have scalarSeries := has_pointwise_sum_fourier_series_of_summable
    (diskCellComponent_fourierCoeff_summable field point coordinate) circle
  have scalarTsum := scalarSeries.tsum_eq
  have component_apply :
      diskCellComponent field point coordinate circle =
        field.value (point, circle) coordinate := rfl
  rw [component_apply] at scalarTsum
  have scalarTsum' : (∑' cell : ℤ,
      fourierCoeff (T := 2 * Real.pi)
        (diskCellComponent field point coordinate) cell *
          fourier cell circle) =
      field.value (point, circle) coordinate := by
    simpa only [smul_eq_mul] using scalarTsum
  simpa only [coefficients, ordinaryFourierCoefficientCore_apply,
    ← diskCellComponent_fourierCoeff field point coordinate,
    PiLp.smul_apply, smul_eq_mul, cellCharacter, mul_comm] using scalarTsum'

/-- The inverse Fourier core reconstructs the entire closed jet, since the
closed-jet carrier is determined by its continuous value. -/
theorem ordinaryReconstructedClosedJet_fourierCoefficientCore
    {dimension : ℕ} (field : DiskCellClosedJet dimension) :
    ordinaryReconstructedClosedJet (ordinaryFourierCoefficientCore field) =
      field := by
  apply diskCellClosedJet_eq_of_value_eq
  exact ordinaryReconstructedValue_ordinaryFourierCoefficientCore field

end Grad.CartesianState
