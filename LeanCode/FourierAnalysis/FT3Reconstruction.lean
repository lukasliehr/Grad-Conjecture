import FT2Sobolev
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff

universe valueUniverse

namespace Grad.FourierGrade

/- The product-torus Fourier theorems use probability Haar measure.  Repeat
the same local instances here so reconstruction and coefficient recovery use
the identical normalization. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The one-dimensional summable comparison weight used in the three-dimensional
Fourier reconstruction. -/
def integerSquareDecay (index : ℤ) : ℝ :=
  (1 + (index : ℝ) ^ 2)⁻¹

theorem integerSquareDecay_nonneg (index : ℤ) : 0 ≤ integerSquareDecay index := by
  unfold integerSquareDecay
  positivity

theorem integerSquareDecay_summable : Summable integerSquareDecay := by
  have punctured : Summable (fun index : ℤ => 1 / (index : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have patched : Summable (fun index : ℤ =>
      if index = 0 then 1 else ((index : ℝ) ^ 2)⁻¹) := by
    apply punctured.congr_cofinite
    have awayFromZero : ∀ᶠ index : ℤ in Filter.cofinite, index ≠ 0 := by
      apply Filter.eventually_cofinite.mpr
      simp
    filter_upwards [awayFromZero] with index nonzero
    simp [nonzero, one_div]
  apply Summable.of_nonneg_of_le integerSquareDecay_nonneg _ patched
  intro index
  by_cases zero : index = 0
  · simp [integerSquareDecay, zero]
  · have castNonzero : (index : ℝ) ≠ 0 := by exact_mod_cast zero
    have castSquarePositive : 0 < (index : ℝ) ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr castNonzero
    simp only [if_neg zero]
    exact (inv_le_inv₀ (by positivity : 0 < 1 + (index : ℝ) ^ 2)
      castSquarePositive).mpr (by linarith)

/-- Product comparison weight on the literal nested triple `ℤ³`. -/
def latticeDecay (mode : FourierMode) : ℝ :=
  integerSquareDecay mode.1 *
    (integerSquareDecay mode.2.1 * integerSquareDecay mode.2.2)

theorem latticeDecay_nonneg (mode : FourierMode) : 0 ≤ latticeDecay mode := by
  unfold latticeDecay
  exact mul_nonneg (integerSquareDecay_nonneg mode.1)
    (mul_nonneg (integerSquareDecay_nonneg mode.2.1)
      (integerSquareDecay_nonneg mode.2.2))

theorem latticeDecay_summable : Summable latticeDecay := by
  change Summable (fun mode : ℤ × (ℤ × ℤ) =>
    integerSquareDecay mode.1 *
      (integerSquareDecay mode.2.1 * integerSquareDecay mode.2.2))
  simpa only using
    integerSquareDecay_summable.mul_of_nonneg
      (integerSquareDecay_summable.mul_of_nonneg integerSquareDecay_summable
        integerSquareDecay_nonneg integerSquareDecay_nonneg)
      integerSquareDecay_nonneg
      (fun pair : ℤ × ℤ => mul_nonneg
        (integerSquareDecay_nonneg pair.1) (integerSquareDecay_nonneg pair.2))

/-- The fixed six-order decay reserve.  Its summability is exactly the
three-dimensional shell-count input needed for uniform reconstruction. -/
def inverseSixWeight (mode : FourierMode) : ℝ :=
  (frequencyWeight mode ^ 6)⁻¹

theorem integerFactor_first_le_weight_sq (mode : FourierMode) :
    1 + (mode.1 : ℝ) ^ 2 ≤ frequencyWeight mode ^ 2 := by
  have scale : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  have absolute : |(mode.1 : ℝ)| ≤ |frequencyVector mode 0| := by
    calc
      |(mode.1 : ℝ)| = 1 * |(mode.1 : ℝ)| := by rw [one_mul]
      _ ≤ (Real.pi / 2) * |(mode.1 : ℝ)| :=
        mul_le_mul_of_nonneg_right scale (abs_nonneg _)
      _ = |frequencyVector mode 0| := by
        rw [frequencyVector_zero, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
  have square := pow_le_pow_left₀ (abs_nonneg _) absolute 2
  rw [frequencyWeight_sq_expanded]
  have secondNonnegative := sq_nonneg |frequencyVector mode 1|
  have cellNonnegative := sq_nonneg |frequencyVector mode 2|
  simp only [coordinateSquare, sq_abs]
  simp only [sq_abs] at square
  nlinarith

theorem integerFactor_second_le_weight_sq (mode : FourierMode) :
    1 + (mode.2.1 : ℝ) ^ 2 ≤ frequencyWeight mode ^ 2 := by
  have scale : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  have absolute : |(mode.2.1 : ℝ)| ≤ |frequencyVector mode 1| := by
    calc
      |(mode.2.1 : ℝ)| = 1 * |(mode.2.1 : ℝ)| := by rw [one_mul]
      _ ≤ (Real.pi / 2) * |(mode.2.1 : ℝ)| :=
        mul_le_mul_of_nonneg_right scale (abs_nonneg _)
      _ = |frequencyVector mode 1| := by
        rw [frequencyVector_one, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
  have square := pow_le_pow_left₀ (abs_nonneg _) absolute 2
  rw [frequencyWeight_sq_expanded]
  have firstNonnegative := sq_nonneg |frequencyVector mode 0|
  have cellNonnegative := sq_nonneg |frequencyVector mode 2|
  simp only [coordinateSquare, sq_abs]
  simp only [sq_abs] at square
  nlinarith

theorem integerFactor_cell_le_weight_sq (mode : FourierMode) :
    1 + (mode.2.2 : ℝ) ^ 2 ≤ frequencyWeight mode ^ 2 := by
  rw [frequencyWeight_sq_expanded]
  have firstNonnegative := sq_nonneg |frequencyVector mode 0|
  have secondNonnegative := sq_nonneg |frequencyVector mode 1|
  simp only [coordinateSquare, frequencyVector_two, sq_abs]
  nlinarith

theorem inverseSixWeight_le_latticeDecay (mode : FourierMode) :
    inverseSixWeight mode ≤ latticeDecay mode := by
  let first : ℝ := 1 + (mode.1 : ℝ) ^ 2
  let second : ℝ := 1 + (mode.2.1 : ℝ) ^ 2
  let cell : ℝ := 1 + (mode.2.2 : ℝ) ^ 2
  have firstPositive : 0 < first := by dsimp [first]; positivity
  have secondPositive : 0 < second := by dsimp [second]; positivity
  have cellPositive : 0 < cell := by dsimp [cell]; positivity
  have productPositive : 0 < first * (second * cell) := by positivity
  have productBound : first * (second * cell) ≤ frequencyWeight mode ^ 6 := by
    calc
      first * (second * cell) ≤
          frequencyWeight mode ^ 2 *
            (frequencyWeight mode ^ 2 * frequencyWeight mode ^ 2) := by
        exact mul_le_mul (integerFactor_first_le_weight_sq mode)
          (mul_le_mul (integerFactor_second_le_weight_sq mode)
            (integerFactor_cell_le_weight_sq mode) cellPositive.le
            (sq_nonneg (frequencyWeight mode)))
          (mul_nonneg secondPositive.le cellPositive.le)
          (sq_nonneg (frequencyWeight mode))
      _ = frequencyWeight mode ^ 6 := by ring
  have inverseBound : (frequencyWeight mode ^ 6)⁻¹ ≤ (first * (second * cell))⁻¹ :=
    (inv_le_inv₀ (pow_pos (frequencyWeight_pos mode) 6) productPositive).mpr productBound
  calc
    inverseSixWeight mode = (frequencyWeight mode ^ 6)⁻¹ := rfl
    _ ≤ (first * (second * cell))⁻¹ := inverseBound
    _ = latticeDecay mode := by
      simp [latticeDecay, integerSquareDecay, first, second, cell, mul_inv_rev,
        mul_comm]

theorem inverseSixWeight_summable : Summable inverseSixWeight := by
  exact Summable.of_nonneg_of_le (fun mode => by
      unfold inverseSixWeight
      positivity)
    inverseSixWeight_le_latticeDecay latticeDecay_summable

theorem inverseSixWeight_le_one (mode : FourierMode) : inverseSixWeight mode ≤ 1 := by
  unfold inverseSixWeight
  have powerOne : (1 : ℝ) ≤ frequencyWeight mode ^ 6 :=
    one_le_pow₀ (frequencyWeight_one_le mode)
  simpa using (inv_le_one₀ (pow_pos (frequencyWeight_pos mode) 6)).mpr powerOne

theorem inverseSixWeight_sq_summable :
    Summable (fun mode : FourierMode => inverseSixWeight mode ^ 2) := by
  apply Summable.of_nonneg_of_le (fun mode => sq_nonneg _) _ inverseSixWeight_summable
  intro mode
  have nonnegative : 0 ≤ inverseSixWeight mode := by
    unfold inverseSixWeight
    positivity
  nlinarith [inverseSixWeight_le_one mode]

/-- Every polynomially weighted coefficient norm is absolutely summable once
all integer `J_q` grades are finite. -/
theorem weighted_norm_summable_of_all_grades
    {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (values : FourierMode → Value)
    (allGrades : ∀ grade : ℕ, Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2))
    (order : ℕ) :
    Summable (fun mode : FourierMode => frequencyWeight mode ^ order * ‖values mode‖) := by
  let weighted : FourierMode → ℝ := fun mode =>
    frequencyWeight mode ^ (order + 6) * ‖values mode‖
  have weightedSquare : Summable (fun mode : FourierMode => weighted mode ^ 2) := by
    apply (allGrades (order + 6)).congr
    intro mode
    dsimp [weighted]
    symm
    rw [mul_pow, ← pow_mul]
    congr 2
    omega
  have weightedRpowSquare : Summable (fun mode : FourierMode =>
      weighted mode ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using weightedSquare
  have inverseRpowSquare : Summable (fun mode : FourierMode =>
      inverseSixWeight mode ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using inverseSixWeight_sq_summable
  have productSummable : Summable (fun mode : FourierMode =>
      weighted mode * inverseSixWeight mode) := by
    exact Real.summable_mul_of_Lp_Lq_of_nonneg
      (show (2 : ℝ).HolderConjugate 2 by
        rw [Real.holderConjugate_iff]
        norm_num)
      (fun mode => mul_nonneg
        (pow_nonneg (frequencyWeight_pos mode).le _) (norm_nonneg _))
      (fun mode => inv_nonneg.mpr (pow_nonneg (frequencyWeight_pos mode).le _))
      weightedRpowSquare inverseRpowSquare
  apply productSummable.congr
  intro mode
  dsimp [weighted]
  unfold inverseSixWeight
  have sixthPowerNonzero : frequencyWeight mode ^ 6 ≠ 0 :=
    pow_ne_zero 6 (frequencyWeight_ne_zero mode)
  rw [pow_add]
  calc
    (frequencyWeight mode ^ order * frequencyWeight mode ^ 6 * ‖values mode‖) *
          (frequencyWeight mode ^ 6)⁻¹ =
        (frequencyWeight mode ^ order * ‖values mode‖) *
          (frequencyWeight mode ^ 6 * (frequencyWeight mode ^ 6)⁻¹) := by ring
    _ = frequencyWeight mode ^ order * ‖values mode‖ := by
      rw [mul_inv_cancel₀ sixthPowerNonzero, mul_one]

/-- The literal unweighted coefficients of an all-grade core have every
polynomially weighted square norm summable. -/
theorem core_grade_energy_summable
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (values : JCore Value) (grade : ℕ) :
    Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖values.1 mode‖ ^ 2) := by
  have fromGrade := gradeCoefficientEnergy_summable grade (coreToGrade grade values)
  apply fromGrade.congr
  intro mode
  rw [coreToGrade_coefficient]

/-- All polynomially weighted coefficient norms of an all-grade core are
absolutely summable. -/
theorem core_weighted_norm_summable
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (values : JCore Value) (order : ℕ) :
    Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ order * ‖values.1 mode‖) :=
  weighted_norm_summable_of_all_grades values.1
    (fun grade => core_grade_energy_summable values grade) order

/-- One vector-valued character term in the uniform Fourier reconstruction. -/
def vectorTorusTerm
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (mode : FourierMode) (value : Value) : C(ProductTorus, Value) where
  toFun point := torusCharacter mode point • value
  continuous_toFun := (torusCharacter mode).continuous.smul continuous_const

theorem vectorTorusTerm_norm_le
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (mode : FourierMode) (value : Value) :
    ‖vectorTorusTerm mode value‖ ≤ ‖value‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg value)]
  intro point
  change ‖torusCharacter mode point • value‖ ≤ ‖value‖
  rw [norm_smul]
  have characterBound : ‖torusCharacter mode point‖ ≤ 1 := by
    exact ((torusCharacter mode).norm_coe_le_norm point).trans_eq
      UnitAddTorus.mFourier_norm
  simpa using mul_le_mul_of_nonneg_right characterBound (norm_nonneg value)

/-- The character series of an all-grade core converges absolutely in the
uniform norm on the probability product torus. -/
theorem vectorTorusTerm_summable
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) :
    Summable (fun mode : FourierMode => vectorTorusTerm mode (values.1 mode)) := by
  have coefficientNorms : Summable (fun mode : FourierMode => ‖values.1 mode‖) := by
    simpa using core_weighted_norm_summable values 0
  exact Summable.of_norm_bounded coefficientNorms
    (fun mode => vectorTorusTerm_norm_le mode (values.1 mode))

/-- The one continuous product-torus field reconstructed from a coefficient
family lying in every integer Fourier grade. -/
def reconstructedTorus
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) : C(ProductTorus, Value) :=
  ∑' mode : FourierMode, vectorTorusTerm mode (values.1 mode)

theorem hasSum_reconstructedTorus
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) :
    HasSum (fun mode : FourierMode => vectorTorusTerm mode (values.1 mode))
      (reconstructedTorus values) :=
  (vectorTorusTerm_summable values).hasSum

/-- The uniform reconstruction has exactly the paper's physical frequencies
on normalized representatives. -/
theorem reconstructedTorus_normalized_apply
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) (y₁ y₂ ζ : ℝ) :
    reconstructedTorus values (normalizedTorusPoint y₁ y₂ ζ) =
      ∑' mode : FourierMode, Complex.exp (Complex.I *
        (((Real.pi / 2) * mode.1) * y₁ +
          ((Real.pi / 2) * mode.2.1) * y₂ + mode.2.2 * ζ)) • values.1 mode := by
  unfold reconstructedTorus
  change (ContinuousMap.evalCLM ℂ (normalizedTorusPoint y₁ y₂ ζ))
      (∑' mode : FourierMode, vectorTorusTerm mode (values.1 mode)) = _
  rw [(ContinuousMap.evalCLM ℂ (normalizedTorusPoint y₁ y₂ ζ)).map_tsum
    (vectorTorusTerm_summable values)]
  apply tsum_congr
  intro mode
  change torusCharacter mode (normalizedTorusPoint y₁ y₂ ζ) • values.1 mode = _
  rw [torusCharacter_normalized_apply]

/-- In the scalar case the reconstructed continuous field, mapped to `L²`,
is exactly the inverse Hilbert-basis image of the grade-zero coefficient
sequence. -/
theorem scalar_reconstructedTorus_toLp (values : JCore ℂ) :
    ContinuousMap.toLp 2 volume ℂ (reconstructedTorus values) =
      UnitAddTorus.mFourierBasis.repr.symm
        ⟨fun index : Fin 3 → ℤ => values.1 (vectorMode index), by
          have baseMember : Memℓp values.1 2 := by
            convert values.property 0 using 1
            funext mode
            simp
          apply memℓp_gen
          have baseSummable := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp baseMember
          simpa [Function.comp_def, modeEquiv] using
            modeEquiv.symm.summable_iff.mpr baseSummable⟩ := by
  let reindexedValues : lp (fun _ : Fin 3 → ℤ => ℂ) 2 :=
    ⟨fun index => values.1 (vectorMode index), by
      have baseMember : Memℓp values.1 2 := by
        convert values.property 0 using 1
        funext mode
        simp
      apply memℓp_gen
      have baseSummable :=
        (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp baseMember
      simpa [Function.comp_def, modeEquiv] using
        modeEquiv.symm.summable_iff.mpr baseSummable⟩
  have mapped := (ContinuousMap.toLp 2 volume ℂ).hasSum
    (hasSum_reconstructedTorus values)
  have mappedSeries : HasSum
      (fun mode : FourierMode => values.1 mode • torusCharacterL2 mode)
      (ContinuousMap.toLp 2 volume ℂ (reconstructedTorus values)) := by
    convert mapped using 1
    funext mode
    change values.1 mode • ContinuousMap.toLp 2 volume ℂ (torusCharacter mode) =
      ContinuousMap.toLp 2 volume ℂ (vectorTorusTerm mode (values.1 mode))
    rw [← (ContinuousMap.toLp 2 volume ℂ).map_smul]
    apply congrArg
    ext point
    change values.1 mode * torusCharacter mode point =
      torusCharacter mode point * values.1 mode
    rw [mul_comm]
  have basisSeries : HasSum
      (fun mode : FourierMode => values.1 mode • torusCharacterL2 mode)
      (UnitAddTorus.mFourierBasis.repr.symm reindexedValues) := by
    have original := UnitAddTorus.mFourierBasis.hasSum_repr_symm reindexedValues
    have reindexed := modeEquiv.hasSum_iff.mpr original
    convert reindexed using 1
    funext mode
    change values.1 mode • torusCharacterL2 mode =
      reindexedValues (modeVector mode) • UnitAddTorus.mFourierBasis (modeVector mode)
    congr 1
    rw [UnitAddTorus.coe_mFourierBasis]
    rfl
  exact mappedSeries.unique basisSeries

/-- Fourier integration of the uniformly reconstructed scalar series recovers
the original literal coefficient at every mode. -/
theorem scalar_reconstructedTorus_coefficient (values : JCore ℂ)
    (mode : FourierMode) :
    continuousTorusCoefficient (reconstructedTorus values) mode = values.1 mode := by
  let reindexedValues : lp (fun _ : Fin 3 → ℤ => ℂ) 2 :=
    ⟨fun index => values.1 (vectorMode index), by
      have baseMember : Memℓp values.1 2 := by
        convert values.property 0 using 1
        funext sourceMode
        simp
      apply memℓp_gen
      have baseSummable :=
        (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp baseMember
      simpa [Function.comp_def, modeEquiv] using
        modeEquiv.symm.summable_iff.mpr baseSummable⟩
  calc
    continuousTorusCoefficient (reconstructedTorus values) mode =
        torusCoefficient (ContinuousMap.toLp 2 volume ℂ
          (reconstructedTorus values)) mode := by
      exact (UnitAddTorus.mFourierCoeff_toLp
        (reconstructedTorus values) (modeVector mode)).symm
    _ = UnitAddTorus.mFourierBasis.repr
        (ContinuousMap.toLp 2 volume ℂ (reconstructedTorus values)) (modeVector mode) := by
      exact (UnitAddTorus.mFourierBasis_repr _ (modeVector mode)).symm
    _ = UnitAddTorus.mFourierBasis.repr
        (UnitAddTorus.mFourierBasis.repr.symm reindexedValues) (modeVector mode) := by
      rw [scalar_reconstructedTorus_toLp]
    _ = reindexedValues (modeVector mode) := by
      rw [UnitAddTorus.mFourierBasis.repr.apply_symm_apply]
    _ = values.1 mode := by
      rfl

/-- One value-space coordinate of an all-grade Euclidean core is again an
all-grade scalar core, with the same literal Fourier index. -/
def euclideanCoordinateCore {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    (coordinate : Fin dimension) : JCore ℂ :=
  ⟨fun mode => values.1 mode coordinate, fun grade => by
    apply (values.property grade).mono'
    intro mode
    have coordinateBound := PiLp.norm_apply_le
      ((frequencyWeight mode : ℂ) ^ grade • values.1 mode) coordinate
    simpa only [PiLp.smul_apply, smul_eq_mul] using coordinateBound⟩

/-- Coordinate projection of a continuous Euclidean-valued torus field. -/
def euclideanContinuousComponent {dimension : ℕ}
    (field : C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension))
    (coordinate : Fin dimension) : C(ProductTorus, ℂ) where
  toFun point := field point coordinate
  continuous_toFun :=
    (euclideanComponent dimension coordinate).continuous.comp field.continuous

theorem euclideanContinuousComponent_reconstructed {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    (coordinate : Fin dimension) :
    euclideanContinuousComponent (reconstructedTorus values) coordinate =
      reconstructedTorus (euclideanCoordinateCore values coordinate) := by
  ext point
  have vectorPointSum :=
    (ContinuousMap.evalCLM ℂ point).hasSum (hasSum_reconstructedTorus values)
  have coordinatePointSum :=
    (euclideanComponent dimension coordinate).hasSum vectorPointSum
  have scalarPointSum := (ContinuousMap.evalCLM ℂ point).hasSum
    (hasSum_reconstructedTorus (euclideanCoordinateCore values coordinate))
  exact coordinatePointSum.unique scalarPointSum

theorem productTorus_continuousMap_integrable
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (field : C(ProductTorus, Value)) : Integrable field := by
  have fromL2 := (Lp.memLp (ContinuousMap.toLp 2 volume ℂ field)).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply fromL2.congr
  exact ContinuousMap.coeFn_toLp volume field

theorem euclideanContinuousComponent_mFourierCoeff {dimension : ℕ}
    (field : C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension))
    (coordinate : Fin dimension) (index : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff field index coordinate =
      UnitAddTorus.mFourierCoeff (euclideanContinuousComponent field coordinate) index := by
  let integrand : C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension) :=
    ⟨fun point => UnitAddTorus.mFourier (-index) point • field point,
      (UnitAddTorus.mFourier (-index)).continuous.smul field.continuous⟩
  have commutes := (euclideanComponent dimension coordinate).integral_comp_comm
    (productTorus_continuousMap_integrable integrand)
  exact commutes.symm

/-- Fourier integration of the one uniformly reconstructed
finite-dimensional field recovers its original vector coefficient. -/
theorem euclidean_reconstructedTorus_coefficient {dimension : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    (mode : FourierMode) :
    UnitAddTorus.mFourierCoeff (reconstructedTorus values) (modeVector mode) =
      values.1 mode := by
  ext coordinate
  calc
    UnitAddTorus.mFourierCoeff (reconstructedTorus values) (modeVector mode) coordinate =
        continuousTorusCoefficient
          (euclideanContinuousComponent (reconstructedTorus values) coordinate) mode :=
      euclideanContinuousComponent_mFourierCoeff
        (reconstructedTorus values) coordinate (modeVector mode)
    _ = continuousTorusCoefficient
        (reconstructedTorus (euclideanCoordinateCore values coordinate)) mode := by
      rw [euclideanContinuousComponent_reconstructed]
    _ = (euclideanCoordinateCore values coordinate).1 mode :=
      scalar_reconstructedTorus_coefficient (euclideanCoordinateCore values coordinate) mode
    _ = values.1 mode coordinate := rfl

/-- Real physical coordinate space for the three frequencies
`(π k₁/2, π k₂/2, n)`. -/
abbrev PhysicalFrequencySpace := EuclideanSpace ℝ (Fin 3)

/-- The purely imaginary real-linear phase functional of one physical Fourier
mode. -/
def physicalPhaseLinear (mode : FourierMode) : PhysicalFrequencySpace →L[ℝ] ℂ :=
  Complex.I • Complex.ofRealCLM.comp (innerSL ℝ (frequencyVector mode))

@[simp] theorem physicalPhaseLinear_apply (mode : FourierMode)
    (point : PhysicalFrequencySpace) :
    physicalPhaseLinear mode point =
      Complex.I * (inner ℝ (frequencyVector mode) point : ℂ) := by
  simp [physicalPhaseLinear, innerSL_apply_apply, smul_eq_mul]

theorem physicalPhaseLinear_norm_le_weight (mode : FourierMode) :
    ‖physicalPhaseLinear mode‖ ≤ frequencyWeight mode := by
  apply (physicalPhaseLinear mode).opNorm_le_bound (frequencyWeight_pos mode).le
  intro point
  rw [physicalPhaseLinear_apply, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |inner ℝ (frequencyVector mode) point| ≤
        ‖frequencyVector mode‖ * ‖point‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (frequencyVector mode) point)
    _ ≤ frequencyWeight mode * ‖point‖ :=
      mul_le_mul_of_nonneg_right (by
        rw [frequencyWeight]
        exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by
          nlinarith [sq_nonneg ‖frequencyVector mode‖])) (norm_nonneg point)

/-- The complex iterated Fréchet derivative of `exp` is the scalar-product
multilinear map with coefficient `exp argument`. -/
theorem complex_exp_iteratedFDeriv (rank : ℕ) (argument : ℂ) :
    iteratedFDeriv ℂ rank Complex.exp argument =
      ContinuousMultilinearMap.piFieldEquiv ℂ (Fin rank) ℂ
        (Complex.exp argument) := by
  rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
  have identity := congrFun (iteratedDeriv_cexp_const_mul rank 1) argument
  simpa using identity

theorem complex_exp_real_iteratedFDeriv_norm (rank : ℕ) (argument : ℂ) :
    ‖iteratedFDeriv ℝ rank Complex.exp argument‖ = ‖Complex.exp argument‖ := by
  have complexSmooth : ContDiffAt ℂ rank Complex.exp argument :=
    Complex.contDiff_exp.contDiffAt
  rw [← complexSmooth.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  rw [complex_exp_iteratedFDeriv, LinearIsometryEquiv.norm_map]

theorem physicalPhase_exp_iteratedFDeriv_norm (rank : ℕ) (mode : FourierMode)
    (point : PhysicalFrequencySpace) :
    ‖iteratedFDeriv ℝ rank Complex.exp (physicalPhaseLinear mode point)‖ = 1 := by
  rw [complex_exp_real_iteratedFDeriv_norm, Complex.norm_exp,
    physicalPhaseLinear_apply]
  simp

/-- The actual smooth physical character with the paper's anisotropic
frequency vector. -/
def physicalCharacter (mode : FourierMode) : PhysicalFrequencySpace → ℂ :=
  Complex.exp ∘ physicalPhaseLinear mode

theorem physicalCharacter_contDiff (mode : FourierMode) :
    ContDiff ℝ ∞ (physicalCharacter mode) :=
  Complex.contDiff_exp.comp (physicalPhaseLinear mode).contDiff

theorem physicalCharacter_iteratedFDeriv_norm_le
    (rank : ℕ) (mode : FourierMode) (point : PhysicalFrequencySpace) :
    ‖iteratedFDeriv ℝ rank (physicalCharacter mode) point‖ ≤
      frequencyWeight mode ^ rank := by
  rw [physicalCharacter,
    (physicalPhaseLinear mode).iteratedFDeriv_comp_right (n := ∞)
      (Complex.contDiff_exp (𝕜 := ℝ)) point (i := rank)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl rank)]
  calc
    ‖(iteratedFDeriv ℝ rank Complex.exp (physicalPhaseLinear mode point)).compContinuousLinearMap
        (fun _ => physicalPhaseLinear mode)‖ ≤
        ‖iteratedFDeriv ℝ rank Complex.exp (physicalPhaseLinear mode point)‖ *
          ∏ _ : Fin rank, ‖physicalPhaseLinear mode‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖physicalPhaseLinear mode‖ ^ rank := by
      rw [physicalPhase_exp_iteratedFDeriv_norm, one_mul]
      simp
    _ ≤ frequencyWeight mode ^ rank :=
      pow_le_pow_left₀ (norm_nonneg _) (physicalPhaseLinear_norm_le_weight mode) rank

/-- One smooth physical Fourier summand. -/
def physicalFourierTerm
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (mode : FourierMode) (value : Value) (point : PhysicalFrequencySpace) : Value :=
  physicalCharacter mode point • value

theorem physicalFourierTerm_contDiff
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (mode : FourierMode) (value : Value) :
    ContDiff ℝ ∞ (physicalFourierTerm mode value) :=
  (physicalCharacter_contDiff mode).smul_const value

theorem physicalFourierTerm_iteratedFDeriv_norm_le
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (rank : ℕ) (mode : FourierMode) (value : Value)
    (point : PhysicalFrequencySpace) :
    ‖iteratedFDeriv ℝ rank (physicalFourierTerm mode value) point‖ ≤
      frequencyWeight mode ^ rank * ‖value‖ := by
  change ‖iteratedFDeriv ℝ rank
      (fun point => physicalCharacter mode point • value) point‖ ≤ _
  rw [iteratedFDeriv_smul_const_apply
    ((physicalCharacter_contDiff mode).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl rank))]
  have smulRightNorm :
      ‖(ContinuousLinearMap.id ℝ ℂ).smulRight value‖ ≤ ‖value‖ := by
    refine ContinuousLinearMap.opNorm_le_bound
      ((ContinuousLinearMap.id ℝ ℂ).smulRight value) (norm_nonneg value) ?_
    intro scalar
    change ‖scalar • value‖ ≤ ‖value‖ * ‖scalar‖
    rw [norm_smul]
    exact le_of_eq (mul_comm _ _)
  calc
    ‖((ContinuousLinearMap.id ℝ ℂ).smulRight value).compContinuousMultilinearMap
        (iteratedFDeriv ℝ rank (physicalCharacter mode) point)‖ ≤
        ‖(ContinuousLinearMap.id ℝ ℂ).smulRight value‖ *
          ‖iteratedFDeriv ℝ rank (physicalCharacter mode) point‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖value‖ * (frequencyWeight mode ^ rank) :=
      mul_le_mul smulRightNorm
        (physicalCharacter_iteratedFDeriv_norm_le rank mode point)
        (norm_nonneg _) (norm_nonneg _)
    _ = frequencyWeight mode ^ rank * ‖value‖ := by rw [mul_comm]

/-- The single smooth periodic physical representative reconstructed from an
all-grade coefficient family. -/
def reconstructedPhysical
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) : PhysicalFrequencySpace → Value :=
  fun point => ∑' mode : FourierMode,
    physicalFourierTerm mode (values.1 mode) point

theorem reconstructedPhysical_contDiff
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) :
    ContDiff ℝ ∞ (reconstructedPhysical values) := by
  apply contDiff_tsum
    (f := fun mode : FourierMode => physicalFourierTerm mode (values.1 mode))
    (v := fun rank mode => frequencyWeight mode ^ rank * ‖values.1 mode‖)
  · exact fun mode => physicalFourierTerm_contDiff mode (values.1 mode)
  · intro rank _rankBound
    exact core_weighted_norm_summable values rank
  · intro rank mode point _rankBound
    exact physicalFourierTerm_iteratedFDeriv_norm_le rank mode (values.1 mode) point

/-- A literal physical-coordinate representative in the real Euclidean
frequency space. -/
def physicalPoint (y₁ y₂ ζ : ℝ) : PhysicalFrequencySpace :=
  WithLp.toLp 2 ![y₁, y₂, ζ]

@[simp] theorem physicalPhaseLinear_physicalPoint (mode : FourierMode)
    (y₁ y₂ ζ : ℝ) :
    physicalPhaseLinear mode (physicalPoint y₁ y₂ ζ) =
      Complex.I *
        (((Real.pi / 2) * mode.1) * y₁ +
          ((Real.pi / 2) * mode.2.1) * y₂ + mode.2.2 * ζ) := by
  rw [physicalPhaseLinear_apply]
  congr 1
  rw [PiLp.inner_apply]
  simp [frequencyVector, physicalPoint, Fin.sum_univ_succ]
  ring

@[simp] theorem physicalCharacter_physicalPoint (mode : FourierMode)
    (y₁ y₂ ζ : ℝ) :
    physicalCharacter mode (physicalPoint y₁ y₂ ζ) =
      Complex.exp (Complex.I *
        (((Real.pi / 2) * mode.1) * y₁ +
          ((Real.pi / 2) * mode.2.1) * y₂ + mode.2.2 * ζ)) := by
  change Complex.exp (physicalPhaseLinear mode (physicalPoint y₁ y₂ ζ)) = _
  rw [physicalPhaseLinear_physicalPoint]

/-- The smooth physical reconstruction descends to exactly the uniformly
reconstructed product-torus field on every physical representative. -/
theorem reconstructedPhysical_physicalPoint
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (values : JCore Value) (y₁ y₂ ζ : ℝ) :
    reconstructedPhysical values (physicalPoint y₁ y₂ ζ) =
      reconstructedTorus values (normalizedTorusPoint y₁ y₂ ζ) := by
  rw [reconstructedTorus_normalized_apply]
  unfold reconstructedPhysical physicalFourierTerm
  apply tsum_congr
  intro mode
  rw [physicalCharacter_physicalPoint]

end Grad.FourierGrade
