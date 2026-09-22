import FT3Reconstruction

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff

universe valueUniverse

namespace Grad.FourierGrade

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Isometric insertion of one complex coordinate into the actual finite
Euclidean value carrier. -/
def euclideanSingle (dimension : ℕ) (coordinate : Fin dimension) :
    ℂ →ₗᵢ[ℂ] Grad.ClosedJets.ComplexEuclidean dimension where
  toFun value := PiLp.single 2 coordinate value
  map_add' first second := PiLp.single_add 2 coordinate
  map_smul' scalar value := by
    apply PiLp.ext
    intro target
    by_cases equality : coordinate = target
    · subst target
      simp
    · simp [equality]
  norm_map' value := by simp

/-- Insert one scalar `L²` coordinate into the finite-dimensional vector
`L²` space. -/
def euclideanSingleL2 (dimension : ℕ) (coordinate : Fin dimension) :
    ScalarTorusL2 →L[ℂ] EuclideanTorusL2 dimension :=
  (euclideanSingle dimension coordinate).toContinuousLinearMap.compLpL 2 volume

/-- The explicit finite-coordinate vector Fourier term.  Each coordinate is
the scalar Fourier term of the corresponding component. -/
def euclideanL2FourierTerm {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (mode : FourierMode) :
    EuclideanTorusL2 dimension :=
  ∑ coordinate : Fin dimension,
    torusCoefficient (euclideanComponentL2 field coordinate) mode •
      euclideanSingleL2 dimension coordinate (torusCharacterL2 mode)

theorem euclideanSingleL2_component_ae {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (coordinate : Fin dimension) :
    (fun point : ProductTorus =>
      euclideanSingleL2 dimension coordinate
        (euclideanComponentL2 field coordinate) point) =ᵐ[volume]
      fun point => PiLp.single 2 coordinate (field point coordinate) := by
  filter_upwards [
    (euclideanSingle dimension coordinate).toContinuousLinearMap.coeFn_compLpL
      (euclideanComponentL2 field coordinate),
    euclideanComponentL2_ae field coordinate] with point inserted component
  calc
    euclideanSingleL2 dimension coordinate
        (euclideanComponentL2 field coordinate) point =
        (euclideanSingle dimension coordinate).toContinuousLinearMap
          (euclideanComponentL2 field coordinate point) := by
      simpa only [euclideanSingleL2] using inserted
    _ = PiLp.single 2 coordinate (field point coordinate) := by
      rw [component]
      rfl

theorem euclidean_l2_coordinate_decomposition {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) :
    (∑ coordinate : Fin dimension,
      euclideanSingleL2 dimension coordinate
        (euclideanComponentL2 field coordinate)) = field := by
  apply Lp.ext
  have allCoordinates : ∀ᵐ point : ProductTorus, ∀ coordinate : Fin dimension,
      euclideanSingleL2 dimension coordinate
          (euclideanComponentL2 field coordinate) point =
        PiLp.single 2 coordinate (field point coordinate) :=
    ae_all_iff.mpr (fun coordinate =>
      euclideanSingleL2_component_ae field coordinate)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun coordinate => euclideanSingleL2 dimension coordinate
        (euclideanComponentL2 field coordinate)), allCoordinates]
    with point summed coordinates
  rw [summed]
  have vectorSum :
      (∑ coordinate : Fin dimension,
        euclideanSingleL2 dimension coordinate
          (euclideanComponentL2 field coordinate) point) =
      ∑ coordinate : Fin dimension,
        PiLp.single 2 coordinate (field point coordinate) := by
    exact Finset.sum_congr rfl (fun coordinate _ => coordinates coordinate)
  rw [vectorSum]
  apply PiLp.ext
  intro target
  simp

/-- The explicit vector Fourier series converges in the actual vector-valued
`L²` norm.  This is the finite-dimensional counterpart of the scalar basis
series, with no coordinate or norm weakening. -/
theorem euclidean_fourier_series_L2 {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) :
    HasSum (euclideanL2FourierTerm field) field := by
  have coordinateSeries : ∀ coordinate : Fin dimension,
      HasSum
        (fun mode : FourierMode =>
          torusCoefficient (euclideanComponentL2 field coordinate) mode •
            euclideanSingleL2 dimension coordinate (torusCharacterL2 mode))
        (euclideanSingleL2 dimension coordinate
          (euclideanComponentL2 field coordinate)) := by
    intro coordinate
    simpa only [map_smul] using
      (euclideanSingleL2 dimension coordinate).hasSum
        (torus_fourier_series_L2 (euclideanComponentL2 field coordinate))
  have finiteSeries : ∀ coordinates : Finset (Fin dimension),
      HasSum
        (fun mode : FourierMode => ∑ coordinate ∈ coordinates,
          torusCoefficient (euclideanComponentL2 field coordinate) mode •
            euclideanSingleL2 dimension coordinate (torusCharacterL2 mode))
        (∑ coordinate ∈ coordinates,
          euclideanSingleL2 dimension coordinate
            (euclideanComponentL2 field coordinate)) := by
    intro coordinates
    induction coordinates using Finset.induction_on with
    | empty => simp
    | @insert coordinate coordinates fresh inductionHypothesis =>
        simpa [Finset.sum_insert, fresh] using
          (coordinateSeries coordinate).add inductionHypothesis
  change HasSum (fun mode : FourierMode => ∑ coordinate : Fin dimension,
    torusCoefficient (euclideanComponentL2 field coordinate) mode •
      euclideanSingleL2 dimension coordinate (torusCharacterL2 mode)) field
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true,
    euclidean_l2_coordinate_decomposition field] using finiteSeries Finset.univ

/-- The conventional vector Fourier term: the literal vector coefficient
multiplied by the literal torus character, regarded in `L²`. -/
def euclideanVectorFourierTerm {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (mode : FourierMode) :
    EuclideanTorusL2 dimension :=
  ContinuousMap.toLp 2 volume ℂ
    (vectorTorusTerm mode (euclideanTorusCoefficient field mode))

theorem euclideanSingleL2_torusCharacter_ae (dimension : ℕ)
    (coordinate : Fin dimension) (mode : FourierMode) :
    (fun point : ProductTorus =>
      euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) point) =ᵐ[volume]
      fun point => PiLp.single 2 coordinate (torusCharacter mode point) := by
  filter_upwards [
    (euclideanSingle dimension coordinate).toContinuousLinearMap.coeFn_compLpL
      (torusCharacterL2 mode),
    UnitAddTorus.coeFn_mFourierLp 2 (modeVector mode)]
    with point inserted character
  rw [show euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) point =
      (euclideanSingle dimension coordinate).toContinuousLinearMap
        (torusCharacterL2 mode point) by
        simpa only [euclideanSingleL2] using inserted]
  have characterValue : torusCharacterL2 mode point = torusCharacter mode point := by
    exact character
  rw [characterValue]
  rfl

/-- The finite-coordinate term is exactly the conventional vector Fourier
term, so the preceding series is an explicit vector Fourier projection
sequence rather than merely a coordinatewise surrogate. -/
theorem euclideanL2FourierTerm_eq_vectorTerm {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (mode : FourierMode) :
    euclideanL2FourierTerm field mode = euclideanVectorFourierTerm field mode := by
  apply Lp.ext
  have allCoordinates : ∀ᵐ point : ProductTorus, ∀ coordinate : Fin dimension,
      euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) point =
        PiLp.single 2 coordinate (torusCharacter mode point) :=
    ae_all_iff.mpr (fun coordinate =>
      euclideanSingleL2_torusCharacter_ae dimension coordinate mode)
  have allScalars : ∀ᵐ point : ProductTorus, ∀ coordinate : Fin dimension,
      (torusCoefficient (euclideanComponentL2 field coordinate) mode •
          euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) :
        EuclideanTorusL2 dimension) point =
        torusCoefficient (euclideanComponentL2 field coordinate) mode •
          euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) point :=
    ae_all_iff.mpr (fun coordinate => Lp.coeFn_smul
      (torusCoefficient (euclideanComponentL2 field coordinate) mode)
      (euclideanSingleL2 dimension coordinate (torusCharacterL2 mode)))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun coordinate =>
        torusCoefficient (euclideanComponentL2 field coordinate) mode •
          euclideanSingleL2 dimension coordinate (torusCharacterL2 mode)),
    allCoordinates, allScalars,
    ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) volume
      (vectorTorusTerm mode (euclideanTorusCoefficient field mode))]
    with point summed characters scalars conventional
  rw [show (euclideanL2FourierTerm field mode : ProductTorus →
      Grad.ClosedJets.ComplexEuclidean dimension) point =
      ∑ coordinate : Fin dimension,
        (torusCoefficient (euclideanComponentL2 field coordinate) mode •
          euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) :
            EuclideanTorusL2 dimension) point by
      exact summed]
  change (∑ coordinate : Fin dimension,
      (torusCoefficient (euclideanComponentL2 field coordinate) mode •
        euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) :
          EuclideanTorusL2 dimension) point) =
    (ContinuousMap.toLp 2 volume ℂ
      (vectorTorusTerm mode (euclideanTorusCoefficient field mode))) point
  rw [conventional]
  rw [Finset.sum_congr rfl (fun coordinate _ => scalars coordinate)]
  change (∑ coordinate : Fin dimension,
      torusCoefficient (euclideanComponentL2 field coordinate) mode •
        euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) point) =
    torusCharacter mode point • euclideanTorusCoefficient field mode
  have characterSum :
      (∑ coordinate : Fin dimension,
        torusCoefficient (euclideanComponentL2 field coordinate) mode •
          euclideanSingleL2 dimension coordinate (torusCharacterL2 mode) point) =
        ∑ coordinate : Fin dimension,
          torusCoefficient (euclideanComponentL2 field coordinate) mode •
            PiLp.single 2 coordinate (torusCharacter mode point) := by
    apply Finset.sum_congr rfl
    intro coordinate _membership
    rw [characters coordinate]
  rw [characterSum]
  have commuteSingle : ∀ coordinate : Fin dimension,
      torusCoefficient (euclideanComponentL2 field coordinate) mode •
          (PiLp.single 2 coordinate (torusCharacter mode point) :
            Grad.ClosedJets.ComplexEuclidean dimension) =
        torusCharacter mode point •
          (PiLp.single 2 coordinate
            (torusCoefficient (euclideanComponentL2 field coordinate) mode) :
              Grad.ClosedJets.ComplexEuclidean dimension) := by
    intro coordinate
    apply PiLp.ext
    intro target
    by_cases equality : coordinate = target
    · subst target
      simp [mul_comm]
    · simp [equality]
  rw [Finset.sum_congr rfl (fun coordinate _ => commuteSingle coordinate)]
  rw [← Finset.smul_sum]
  congr 1
  apply PiLp.ext
  intro target
  simp only [euclideanComponentL2_coefficient]
  simp

/-- Conventional vector Fourier terms themselves converge in `L²`. -/
theorem euclidean_vector_fourier_series_L2 {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) :
    HasSum (euclideanVectorFourierTerm field) field := by
  convert euclidean_fourier_series_L2 field using 1
  funext mode
  exact (euclideanL2FourierTerm_eq_vectorTerm field mode).symm

/-- Unit coordinate direction in physical Euclidean space. -/
def physicalCoordinateDirection (coordinate : Fin 3) : PhysicalFrequencySpace :=
  PiLp.single 2 coordinate 1

/-- The complex multiplier for one physical partial derivative. -/
def partialFrequencyFactor (coordinate : Fin 3) (mode : FourierMode) : ℂ :=
  Complex.I * (frequencyVector mode coordinate : ℂ)

@[simp] theorem partialFrequencyFactor_norm (coordinate : Fin 3)
    (mode : FourierMode) :
    ‖partialFrequencyFactor coordinate mode‖ =
      |frequencyVector mode coordinate| := by
  rw [partialFrequencyFactor, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

@[simp] theorem physicalPhaseLinear_coordinateDirection (coordinate : Fin 3)
    (mode : FourierMode) :
    physicalPhaseLinear mode (physicalCoordinateDirection coordinate) =
      partialFrequencyFactor coordinate mode := by
  rw [physicalPhaseLinear_apply, partialFrequencyFactor]
  congr 1
  rw [PiLp.inner_apply]
  simp [physicalCoordinateDirection]

/-- Coefficients after one actual physical partial derivative.  Membership in
every grade follows from one additional exact Fourier weight. -/
def partialDerivativeCore
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (values : JCore Value) : JCore Value := by
  refine ⟨fun mode => partialFrequencyFactor coordinate mode • values.1 mode,
    fun grade => ?_⟩
  apply (values.property (grade + 1)).mono'
  intro mode
  simp only [norm_smul, partialFrequencyFactor_norm, Complex.norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (frequencyWeight_pos mode)]
  have coordinateBound := frequencyVector_abs_le_weight mode coordinate
  have weightNonnegative : 0 ≤ frequencyWeight mode :=
    (frequencyWeight_pos mode).le
  calc
    frequencyWeight mode ^ grade *
        (|frequencyVector mode coordinate| * ‖values.1 mode‖) =
        (frequencyWeight mode ^ grade * |frequencyVector mode coordinate|) *
          ‖values.1 mode‖ := by ring
    _ ≤ (frequencyWeight mode ^ grade * frequencyWeight mode) *
          ‖values.1 mode‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left coordinateBound (pow_nonneg weightNonnegative _))
        (norm_nonneg _)
    _ = frequencyWeight mode ^ (grade + 1) * ‖values.1 mode‖ := by
      rw [pow_succ]

@[simp] theorem partialDerivativeCore_apply
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (values : JCore Value) (mode : FourierMode) :
    (partialDerivativeCore coordinate values).1 mode =
      partialFrequencyFactor coordinate mode • values.1 mode := rfl

theorem physicalFourierTerm_fderiv_coordinate
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (mode : FourierMode) (value : Value)
    (point : PhysicalFrequencySpace) :
    fderiv ℝ (physicalFourierTerm mode value) point
        (physicalCoordinateDirection coordinate) =
      physicalFourierTerm mode
        (partialFrequencyFactor coordinate mode • value) point := by
  have characterDerivative : HasFDerivAt (physicalCharacter mode)
      (Complex.exp (physicalPhaseLinear mode point) • physicalPhaseLinear mode) point := by
    change HasFDerivAt (fun point => Complex.exp (physicalPhaseLinear mode point)) _ point
    exact (physicalPhaseLinear mode).hasFDerivAt.cexp
  have termDerivative := (characterDerivative.smul_const value).fderiv
  change fderiv ℝ (fun point => physicalCharacter mode point • value) point
      (physicalCoordinateDirection coordinate) = _
  rw [termDerivative, ContinuousLinearMap.smulRight_apply]
  simp only [smul_apply, physicalPhaseLinear_coordinateDirection,
    physicalCharacter, Function.comp_apply, physicalFourierTerm, smul_smul]
  congr 1

@[simp] theorem physicalCharacter_norm (mode : FourierMode)
    (point : PhysicalFrequencySpace) :
    ‖physicalCharacter mode point‖ = 1 := by
  rw [physicalCharacter, Function.comp_apply, Complex.norm_exp,
    physicalPhaseLinear_apply]
  simp

@[simp] theorem physicalFourierTerm_norm
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (mode : FourierMode) (value : Value) (point : PhysicalFrequencySpace) :
    ‖physicalFourierTerm mode value point‖ = ‖value‖ := by
  rw [physicalFourierTerm, norm_smul, physicalCharacter_norm, one_mul]

theorem physicalFourierTerm_point_summable
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value]
    (values : JCore Value) (point : PhysicalFrequencySpace) :
    Summable (fun mode : FourierMode =>
      physicalFourierTerm mode (values.1 mode) point) := by
  have coefficientNorms : Summable (fun mode : FourierMode => ‖values.1 mode‖) := by
    simpa using core_weighted_norm_summable values 0
  exact Summable.of_norm_bounded coefficientNorms
    (fun mode => (physicalFourierTerm_norm mode (values.1 mode) point).le)

theorem physicalFourierTerm_fderiv_norm_le
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (mode : FourierMode) (value : Value) (point : PhysicalFrequencySpace) :
    ‖fderiv ℝ (physicalFourierTerm mode value) point‖ ≤
      frequencyWeight mode * ‖value‖ := by
  rw [← norm_iteratedFDeriv_one]
  simpa only [pow_one] using
    physicalFourierTerm_iteratedFDeriv_norm_le 1 mode value point

/-- Actual coordinate partial differentiation on the physical representative. -/
def physicalPartialDerivative
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (field : PhysicalFrequencySpace → Value) :
    PhysicalFrequencySpace → Value :=
  fun point => fderiv ℝ field point (physicalCoordinateDirection coordinate)

/-- Differentiating the uniformly reconstructed physical field in an actual
coordinate direction gives the reconstruction of the exactly multiplied
coefficient core. -/
theorem physicalPartialDerivative_reconstructed
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (coordinate : Fin 3) (values : JCore Value) :
    physicalPartialDerivative coordinate (reconstructedPhysical values) =
      reconstructedPhysical (partialDerivativeCore coordinate values) := by
  funext point
  have weightedSummable : Summable (fun mode : FourierMode =>
      frequencyWeight mode * ‖values.1 mode‖) := by
    simpa only [pow_one] using core_weighted_norm_summable values 1
  have derivativeIdentity :
      fderiv ℝ (reconstructedPhysical values) point =
        ∑' mode : FourierMode,
          fderiv ℝ (physicalFourierTerm mode (values.1 mode)) point := by
    apply fderiv_tsum_apply
      (u := fun mode : FourierMode => frequencyWeight mode * ‖values.1 mode‖)
      (x₀ := 0)
    · exact weightedSummable
    · exact fun mode => (physicalFourierTerm_contDiff mode
        (values.1 mode)).differentiable (by simp)
    · exact fun mode sourcePoint =>
        physicalFourierTerm_fderiv_norm_le mode (values.1 mode) sourcePoint
    · exact physicalFourierTerm_point_summable values 0
  have derivativeSummable : Summable (fun mode : FourierMode =>
      fderiv ℝ (physicalFourierTerm mode (values.1 mode)) point) :=
    Summable.of_norm_bounded weightedSummable
      (fun mode => physicalFourierTerm_fderiv_norm_le mode (values.1 mode) point)
  calc
    physicalPartialDerivative coordinate (reconstructedPhysical values) point =
        (∑' mode : FourierMode,
          fderiv ℝ (physicalFourierTerm mode (values.1 mode)) point)
            (physicalCoordinateDirection coordinate) := by
      rw [physicalPartialDerivative, derivativeIdentity]
    _ = ∑' mode : FourierMode,
        fderiv ℝ (physicalFourierTerm mode (values.1 mode)) point
          (physicalCoordinateDirection coordinate) := by
      simpa using (ContinuousLinearMap.apply ℝ Value
        (physicalCoordinateDirection coordinate)).map_tsum derivativeSummable
    _ = ∑' mode : FourierMode,
        physicalFourierTerm mode
          (partialFrequencyFactor coordinate mode • values.1 mode) point := by
      apply tsum_congr
      intro mode
      exact physicalFourierTerm_fderiv_coordinate coordinate mode (values.1 mode) point
    _ = reconstructedPhysical (partialDerivativeCore coordinate values) point := rfl

/-- Repeat one coordinate derivative exactly `count` times. -/
def repeatedPhysicalPartial
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (count : ℕ)
    (field : PhysicalFrequencySpace → Value) : PhysicalFrequencySpace → Value :=
  (physicalPartialDerivative coordinate)^[count] field

/-- Repeat the matching coefficient multiplier exactly `count` times. -/
def repeatedPartialCore
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (count : ℕ) (values : JCore Value) : JCore Value :=
  (partialDerivativeCore coordinate)^[count] values

theorem repeatedPhysicalPartial_reconstructed
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (coordinate : Fin 3) (count : ℕ) (values : JCore Value) :
    repeatedPhysicalPartial coordinate count (reconstructedPhysical values) =
      reconstructedPhysical (repeatedPartialCore coordinate count values) := by
  induction count generalizing values with
  | zero => simp [repeatedPhysicalPartial, repeatedPartialCore]
  | succ count inductionHypothesis =>
      have applied := inductionHypothesis (partialDerivativeCore coordinate values)
      simp only [repeatedPhysicalPartial, repeatedPartialCore] at applied ⊢
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        physicalPartialDerivative_reconstructed, applied]

@[simp] theorem repeatedPartialCore_apply
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (coordinate : Fin 3) (count : ℕ) (values : JCore Value)
    (mode : FourierMode) :
    (repeatedPartialCore coordinate count values).1 mode =
      partialFrequencyFactor coordinate mode ^ count • values.1 mode := by
  induction count generalizing values with
  | zero => simp [repeatedPartialCore]
  | succ count inductionHypothesis =>
      have applied := inductionHypothesis (partialDerivativeCore coordinate values)
      simp only [repeatedPartialCore] at applied ⊢
      rw [Function.iterate_succ_apply, applied, partialDerivativeCore_apply,
        smul_smul, pow_succ]

/-- The exact complex multiplier of the unordered mixed derivative
`(α₁, α₂, b)`. -/
def mixedFrequencyFactor (index : FourierMultiIndex) (mode : FourierMode) : ℂ :=
  partialFrequencyFactor 2 mode ^ index.2 *
    (partialFrequencyFactor 1 mode ^ index.1.2 *
      partialFrequencyFactor 0 mode ^ index.1.1)

/-- Coefficient core of the actual unordered mixed physical derivative. -/
def mixedDerivativeCore
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (index : FourierMultiIndex) (values : JCore Value) : JCore Value :=
  repeatedPartialCore 2 index.2
    (repeatedPartialCore 1 index.1.2
      (repeatedPartialCore 0 index.1.1 values))

/-- The actual unordered mixed derivative of a smooth physical field. -/
def physicalMixedDerivative
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (index : FourierMultiIndex) (field : PhysicalFrequencySpace → Value) :
    PhysicalFrequencySpace → Value :=
  repeatedPhysicalPartial 2 index.2
    (repeatedPhysicalPartial 1 index.1.2
      (repeatedPhysicalPartial 0 index.1.1 field))

@[simp] theorem mixedDerivativeCore_apply
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (index : FourierMultiIndex) (values : JCore Value) (mode : FourierMode) :
    (mixedDerivativeCore index values).1 mode =
      mixedFrequencyFactor index mode • values.1 mode := by
  simp only [mixedDerivativeCore, repeatedPartialCore_apply, mixedFrequencyFactor,
    smul_smul]

theorem physicalMixedDerivative_reconstructed
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (index : FourierMultiIndex) (values : JCore Value) :
    physicalMixedDerivative index (reconstructedPhysical values) =
      reconstructedPhysical (mixedDerivativeCore index values) := by
  rw [physicalMixedDerivative, repeatedPhysicalPartial_reconstructed,
    repeatedPhysicalPartial_reconstructed, repeatedPhysicalPartial_reconstructed]
  rfl

theorem mixedFrequencyFactor_norm_sq (index : FourierMultiIndex)
    (mode : FourierMode) :
    ‖mixedFrequencyFactor index mode‖ ^ 2 = derivativeMultiplier index mode := by
  simp only [mixedFrequencyFactor, norm_mul, norm_pow,
    partialFrequencyFactor_norm, derivativeMultiplier]
  ring

theorem mixedDerivativeCore_norm_sq
    {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (index : FourierMultiIndex) (values : JCore Value) (mode : FourierMode) :
    ‖(mixedDerivativeCore index values).1 mode‖ ^ 2 =
      derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2 := by
  rw [mixedDerivativeCore_apply, norm_smul, mul_pow,
    mixedFrequencyFactor_norm_sq]

theorem euclideanComponentL2_continuousToLp {dimension : ℕ}
    (field : C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension))
    (coordinate : Fin dimension) :
    euclideanComponentL2 (ContinuousMap.toLp 2 volume ℂ field) coordinate =
      ContinuousMap.toLp 2 volume ℂ
        (euclideanContinuousComponent field coordinate) := by
  apply Lp.ext
  filter_upwards [
    euclideanComponentL2_ae (ContinuousMap.toLp 2 volume ℂ field) coordinate,
    ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) volume field,
    ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) volume
      (euclideanContinuousComponent field coordinate)]
    with point component vector scalar
  rw [component, vector, scalar]
  rfl

theorem euclideanTorusCoefficient_continuousToLp {dimension : ℕ}
    (field : C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension))
    (mode : FourierMode) :
    euclideanTorusCoefficient (ContinuousMap.toLp 2 volume ℂ field) mode =
      UnitAddTorus.mFourierCoeff field (modeVector mode) := by
  ext coordinate
  calc
    euclideanTorusCoefficient (ContinuousMap.toLp 2 volume ℂ field) mode coordinate =
        torusCoefficient
          (euclideanComponentL2 (ContinuousMap.toLp 2 volume ℂ field) coordinate)
          mode :=
      (euclideanComponentL2_coefficient
        (ContinuousMap.toLp 2 volume ℂ field) coordinate mode).symm
    _ = torusCoefficient
        (ContinuousMap.toLp 2 volume ℂ
          (euclideanContinuousComponent field coordinate)) mode := by
      rw [euclideanComponentL2_continuousToLp]
    _ = continuousTorusCoefficient
        (euclideanContinuousComponent field coordinate) mode := by
      exact UnitAddTorus.mFourierCoeff_toLp
        (euclideanContinuousComponent field coordinate) (modeVector mode)
    _ = UnitAddTorus.mFourierCoeff field (modeVector mode) coordinate :=
      (euclideanContinuousComponent_mFourierCoeff
        field coordinate (modeVector mode)).symm

/-- P13 directly for an actual continuous finite-dimensional torus field. -/
theorem euclidean_continuous_torus_parseval {dimension : ℕ}
    (field : C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension)) :
    (∫ point : ProductTorus, ‖field point‖ ^ 2) =
      ∑' mode : FourierMode,
        ‖UnitAddTorus.mFourierCoeff field (modeVector mode)‖ ^ 2 := by
  calc
    (∫ point : ProductTorus, ‖field point‖ ^ 2) =
        ∫ point : ProductTorus,
          ‖(ContinuousMap.toLp 2 volume ℂ field) point‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
        (𝕜 := ℂ) volume field]
        with point equality
      rw [equality]
    _ = ∑' mode : FourierMode,
        ‖euclideanTorusCoefficient
          (ContinuousMap.toLp 2 volume ℂ field) mode‖ ^ 2 :=
      euclidean_torus_parseval (ContinuousMap.toLp 2 volume ℂ field)
    _ = ∑' mode : FourierMode,
        ‖UnitAddTorus.mFourierCoeff field (modeVector mode)‖ ^ 2 := by
      apply tsum_congr
      intro mode
      rw [euclideanTorusCoefficient_continuousToLp]

/-- The torus field representing one actual unordered mixed physical
derivative. -/
def torusMixedDerivative {dimension : ℕ}
    (index : FourierMultiIndex)
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    C(ProductTorus, Grad.ClosedJets.ComplexEuclidean dimension) :=
  reconstructedTorus (mixedDerivativeCore index values)

/-- The torus mixed-derivative representative agrees pointwise with the
actual iterated coordinate derivative of the physical reconstruction. -/
theorem physicalMixedDerivative_physicalPoint {dimension : ℕ}
    (index : FourierMultiIndex)
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    (y₁ y₂ ζ : ℝ) :
    physicalMixedDerivative index (reconstructedPhysical values)
        (physicalPoint y₁ y₂ ζ) =
      torusMixedDerivative index values (normalizedTorusPoint y₁ y₂ ζ) := by
  rw [physicalMixedDerivative_reconstructed]
  exact reconstructedPhysical_physicalPoint
    (mixedDerivativeCore index values) y₁ y₂ ζ

/-- The actual derivative Sobolev square norm: sum, over every unordered
mixed index of total order at most `grade`, of the probability-torus `L²`
norm squared of the corresponding actual derivative. -/
def actualDerivativeEnergy {dimension : ℕ} (grade : ℕ)
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) : ℝ :=
  ∑ index ∈ fourierMultiIndices grade,
    ∫ point : ProductTorus, ‖torusMixedDerivative index values point‖ ^ 2

theorem torusMixedDerivative_parseval {dimension : ℕ}
    (index : FourierMultiIndex)
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    (∫ point : ProductTorus, ‖torusMixedDerivative index values point‖ ^ 2) =
      ∑' mode : FourierMode,
        derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2 := by
  calc
    (∫ point : ProductTorus, ‖torusMixedDerivative index values point‖ ^ 2) =
        ∑' mode : FourierMode,
          ‖UnitAddTorus.mFourierCoeff (torusMixedDerivative index values)
            (modeVector mode)‖ ^ 2 :=
      euclidean_continuous_torus_parseval (torusMixedDerivative index values)
    _ = ∑' mode : FourierMode,
        derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2 := by
      apply tsum_congr
      intro mode
      rw [torusMixedDerivative, euclidean_reconstructedTorus_coefficient,
        mixedDerivativeCore_norm_sq]

theorem derivativeMultiplier_sequence_summable {dimension grade : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension))
    {index : FourierMultiIndex} (membership : index ∈ fourierMultiIndices grade) :
    Summable (fun mode : FourierMode =>
      derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun mode => mul_nonneg (derivativeMultiplier_nonneg index mode) (sq_nonneg _))
    (fun mode => mul_le_mul_of_nonneg_right
      (derivativeMultiplier_le_gradeWeight membership mode) (sq_nonneg _))
    (core_grade_energy_summable values grade)

theorem actualDerivativeEnergy_eq_sequenceEnergy {dimension grade : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    actualDerivativeEnergy grade values = derivativeSequenceEnergy grade values.1 := by
  calc
    actualDerivativeEnergy grade values =
        ∑ index ∈ fourierMultiIndices grade,
          ∑' mode : FourierMode,
            derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro index _membership
      exact torusMixedDerivative_parseval index values
    _ = ∑' mode : FourierMode,
        ∑ index ∈ fourierMultiIndices grade,
          derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2 := by
      exact (Summable.tsum_finsetSum
        (fun index membership =>
          derivativeMultiplier_sequence_summable values membership)).symm
    _ = derivativeSequenceEnergy grade values.1 := by
      apply tsum_congr
      intro mode
      change (∑ index ∈ fourierMultiIndices grade,
        derivativeMultiplier index mode * ‖values.1 mode‖ ^ 2) =
        derivativeWeight grade mode * ‖values.1 mode‖ ^ 2
      rw [derivativeWeight, Finset.sum_mul]

theorem derivativeCoefficientEnergy_coreToGrade {dimension grade : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    derivativeCoefficientEnergy grade (coreToGrade grade values) =
      derivativeSequenceEnergy grade values.1 := by
  unfold derivativeCoefficientEnergy derivativeSequenceEnergy
  apply tsum_congr
  intro mode
  rw [coreToGrade_coefficient]

/-- Exact P15 for the actual mixed derivatives of the one reconstructed
smooth torus/physical field. -/
theorem actualDerivativeEnergy_comparison {dimension grade : ℕ}
    (values : JCore (Grad.ClosedJets.ComplexEuclidean dimension)) :
    ((4 : ℝ) ^ grade)⁻¹ * ‖coreToGrade grade values‖ ^ 2 ≤
        actualDerivativeEnergy grade values ∧
      actualDerivativeEnergy grade values ≤
        (Nat.choose (grade + 3) 3 : ℝ) * ‖coreToGrade grade values‖ ^ 2 := by
  have comparison := derivativeCoefficientEnergy_comparison grade
    (coreToGrade grade values)
  rw [derivativeCoefficientEnergy_coreToGrade,
    ← actualDerivativeEnergy_eq_sequenceEnergy] at comparison
  exact comparison

end Grad.FourierGrade
