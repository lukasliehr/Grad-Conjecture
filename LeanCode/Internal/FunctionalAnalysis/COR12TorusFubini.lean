import COR12Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open MeasureTheory
open scoped Interval

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Splitting one coordinate from the normalized product torus preserves the
probability Haar measure. -/
theorem productTorus_piFinSuccAbove_measurePreserving (coordinate : Fin 3) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin 3 => UnitAddCircle) coordinate) := by
  exact volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 => UnitAddCircle) coordinate

/-- The physical period attached to a normalized torus coordinate. -/
def physicalCoordinatePeriod (coordinate : Fin 3) : ℝ :=
  ![(4 : ℝ), (4 : ℝ), 2 * Real.pi] coordinate

theorem physicalCoordinatePeriod_pos (coordinate : Fin 3) :
    0 < physicalCoordinatePeriod coordinate := by
  fin_cases coordinate <;> simp [physicalCoordinatePeriod, Real.pi_pos]

/-- Convert normalized real representatives to physical `(4,4,2π)`
representatives. -/
def physicalPointFromNormalized (point : Fin 3 → ℝ) : SpatialCell :=
  WithLp.toLp 2 (fun coordinate =>
    physicalCoordinatePeriod coordinate * point coordinate)

theorem torusCellToProduct_physicalPointFromNormalized (point : Fin 3 → ℝ) :
    torusCellToProduct
        (torusCellPoint (physicalPointFromNormalized point)) =
      fun coordinate => (point coordinate : UnitAddCircle) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [torusCellToProduct, spatialCircleToUnit, cellCircleToUnit,
      torusCellPoint, physicalPointFromNormalized, physicalCoordinatePeriod] <;>
    field_simp [Real.pi_ne_zero]

theorem torusCellToProduct_symm_insertNth_real
    (coordinate : Fin 3) (rest : Fin 2 → ℝ) (value : ℝ) :
    torusCellToProduct.symm
        (coordinate.insertNth (value : UnitAddCircle)
          (fun index => (rest index : UnitAddCircle))) =
      torusCellPoint
        (physicalPointFromNormalized (coordinate.insertNth value rest)) := by
  apply torusCellToProduct.injective
  rw [torusCellToProduct_physicalPointFromNormalized]
  funext index
  by_cases same : index = coordinate
  · subst index
    simp
  · obtain ⟨other, rfl⟩ := Fin.exists_succAbove_eq same
    simp

def physicalCoordinateEmbeddingLinear (coordinate : Fin 3) :
    ℝ →ₗ[ℝ] SpatialCell where
  toFun value :=
    (physicalCoordinatePeriod coordinate * value) • spatialCellBasis coordinate
  map_add' first second := by
    rw [mul_add, add_smul]
  map_smul' scalar value := by
    simp only [RingHom.id_apply, smul_eq_mul, smul_smul]
    congr 1
    ring

noncomputable def physicalCoordinateEmbeddingCLM (coordinate : Fin 3) :
    ℝ →L[ℝ] SpatialCell :=
  (physicalCoordinateEmbeddingLinear coordinate).toContinuousLinearMap

@[simp] theorem physicalCoordinateEmbeddingCLM_apply
    (coordinate : Fin 3) (value : ℝ) :
    physicalCoordinateEmbeddingCLM coordinate value =
      (physicalCoordinatePeriod coordinate * value) •
        spatialCellBasis coordinate := rfl

@[simp] theorem physicalCoordinateEmbeddingCLM_one (coordinate : Fin 3) :
    physicalCoordinateEmbeddingCLM coordinate 1 =
      physicalCoordinatePeriod coordinate • spatialCellBasis coordinate := by
  simp

theorem physicalPointFromNormalized_insertNth (coordinate : Fin 3)
    (rest : Fin 2 → ℝ) (value : ℝ) :
    physicalPointFromNormalized (coordinate.insertNth value rest) =
      physicalCoordinateEmbeddingCLM coordinate value +
        physicalPointFromNormalized (coordinate.insertNth 0 rest) := by
  ext index
  by_cases same : index = coordinate
  · subst index
    simp [physicalPointFromNormalized, physicalCoordinateEmbeddingCLM,
      physicalCoordinateEmbeddingLinear, spatialCellBasis]
  · obtain ⟨other, rfl⟩ := Fin.exists_succAbove_eq same
    simp [physicalPointFromNormalized, physicalCoordinateEmbeddingCLM,
      physicalCoordinateEmbeddingLinear, spatialCellBasis]

theorem physicalPointFromNormalized_insertNth_hasFDerivAt
    (coordinate : Fin 3) (rest : Fin 2 → ℝ) (value : ℝ) :
    HasFDerivAt
      (fun candidate : ℝ =>
        physicalPointFromNormalized (coordinate.insertNth candidate rest))
      (physicalCoordinateEmbeddingCLM coordinate) value := by
  have functionIdentity :
      (fun candidate : ℝ =>
        physicalPointFromNormalized (coordinate.insertNth candidate rest)) =
      fun candidate => physicalCoordinateEmbeddingCLM coordinate candidate +
        physicalPointFromNormalized (coordinate.insertNth 0 rest) := by
    funext candidate
    exact physicalPointFromNormalized_insertNth coordinate rest candidate
  rw [functionIdentity]
  exact (physicalCoordinateEmbeddingCLM coordinate).hasFDerivAt.add_const _

/-- Along one normalized real coordinate, the derivative of an actual
physical mixed derivative gains the corresponding physical period. -/
theorem mixedCartesianDerivative_normalizedCoordinate_hasDerivAt
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (rest : Fin 2 → ℝ) (value : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        mixedCartesianDerivative order word (torusCellLift field.value)
          (physicalPointFromNormalized
            (coordinate.insertNth candidate rest)))
      (physicalCoordinatePeriod coordinate •
        mixedCartesianDerivative (order + 1) (Fin.cons coordinate word)
          (torusCellLift field.value)
          (physicalPointFromNormalized
            (coordinate.insertNth value rest))) value := by
  let point := physicalPointFromNormalized
    (coordinate.insertNth value rest)
  have smoothAt := field.smoothLift.contDiffAt (x := point)
  have tensorDifferentiable := smoothAt.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
  have evaluatedDifferentiable : DifferentiableAt ℝ
      (fun ambient => mixedCartesianDerivative order word
        (torusCellLift field.value) ambient) point :=
    tensorDifferentiable.continuousMultilinear_apply_const
      (fun position => spatialCellBasis (word position))
  have composed := evaluatedDifferentiable.hasFDerivAt.comp value
    (physicalPointFromNormalized_insertNth_hasFDerivAt coordinate rest value)
  have derivativeValue :
      ((fderiv ℝ
          (fun ambient => mixedCartesianDerivative order word
            (torusCellLift field.value) ambient) point).comp
            (physicalCoordinateEmbeddingCLM coordinate)) 1 =
        physicalCoordinatePeriod coordinate •
          mixedCartesianDerivative (order + 1) (Fin.cons coordinate word)
            (torusCellLift field.value) point := by
    rw [ContinuousLinearMap.comp_apply,
      physicalCoordinateEmbeddingCLM_one, map_smul]
    congr 1
    exact (tensorDifferentiable.iteratedFDeriv_succ_apply_left'
      (m := Fin.cons (spatialCellBasis coordinate)
        (fun position => spatialCellBasis (word position)))).symm
  exact composed.hasDerivAt.congr_deriv derivativeValue

/-- The chosen P09 continuous extension of one actual physical mixed
derivative, transported to the normalized product torus. -/
def normalizedMixedDerivative {dimension order : ℕ}
    (field : TorusSmoothField dimension) (word : MixedCartesianWord order) :
    C(ProductTorus, ComplexEuclidean dimension) :=
  (torusDerivative field order word).comp
    ⟨torusCellToProduct.symm, torusCellToProduct.symm.continuous⟩

theorem normalizedMixedDerivative_insertNth_real
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (rest : Fin 2 → ℝ) (value : ℝ) :
    normalizedMixedDerivative field word
        (coordinate.insertNth (value : UnitAddCircle)
          (fun index => (rest index : UnitAddCircle))) =
      mixedCartesianDerivative order word (torusCellLift field.value)
        (physicalPointFromNormalized
          (coordinate.insertNth value rest)) := by
  change torusDerivative field order word
      (torusCellToProduct.symm
        (coordinate.insertNth (value : UnitAddCircle)
          (fun index => (rest index : UnitAddCircle)))) = _
  rw [torusCellToProduct_symm_insertNth_real,
    torusDerivative_spec]

theorem normalizedMixedDerivative_coordinate_hasDerivAt
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (rest : Fin 2 → ℝ) (value : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        normalizedMixedDerivative field word
          (coordinate.insertNth (candidate : UnitAddCircle)
            (fun index => (rest index : UnitAddCircle))))
      (physicalCoordinatePeriod coordinate •
        normalizedMixedDerivative field (Fin.cons coordinate word)
          (coordinate.insertNth (value : UnitAddCircle)
            (fun index => (rest index : UnitAddCircle)))) value := by
  simpa only [normalizedMixedDerivative_insertNth_real] using
    mixedCartesianDerivative_normalizedCoordinate_hasDerivAt
      field word coordinate rest value

theorem normalizedMixedDerivative_zero {dimension : ℕ}
    (field : TorusSmoothField dimension) :
    normalizedMixedDerivative field emptyMixedCartesianWord =
      torusSmoothNormalizedValue field := by
  have zeroDerivative :
      torusDerivative field 0 emptyMixedCartesianWord = field.value := by
    symm
    apply torusDerivative_unique field 0 emptyMixedCartesianWord field.value
    intro point
    rfl
  exact congrArg
    (fun value : C(TorusCellDomain, ComplexEuclidean dimension) =>
      value.comp ⟨torusCellToProduct.symm,
        torusCellToProduct.symm.continuous⟩) zeroDerivative

/-- One-dimensional integration by parts on a normalized coordinate slice.
The physical period is left explicit, so this is the exact bridge from the
P09 physical derivatives to the normalized product-torus character. -/
theorem fourierCoeff_normalizedMixedDerivative_insertNth_real
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (rest : Fin 2 → ℝ) (frequency : ℤ) :
    (physicalCoordinatePeriod coordinate : ℂ) •
        fourierCoeff
          (fun circle : UnitAddCircle =>
            normalizedMixedDerivative field (Fin.cons coordinate word)
              (coordinate.insertNth circle
                (fun index => (rest index : UnitAddCircle)))) frequency =
      (2 * Real.pi * Complex.I * (frequency : ℂ)) •
        fourierCoeff
          (fun circle : UnitAddCircle =>
            normalizedMixedDerivative field word
              (coordinate.insertNth circle
                (fun index => (rest index : UnitAddCircle)))) frequency := by
  let oldValue : ℝ → ComplexEuclidean dimension := fun value =>
    normalizedMixedDerivative field word
      (coordinate.insertNth (value : UnitAddCircle)
        (fun index => (rest index : UnitAddCircle)))
  let newValue : ℝ → ComplexEuclidean dimension := fun value =>
    normalizedMixedDerivative field (Fin.cons coordinate word)
      (coordinate.insertNth (value : UnitAddCircle)
        (fun index => (rest index : UnitAddCircle)))
  let character : ℝ → ℂ := fun value =>
    fourier (-frequency) (value : UnitAddCircle)
  let characterDerivative : ℝ → ℂ := fun value =>
    (-2 * Real.pi * Complex.I * (frequency : ℂ)) * character value
  have oldDerivative : ∀ value : ℝ,
      HasDerivAt oldValue
        (physicalCoordinatePeriod coordinate • newValue value) value := by
    intro value
    exact normalizedMixedDerivative_coordinate_hasDerivAt
      field word coordinate rest value
  have characterHasDerivative : ∀ value : ℝ,
      HasDerivAt character (characterDerivative value) value := by
    intro value
    simpa [character, characterDerivative] using
      (hasDerivAt_fourier_neg 1 frequency value)
  have torusCurveContinuous : Continuous
      (fun value : ℝ =>
        (coordinate.insertNth (value : UnitAddCircle)
          (fun index => (rest index : UnitAddCircle)) : ProductTorus)) := by
    apply continuous_pi
    intro index
    refine coordinate.succAboveCases ?_ (fun other => ?_) index
    · simpa using (AddCircle.continuous_mk' 1)
    · simpa using (continuous_const : Continuous
        (fun _ : ℝ => (rest other : UnitAddCircle)))
  have oldContinuous : Continuous oldValue :=
    (normalizedMixedDerivative field word).continuous.comp
      torusCurveContinuous
  have newContinuous : Continuous newValue :=
    (normalizedMixedDerivative field (Fin.cons coordinate word)).continuous.comp
      torusCurveContinuous
  have scaledNewContinuous : Continuous
      (fun value => physicalCoordinatePeriod coordinate • newValue value) :=
    (continuous_const : Continuous
      (fun _ : ℝ => physicalCoordinatePeriod coordinate)).smul newContinuous
  have characterDerivativeContinuous : Continuous characterDerivative := by
    dsimp [characterDerivative]
    fun_prop
  have parts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := 0) (b := 1)
    (fun value _ => characterHasDerivative value)
    (fun value _ => oldDerivative value)
    (characterDerivativeContinuous.intervalIntegrable _ _)
    (scaledNewContinuous.intervalIntegrable _ _)
  have endpointCircle : ((1 : ℝ) : UnitAddCircle) =
      ((0 : ℝ) : UnitAddCircle) := by
    simpa only [zero_add] using AddCircle.coe_add_period 1 (0 : ℝ)
  have integralIdentity :
      (physicalCoordinatePeriod coordinate : ℂ) •
          (∫ value in (0 : ℝ)..1,
            character value • newValue value) =
        (2 * Real.pi * Complex.I * (frequency : ℂ)) •
          (∫ value in (0 : ℝ)..1,
            character value • oldValue value) := by
    have oldEndpoint : oldValue 1 = oldValue 0 := by
      simp only [oldValue, endpointCircle]
    have characterEndpoint : character 1 = character 0 := by
      simp only [character, endpointCircle]
    rw [oldEndpoint, characterEndpoint] at parts
    simp only [sub_self, zero_sub] at parts
    have derivativeIntegral :
        (∫ value in (0 : ℝ)..1,
          characterDerivative value • oldValue value) =
        -(2 * Real.pi * Complex.I * (frequency : ℂ)) •
          (∫ value in (0 : ℝ)..1,
            character value • oldValue value) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro value _membership
      simp only [characterDerivative, neg_mul, neg_smul, mul_smul]
    rw [derivativeIntegral] at parts
    have scaledIntegral :
        (∫ value in (0 : ℝ)..1,
          character value •
            (physicalCoordinatePeriod coordinate • newValue value)) =
        (physicalCoordinatePeriod coordinate : ℂ) •
          (∫ value in (0 : ℝ)..1,
            character value • newValue value) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro value _membership
      change character value •
          (physicalCoordinatePeriod coordinate • newValue value) =
        (physicalCoordinatePeriod coordinate : ℂ) •
          (character value • newValue value)
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simp only [smul_smul]
      rw [mul_comm]
      rfl
    rw [scaledIntegral] at parts
    simpa only [neg_smul, neg_neg] using parts
  rw [fourierCoeff_eq_intervalIntegral _ _ 0,
    fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, div_one, one_smul]
  exact integralIdentity

theorem fourierCoeff_normalizedMixedDerivative_insertNth
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (rest : Fin 2 → UnitAddCircle) (frequency : ℤ) :
    (physicalCoordinatePeriod coordinate : ℂ) •
        fourierCoeff
          (fun circle : UnitAddCircle =>
            normalizedMixedDerivative field (Fin.cons coordinate word)
              (coordinate.insertNth circle rest)) frequency =
      (2 * Real.pi * Complex.I * (frequency : ℂ)) •
        fourierCoeff
          (fun circle : UnitAddCircle =>
            normalizedMixedDerivative field word
              (coordinate.insertNth circle rest)) frequency := by
  have representatives : ∀ index : Fin 2, ∃ value : ℝ,
      (value : UnitAddCircle) = rest index := by
    intro index
    exact QuotientAddGroup.mk_surjective (rest index)
  choose realRest realRest_spec using representatives
  have restIdentity : (fun index => (realRest index : UnitAddCircle)) = rest := by
    funext index
    exact realRest_spec index
  rw [← restIdentity]
  exact fourierCoeff_normalizedMixedDerivative_insertNth_real
    field word coordinate realRest frequency

def remainingTorusCharacter (coordinate : Fin 3)
    (index : Fin 3 → ℤ) (rest : Fin 2 → UnitAddCircle) : ℂ :=
  ∏ other : Fin 2, fourier (-(index (coordinate.succAbove other))) (rest other)

theorem mFourier_insertNth (coordinate : Fin 3) (index : Fin 3 → ℤ)
    (circle : UnitAddCircle) (rest : Fin 2 → UnitAddCircle) :
    UnitAddTorus.mFourier (-index) (coordinate.insertNth circle rest) =
      fourier (-(index coordinate)) circle *
        remainingTorusCharacter coordinate index rest := by
  simp only [UnitAddTorus.mFourier, Pi.neg_apply,
    ContinuousMap.coe_mk, remainingTorusCharacter]
  rw [coordinate.prod_univ_succAbove]
  simp

/-- Fubini decomposition of a product-torus Fourier coefficient along one
chosen coordinate. -/
theorem mFourierCoeff_split_coordinate {dimension : ℕ}
    (field : C(ProductTorus, ComplexEuclidean dimension))
    (coordinate : Fin 3) (index : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff field index =
      ∫ rest : Fin 2 → UnitAddCircle,
        remainingTorusCharacter coordinate index rest •
          fourierCoeff
            (fun circle : UnitAddCircle =>
              field (coordinate.insertNth circle rest))
            (index coordinate) := by
  let equivalence := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => UnitAddCircle) coordinate
  let integrand : C(ProductTorus, ComplexEuclidean dimension) :=
    ⟨fun point => UnitAddTorus.mFourier (-index) point • field point,
      (UnitAddTorus.mFourier (-index)).continuous.smul field.continuous⟩
  have integrableSource : Integrable integrand :=
    productTorus_continuousMap_integrable integrand
  have integrableSplit : Integrable
      (fun pair : UnitAddCircle × (Fin 2 → UnitAddCircle) =>
        integrand (equivalence.symm pair)) :=
    MeasurePreserving.integrable_comp_of_integrable
      ((productTorus_piFinSuccAbove_measurePreserving coordinate).symm)
      integrableSource
  unfold UnitAddTorus.mFourierCoeff
  calc
    (∫ point : ProductTorus,
        UnitAddTorus.mFourier (-index) point • field point) =
        ∫ pair : UnitAddCircle × (Fin 2 → UnitAddCircle),
          integrand (equivalence.symm pair) := by
      simpa [equivalence, integrand, Fin.insertNthEquiv,
        Fin.insertNth_self_removeNth] using
        (productTorus_piFinSuccAbove_measurePreserving coordinate).integral_comp'
          (fun pair : UnitAddCircle × (Fin 2 → UnitAddCircle) =>
            integrand (equivalence.symm pair))
    _ = ∫ rest : Fin 2 → UnitAddCircle,
        ∫ circle : UnitAddCircle,
          integrand (equivalence.symm (circle, rest)) := by
      exact integral_prod_symm _ integrableSplit
    _ = ∫ rest : Fin 2 → UnitAddCircle,
        remainingTorusCharacter coordinate index rest •
          fourierCoeff
            (fun circle : UnitAddCircle =>
              field (coordinate.insertNth circle rest))
            (index coordinate) := by
      apply integral_congr_ae
      filter_upwards [] with rest
      simp only [equivalence,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk]
      simp only [fourierCoeff]
      change (∫ circle : UnitAddCircle,
          UnitAddTorus.mFourier (-index)
              (coordinate.insertNth circle rest) •
            field (coordinate.insertNth circle rest)) =
        remainingTorusCharacter coordinate index rest •
          ∫ circle : UnitAddCircle,
            fourier (-(index coordinate)) circle •
              field (coordinate.insertNth circle rest)
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with circle
      rw [mFourier_insertNth]
      simp only [smul_smul]
      rw [mul_comm]

theorem normalizedMixedDerivative_coefficient_scaled
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (index : Fin 3 → ℤ) :
    (physicalCoordinatePeriod coordinate : ℂ) •
        UnitAddTorus.mFourierCoeff
          (normalizedMixedDerivative field (Fin.cons coordinate word)) index =
      (2 * Real.pi * Complex.I * (index coordinate : ℂ)) •
        UnitAddTorus.mFourierCoeff
          (normalizedMixedDerivative field word) index := by
  rw [mFourierCoeff_split_coordinate, mFourierCoeff_split_coordinate,
    ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with rest
  have slice := fourierCoeff_normalizedMixedDerivative_insertNth
    field word coordinate rest (index coordinate)
  calc
    (physicalCoordinatePeriod coordinate : ℂ) •
        (remainingTorusCharacter coordinate index rest •
          fourierCoeff
            (fun circle : UnitAddCircle =>
              normalizedMixedDerivative field (Fin.cons coordinate word)
                (coordinate.insertNth circle rest))
            (index coordinate)) =
      remainingTorusCharacter coordinate index rest •
        ((physicalCoordinatePeriod coordinate : ℂ) •
          fourierCoeff
            (fun circle : UnitAddCircle =>
              normalizedMixedDerivative field (Fin.cons coordinate word)
                (coordinate.insertNth circle rest))
            (index coordinate)) := by
        simp only [smul_smul]
        rw [mul_comm]
    _ = remainingTorusCharacter coordinate index rest •
        ((2 * Real.pi * Complex.I * (index coordinate : ℂ)) •
          fourierCoeff
            (fun circle : UnitAddCircle =>
              normalizedMixedDerivative field word
                (coordinate.insertNth circle rest))
            (index coordinate)) := congrArg _ slice
    _ = (2 * Real.pi * Complex.I * (index coordinate : ℂ)) •
        (remainingTorusCharacter coordinate index rest •
          fourierCoeff
            (fun circle : UnitAddCircle =>
              normalizedMixedDerivative field word
                (coordinate.insertNth circle rest))
            (index coordinate)) := by
        simp only [smul_smul]
        rw [mul_comm]

theorem physicalCoordinatePeriod_mul_partialFrequencyFactor
    (coordinate : Fin 3) (mode : FourierMode) :
    (physicalCoordinatePeriod coordinate : ℂ) *
        partialFrequencyFactor coordinate mode =
      2 * Real.pi * Complex.I * (modeVector mode coordinate : ℂ) := by
  fin_cases coordinate <;>
    simp [physicalCoordinatePeriod, partialFrequencyFactor,
      frequencyVector, modeVector] <;> ring

/-- Exact Fourier multiplier recurrence for the actual P09 physical
derivatives of an arbitrary smooth torus field. -/
theorem normalizedMixedDerivative_coefficient_prepend
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (coordinate : Fin 3)
    (mode : FourierMode) :
    UnitAddTorus.mFourierCoeff
        (normalizedMixedDerivative field (Fin.cons coordinate word))
        (modeVector mode) =
      partialFrequencyFactor coordinate mode •
        UnitAddTorus.mFourierCoeff
          (normalizedMixedDerivative field word) (modeVector mode) := by
  have scaled := normalizedMixedDerivative_coefficient_scaled
    field word coordinate (modeVector mode)
  rw [← physicalCoordinatePeriod_mul_partialFrequencyFactor] at scaled
  have periodNonzero : (physicalCoordinatePeriod coordinate : ℂ) ≠ 0 := by
    exact_mod_cast (physicalCoordinatePeriod_pos coordinate).ne'
  have cancelled := congrArg
    (fun value : ComplexEuclidean dimension =>
      (physicalCoordinatePeriod coordinate : ℂ)⁻¹ • value) scaled
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ periodNonzero,
    one_mul, one_smul] using cancelled

/-- Coefficients of every ordered actual physical derivative are obtained by
the product of the exact physical frequency factors. -/
theorem normalizedMixedDerivative_coefficient_word
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (word : MixedCartesianWord order) (mode : FourierMode) :
    UnitAddTorus.mFourierCoeff
        (normalizedMixedDerivative field word) (modeVector mode) =
      (∏ position : Fin order,
        partialFrequencyFactor (word position) mode) •
        UnitAddTorus.mFourierCoeff
          (torusSmoothNormalizedValue field) (modeVector mode) := by
  induction order with
  | zero =>
      have wordIdentity : word = emptyMixedCartesianWord :=
        Subsingleton.elim _ _
      rw [wordIdentity]
      rw [normalizedMixedDerivative_zero]
      simp
  | succ order inductionHypothesis =>
      have wordIdentity : word = Fin.cons (word 0) (Fin.tail word) := by
        funext position
        refine Fin.cases ?_ (fun other => ?_) position
        · rfl
        · rfl
      rw [wordIdentity,
        normalizedMixedDerivative_coefficient_prepend,
        inductionHypothesis]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_smul]

theorem diskCellMultiIndexWord_frequency_product
    (index : DiskCellMultiIndex) (mode : FourierMode) :
    (∏ position : Fin (diskCellOrder index),
      partialFrequencyFactor (diskCellMultiIndexWord index position) mode) =
      mixedFrequencyFactor index mode := by
  rw [← List.prod_ofFn]
  calc
    (List.ofFn fun position =>
        partialFrequencyFactor (diskCellMultiIndexWord index position) mode).prod =
      ((List.ofFn (diskCellMultiIndexWord index)).map
        (fun coordinate => partialFrequencyFactor coordinate mode)).prod := by
        exact congrArg List.prod
          (List.ofFn_comp' (diskCellMultiIndexWord index)
            (fun coordinate => partialFrequencyFactor coordinate mode))
    _ = mixedFrequencyFactor index mode := by
      rw [list_ofFn_diskCellMultiIndexWord]
      simp [mixedFrequencyFactor]
      ring

theorem normalizedDiskCellDerivative_coefficient
    {dimension : ℕ} (field : TorusSmoothField dimension)
    (index : DiskCellMultiIndex) (mode : FourierMode) :
    UnitAddTorus.mFourierCoeff
        (normalizedMixedDerivative field (diskCellMultiIndexWord index))
        (modeVector mode) =
      mixedFrequencyFactor index mode •
        UnitAddTorus.mFourierCoeff
          (torusSmoothNormalizedValue field) (modeVector mode) := by
  rw [normalizedMixedDerivative_coefficient_word,
    diskCellMultiIndexWord_frequency_product]

end Grad.COR12Extension
