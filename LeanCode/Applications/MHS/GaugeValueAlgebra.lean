import GaugeTriangularAlgebra

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

/-- The two literal Cartesian basis vectors of the complexified plane. -/
def planarBasis (index : Fin 2) : ComplexEuclidean 2 :=
  WithLp.toLp 2 (Pi.single index 1)

theorem planarBasis_apply (index coordinate : Fin 2) :
    planarBasis index coordinate = if coordinate = index then 1 else 0 := by
  simp [planarBasis]

theorem planarBasis_norm (index : Fin 2) : ‖planarBasis index‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  fin_cases index <;>
    · simp only [Fin.sum_univ_two, planarBasis_apply]
      norm_num

theorem planar_decomposition (value : ComplexEuclidean 2) :
    value = value 0 • planarBasis 0 + value 1 • planarBasis 1 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarBasis_apply]

/-- The literal `(row, column)` scalar entry of a planar operator. -/
def operatorEntry (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (row column : Fin 2) : ℂ :=
  mapping (planarBasis column) row

theorem operator_apply_coordinates (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (value : ComplexEuclidean 2) (row : Fin 2) :
    mapping value row =
      operatorEntry mapping row 0 * value 0 + operatorEntry mapping row 1 * value 1 := by
  conv_lhs => rw [planar_decomposition value]
  rw [map_add, map_smul, map_smul]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, operatorEntry]
  ring

theorem operatorEntry_norm_le (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (row column : Fin 2) : ‖operatorEntry mapping row column‖ ≤ ‖mapping‖ :=
  (PiLp.norm_apply_le _ row).trans ((mapping.le_opNorm _).trans_eq
    (by rw [planarBasis_norm, mul_one]))

theorem operatorEntry_add (first second : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (row column : Fin 2) :
    operatorEntry (first + second) row column =
      operatorEntry first row column + operatorEntry second row column := by
  simp [operatorEntry]

theorem operatorEntry_smul (scalar : ℂ) (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (row column : Fin 2) :
    operatorEntry (scalar • mapping) row column = scalar * operatorEntry mapping row column := by
  simp [operatorEntry]

theorem operatorEntry_comp (first second : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (row column : Fin 2) :
    operatorEntry (first.comp second) row column =
      operatorEntry first row 0 * operatorEntry second 0 column +
        operatorEntry first row 1 * operatorEntry second 1 column := by
  unfold operatorEntry
  rw [ContinuousLinearMap.comp_apply, operator_apply_coordinates]
  rfl

theorem planar_norm_le_coordinates (value : ComplexEuclidean 2) :
    ‖value‖ ≤ ‖value 0‖ + ‖value 1‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_two]
  have square : ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2 ≤ (‖value 0‖ + ‖value 1‖) ^ 2 := by
    nlinarith [norm_nonneg (value 0), norm_nonneg (value 1)]
  calc Real.sqrt (‖value 0‖ ^ 2 + ‖value 1‖ ^ 2)
      ≤ Real.sqrt ((‖value 0‖ + ‖value 1‖) ^ 2) := Real.sqrt_le_sqrt square
    _ = ‖value 0‖ + ‖value 1‖ := Real.sqrt_sq (by positivity)

/-- The conjugation-free algebraic transpose of a planar operator. -/
def transposeLinear :
    (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) →ₗ[ℂ]
      (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) where
  toFun mapping := LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2
        ![operatorEntry mapping 0 0 * value 0 + operatorEntry mapping 1 0 * value 1,
          operatorEntry mapping 0 1 * value 0 + operatorEntry mapping 1 1 * value 1]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp <;> ring
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp <;> ring }
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [LinearMap.toContinuousLinearMap, operatorEntry_add] <;> ring
  map_smul' scalar mapping := by
    apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [LinearMap.toContinuousLinearMap, operatorEntry_smul] <;> ring

def transposeOperator (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  transposeLinear mapping

theorem transposeOperator_apply (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (value : ComplexEuclidean 2) :
    transposeOperator mapping value = WithLp.toLp 2
      ![operatorEntry mapping 0 0 * value 0 + operatorEntry mapping 1 0 * value 1,
        operatorEntry mapping 0 1 * value 0 + operatorEntry mapping 1 1 * value 1] := rfl

theorem transposeOperator_entry (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (row column : Fin 2) :
    operatorEntry (transposeOperator mapping) row column = operatorEntry mapping column row := by
  conv_lhs => unfold operatorEntry
  rw [transposeOperator_apply]
  fin_cases row <;> fin_cases column <;>
    simp [planarBasis_apply, operatorEntry]

theorem transposeOperator_norm_le (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    ‖transposeOperator mapping‖ ≤ 4 * ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro value
  have coordinateZero : ‖transposeOperator mapping value 0‖ ≤
      ‖mapping‖ * ‖value 0‖ + ‖mapping‖ * ‖value 1‖ := by
    rw [transposeOperator_apply]
    refine le_trans ?_ (add_le_add
      (mul_le_mul_of_nonneg_right (operatorEntry_norm_le mapping 0 0) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (operatorEntry_norm_le mapping 1 0) (norm_nonneg _)))
    simpa using norm_add_le (operatorEntry mapping 0 0 * value 0)
      (operatorEntry mapping 1 0 * value 1)
  have coordinateOne : ‖transposeOperator mapping value 1‖ ≤
      ‖mapping‖ * ‖value 0‖ + ‖mapping‖ * ‖value 1‖ := by
    rw [transposeOperator_apply]
    refine le_trans ?_ (add_le_add
      (mul_le_mul_of_nonneg_right (operatorEntry_norm_le mapping 0 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (operatorEntry_norm_le mapping 1 1) (norm_nonneg _)))
    simpa using norm_add_le (operatorEntry mapping 0 1 * value 0)
      (operatorEntry mapping 1 1 * value 1)
  have valueZero := PiLp.norm_apply_le value 0
  have valueOne := PiLp.norm_apply_le value 1
  have mappingNonnegative := norm_nonneg mapping
  calc ‖transposeOperator mapping value‖
      ≤ ‖transposeOperator mapping value 0‖ + ‖transposeOperator mapping value 1‖ :=
        planar_norm_le_coordinates _
    _ ≤ 4 * ‖mapping‖ * ‖value‖ := by nlinarith

def transposeContinuous :
    (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) →L[ℂ]
      (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :=
  transposeLinear.mkContinuous 4 (fun mapping => transposeOperator_norm_le mapping)

@[simp] theorem transposeContinuous_apply (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    transposeContinuous mapping = transposeOperator mapping := rfl

/-- The algebraic operator trace on the complexified plane. -/
def operatorTrace (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) : ℂ :=
  operatorEntry mapping 0 0 + operatorEntry mapping 1 1

theorem operatorTrace_norm_le (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    ‖operatorTrace mapping‖ ≤ 2 * ‖mapping‖ := by
  have zeroBound := operatorEntry_norm_le mapping 0 0
  have oneBound := operatorEntry_norm_le mapping 1 1
  calc ‖operatorTrace mapping‖
      ≤ ‖operatorEntry mapping 0 0‖ + ‖operatorEntry mapping 1 1‖ := norm_add_le _ _
    _ ≤ 2 * ‖mapping‖ := by linarith

def operatorTraceLinear : (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) →ₗ[ℂ] ℂ where
  toFun := operatorTrace
  map_add' first second := by
    unfold operatorTrace
    rw [operatorEntry_add, operatorEntry_add]
    ring
  map_smul' scalar mapping := by
    unfold operatorTrace
    rw [operatorEntry_smul, operatorEntry_smul]
    simp
    ring

def operatorTraceContinuous : (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) →L[ℂ] ℂ :=
  operatorTraceLinear.mkContinuous 2 (fun mapping => operatorTrace_norm_le mapping)

@[simp] theorem operatorTraceContinuous_apply
    (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    operatorTraceContinuous mapping = operatorTrace mapping := rfl

theorem operatorTrace_id : operatorTrace (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) = 2 := by
  unfold operatorTrace operatorEntry
  simp [planarBasis_apply]
  norm_num

theorem operatorTrace_comp_norm_le (first second : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    ‖operatorTrace (first.comp second)‖ ≤ 2 * (‖first‖ * ‖second‖) :=
  (operatorTrace_norm_le _).trans (by
    have := first.opNorm_comp_le second
    have firstNonnegative := norm_nonneg first
    have secondNonnegative := norm_nonneg second
    nlinarith)

/-- The positive-helicity diagonal coefficient of a planar operator. -/
def alphaPlus (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) : ℂ :=
  (operatorEntry mapping 0 0 + operatorEntry mapping 1 1 +
    Complex.I * (operatorEntry mapping 1 0 - operatorEntry mapping 0 1)) / 2

/-- The negative-helicity diagonal coefficient of a planar operator. -/
def alphaMinus (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) : ℂ :=
  (operatorEntry mapping 0 0 + operatorEntry mapping 1 1 -
    Complex.I * (operatorEntry mapping 1 0 - operatorEntry mapping 0 1)) / 2

theorem alphaPlus_add_alphaMinus (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    alphaPlus mapping + alphaMinus mapping = operatorTrace mapping := by
  unfold alphaPlus alphaMinus operatorTrace
  ring

theorem positiveHelicity_conjugation (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    positiveHelicity.comp (mapping.comp positiveHelicity) = alphaPlus mapping • positiveHelicity := by
  apply ContinuousLinearMap.ext
  intro value
  have projectedZero : (positiveHelicity value) 0 = (value 0 + Complex.I * value 1) / 2 := by
    rw [positiveHelicity_apply]
    simp
  have projectedOne : (positiveHelicity value) 1 = (value 1 - Complex.I * value 0) / 2 := by
    rw [positiveHelicity_apply]
    simp
  have innerZero := operator_apply_coordinates mapping (positiveHelicity value) 0
  have innerOne := operator_apply_coordinates mapping (positiveHelicity value) 1
  rw [projectedZero, projectedOne] at innerZero innerOne
  apply PiLp.ext
  intro coordinate
  have outer := positiveHelicity_apply (mapping (positiveHelicity value))
  fin_cases coordinate
  · show (positiveHelicity (mapping (positiveHelicity value))) 0 =
      (alphaPlus mapping • positiveHelicity value) 0
    rw [outer]
    simp only [PiLp.smul_apply, smul_eq_mul, projectedZero]
    show (mapping (positiveHelicity value) 0 + Complex.I * mapping (positiveHelicity value) 1) / 2 = _
    rw [innerZero, innerOne]
    unfold alphaPlus
    ring_nf
    simp [Complex.I_sq]
    ring
  · show (positiveHelicity (mapping (positiveHelicity value))) 1 =
      (alphaPlus mapping • positiveHelicity value) 1
    rw [outer]
    simp only [PiLp.smul_apply, smul_eq_mul, projectedOne]
    show (mapping (positiveHelicity value) 1 - Complex.I * mapping (positiveHelicity value) 0) / 2 = _
    rw [innerZero, innerOne]
    unfold alphaPlus
    ring_nf
    simp [Complex.I_sq]
    ring

theorem negativeHelicity_conjugation (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    negativeHelicity.comp (mapping.comp negativeHelicity) = alphaMinus mapping • negativeHelicity := by
  apply ContinuousLinearMap.ext
  intro value
  have projectedZero : (negativeHelicity value) 0 = (value 0 - Complex.I * value 1) / 2 := by
    rw [negativeHelicity_apply]
    simp
  have projectedOne : (negativeHelicity value) 1 = (value 1 + Complex.I * value 0) / 2 := by
    rw [negativeHelicity_apply]
    simp
  have innerZero := operator_apply_coordinates mapping (negativeHelicity value) 0
  have innerOne := operator_apply_coordinates mapping (negativeHelicity value) 1
  rw [projectedZero, projectedOne] at innerZero innerOne
  apply PiLp.ext
  intro coordinate
  have outer := negativeHelicity_apply (mapping (negativeHelicity value))
  fin_cases coordinate
  · show (negativeHelicity (mapping (negativeHelicity value))) 0 =
      (alphaMinus mapping • negativeHelicity value) 0
    rw [outer]
    simp only [PiLp.smul_apply, smul_eq_mul, projectedZero]
    show (mapping (negativeHelicity value) 0 - Complex.I * mapping (negativeHelicity value) 1) / 2 = _
    rw [innerZero, innerOne]
    unfold alphaMinus
    ring_nf
    simp [Complex.I_sq]
    ring
  · show (negativeHelicity (mapping (negativeHelicity value))) 1 =
      (alphaMinus mapping • negativeHelicity value) 1
    rw [outer]
    simp only [PiLp.smul_apply, smul_eq_mul, projectedOne]
    show (mapping (negativeHelicity value) 1 + Complex.I * mapping (negativeHelicity value) 0) / 2 = _
    rw [innerZero, innerOne]
    unfold alphaMinus
    ring_nf
    simp [Complex.I_sq]
    ring

end Grad.Constraints.Gauges
