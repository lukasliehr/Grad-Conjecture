import AxisJetSupport

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### Word values, supports and suprema of the phased profiles -/

theorem phasedZero_word_value {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) (index : CartesianMultiIndex)
    (point : ClosedDisk) :
    closedMultiDerivative (phaseWeightedJet parameters cell
        (profileJetZero cell vector)) index point =
      cartesianDerivative (cartesianOrder index) (cartesianMultiIndexWord index)
        (phasedFieldZero (parameters := parameters) cell vector) point.val := by
  rw [phaseWeighted_profileZero]
  change closedDerivative (globalClosedJet
    (phasedFieldZero (parameters := parameters) cell vector)
    (phasedFieldZero_smooth cell vector)) (cartesianOrder index)
    (cartesianMultiIndexWord index) point = _
  exact globalClosedJet_derivative _ _ _ _

theorem phasedOne_word_value {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) (index : CartesianMultiIndex)
    (point : ClosedDisk) :
    closedMultiDerivative (phaseWeightedJet parameters cell
        (profileJetOne coordinate cell vector)) index point =
      cartesianDerivative (cartesianOrder index) (cartesianMultiIndexWord index)
        (phasedFieldOne (parameters := parameters) coordinate cell vector)
        point.val := by
  rw [phaseWeighted_profileOne]
  change closedDerivative (globalClosedJet
    (phasedFieldOne (parameters := parameters) coordinate cell vector)
    (phasedFieldOne_smooth coordinate cell vector)) (cartesianOrder index)
    (cartesianMultiIndexWord index) point = _
  exact globalClosedJet_derivative _ _ _ _

theorem phasedZero_word_vanish {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) (index : CartesianMultiIndex)
    (point : ClosedDisk)
    (outside : point.val ∉ Metric.closedBall (0 : SpatialPlane)
      ((4 * cellFrequency cell)⁻¹)) :
    closedMultiDerivative (phaseWeightedJet parameters cell
        (profileJetZero cell vector)) index point = 0 := by
  rw [phasedZero_word_value]
  have derivativeZero : iteratedFDeriv ℝ (cartesianOrder index)
      (phasedFieldZero (parameters := parameters) cell vector) point.val = 0 := by
    by_contra nonzero
    apply outside
    apply phasedFieldZero_tsupport cell vector
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) (cartesianOrder index)
    exact Function.mem_support.mpr nonzero
  change (iteratedFDeriv ℝ (cartesianOrder index)
    (phasedFieldZero (parameters := parameters) cell vector) point.val)
    (fun position => spatialBasis (cartesianMultiIndexWord index position)) = 0
  rw [derivativeZero]
  rfl

theorem phasedOne_word_vanish {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) (index : CartesianMultiIndex)
    (point : ClosedDisk)
    (outside : point.val ∉ Metric.closedBall (0 : SpatialPlane)
      ((4 * cellFrequency cell)⁻¹)) :
    closedMultiDerivative (phaseWeightedJet parameters cell
        (profileJetOne coordinate cell vector)) index point = 0 := by
  rw [phasedOne_word_value]
  have derivativeZero : iteratedFDeriv ℝ (cartesianOrder index)
      (phasedFieldOne (parameters := parameters) coordinate cell vector)
      point.val = 0 := by
    by_contra nonzero
    apply outside
    apply phasedFieldOne_tsupport coordinate cell vector
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) (cartesianOrder index)
    exact Function.mem_support.mpr nonzero
  change (iteratedFDeriv ℝ (cartesianOrder index)
    (phasedFieldOne (parameters := parameters) coordinate cell vector) point.val)
    (fun position => spatialBasis (cartesianMultiIndexWord index position)) = 0
  rw [derivativeZero]
  rfl

theorem phasedZero_word_sup {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) (index : CartesianMultiIndex)
    (point : ClosedDisk) {wordBound : ℝ}
    (scalarBound : ∀ target : SpatialPlane,
      ‖iteratedFDeriv ℝ (cartesianOrder index) (fun source =>
        cartesianWeight parameters cell source *
          jetBump (cellFrequency cell • source)) target‖ ≤ wordBound) :
    ‖closedMultiDerivative (phaseWeightedJet parameters cell
        (profileJetZero cell vector)) index point‖ ≤ wordBound * ‖vector‖ := by
  rw [phasedZero_word_value]
  have wordNorm := phased_word_norm (fun source =>
      cartesianWeight parameters cell source * profileScalarZero cell source)
    ((cartesianWeight_contDiff parameters cell).mul (profileScalarZero_smooth cell))
    vector (cartesianOrder index) (cartesianMultiIndexWord index) point.val
  apply le_trans wordNorm
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg vector)
  exact scalarBound point.val

theorem phasedOne_word_sup {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) (index : CartesianMultiIndex)
    (point : ClosedDisk) {wordBound : ℝ}
    (scalarBound : ∀ target : SpatialPlane,
      ‖iteratedFDeriv ℝ (cartesianOrder index) (fun source =>
        cartesianWeight parameters cell source *
          (coordinateLinear coordinate (cellFrequency cell • source) *
            jetBump (cellFrequency cell • source))) target‖ ≤ wordBound) :
    ‖closedMultiDerivative (phaseWeightedJet parameters cell
        (profileJetOne coordinate cell vector)) index point‖ ≤
      (cellFrequency cell)⁻¹ * wordBound * ‖vector‖ := by
  rw [phasedOne_word_value]
  have wordNorm := phased_word_norm (fun source =>
      cartesianWeight parameters cell source *
        profileScalarOne coordinate cell source)
    ((cartesianWeight_contDiff parameters cell).mul
      (profileScalarOne_smooth coordinate cell))
    vector (cartesianOrder index) (cartesianMultiIndexWord index) point.val
  apply le_trans wordNorm
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg vector)
  have scalarForm : (fun source => cartesianWeight parameters cell source *
      profileScalarOne coordinate cell source) =
      fun source => (cellFrequency cell)⁻¹ •
        (cartesianWeight parameters cell source *
          (coordinateLinear coordinate (cellFrequency cell • source) *
            jetBump (cellFrequency cell • source))) := by
    funext source
    rw [smul_eq_mul, profileScalarOne_scaled]
    ring
  rw [scalarForm]
  have bigSmooth : ContDiff ℝ ∞ (fun source =>
      cartesianWeight parameters cell source *
        (coordinateLinear coordinate (cellFrequency cell • source) *
          jetBump (cellFrequency cell • source))) :=
    (cartesianWeight_contDiff parameters cell).mul
      ((((coordinateLinear coordinate).contDiff).mul jetBump.contDiff).comp
        (contDiff_id.const_smul (cellFrequency cell)))
  rw [iteratedFDeriv_const_smul_apply'
    (bigSmooth.contDiffAt.of_le (natCast_le_infty (cartesianOrder index)))]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (cellFrequency_pos cell).le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (cellFrequency_pos cell).le)
  exact scalarBound point.val

/-! ### The row through the multi-index content sum -/

/-- The full grade row is dominated by the plain sum of its weighted
`L²` word entries. -/
theorem row_le_content_sum {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ≤
      ∑ index : GradeMultiIndex grade,
        cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
          ‖closedContinuousToDiskL2 (closedMultiDerivative
            (phaseWeightedJet parameters cell field) index.toCartesian)‖ := by
  set summandBound : GradeMultiIndex grade → ℝ := fun index =>
    cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) index.toCartesian)‖ with summandDef
  have rowSquare := cellGradeRow_norm_sq (grade := grade) parameters cell field
  have summandNonneg : ∀ index : GradeMultiIndex grade, 0 ≤ summandBound index := by
    intro index
    exact mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)
  have squareIdentity : ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 =
      ∑ index : GradeMultiIndex grade, summandBound index ^ 2 := by
    rw [rowSquare]
    apply Finset.sum_congr rfl
    intro index _
    rw [summandDef]
    rw [mul_pow, ← pow_mul]
    ring_nf
  have sumSquareLe : (∑ index : GradeMultiIndex grade, summandBound index ^ 2) ≤
      (∑ index : GradeMultiIndex grade, summandBound index) ^ 2 := by
    rw [sq (∑ index : GradeMultiIndex grade, summandBound index), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro index _
    rw [sq]
    apply mul_le_mul_of_nonneg_left _ (summandNonneg index)
    exact Finset.single_le_sum (fun inner _ => summandNonneg inner)
      (Finset.mem_univ index)
  have sqrtStep := Real.sqrt_le_sqrt (squareIdentity.le.trans sumSquareLe)
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (Finset.sum_nonneg (fun index _ => summandNonneg index))] at sqrtStep

/-! ### M30's row bounds for the two literal profiles -/

/-- The value-profile grade row costs the axis weight with one full
inverse-frequency gain, uniformly in the cell and inserted value. -/
theorem profileZero_row_bound (parameters : PhaseParameters) (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (cell : ℤ) (dimension : ℕ)
      (vector : ComplexEuclidean dimension),
      ‖cellGradeRowLinear (grade := grade) parameters cell
          (profileJetZero cell vector)‖ ≤
        bound * (axisWeight parameters grade cell * (cellFrequency cell)⁻¹ *
          ‖vector‖) := by
  choose wordBound wordBoundNonneg wordBoundLe using
    fun order => dilated_product_word_bound (parameters := parameters)
      (⇑jetBump) jetBump.contDiff jetBump.hasCompactSupport order
  refine ⟨(∑ index : GradeMultiIndex grade,
      wordBound (cartesianOrder index.toCartesian)) * (ballVolumeSqrt * 4⁻¹),
    ?_, ?_⟩
  · apply mul_nonneg (Finset.sum_nonneg fun index _ => wordBoundNonneg _)
    exact mul_nonneg ballVolumeSqrt_nonneg (by norm_num)
  intro cell dimension vector
  have lambdaPos : (0 : ℝ) < cellFrequency cell := cellFrequency_pos cell
  have radiusNonneg : (0 : ℝ) ≤ (4 * cellFrequency cell)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (by norm_num) lambdaPos.le)
  apply le_trans (row_le_content_sum parameters cell (profileJetZero cell vector))
  have termBound : ∀ index : GradeMultiIndex grade,
      cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell (profileJetZero cell vector))
          index.toCartesian)‖ ≤
      wordBound (cartesianOrder index.toCartesian) * (ballVolumeSqrt * 4⁻¹) *
        (axisWeight parameters grade cell * (cellFrequency cell)⁻¹ * ‖vector‖) := by
    intro index
    have orderLe : cartesianOrder index.toCartesian ≤ grade := index.property
    have supNonneg : (0 : ℝ) ≤ wordBound (cartesianOrder index.toCartesian) *
        Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ cartesianOrder index.toCartesian * ‖vector‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (wordBoundNonneg _) (Real.exp_pos _).le)
        (pow_nonneg lambdaPos.le _)) (norm_nonneg _)
    have l2Bound : ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell (profileJetZero cell vector))
        index.toCartesian)‖ ≤
        wordBound (cartesianOrder index.toCartesian) *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ cartesianOrder index.toCartesian * ‖vector‖ *
          ((4 * cellFrequency cell)⁻¹ * ballVolumeSqrt) := by
      apply l2_norm_le_sup_ball _ radiusNonneg supNonneg
      · intro point outside
        exact phasedZero_word_vanish cell vector index.toCartesian point outside
      · intro point
        apply phasedZero_word_sup cell vector index.toCartesian point
        intro target
        exact wordBoundLe (cartesianOrder index.toCartesian) cell target
    calc cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell (profileJetZero cell vector))
          index.toCartesian)‖ ≤
        cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
          (wordBound (cartesianOrder index.toCartesian) *
            Real.exp (parameters.sigma0 * cellFrequency cell) *
            cellFrequency cell ^ cartesianOrder index.toCartesian * ‖vector‖ *
            ((4 * cellFrequency cell)⁻¹ * ballVolumeSqrt)) :=
          mul_le_mul_of_nonneg_left l2Bound (pow_nonneg lambdaPos.le _)
      _ = wordBound (cartesianOrder index.toCartesian) * (ballVolumeSqrt * 4⁻¹) *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            (cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
              cellFrequency cell ^ cartesianOrder index.toCartesian) *
            (cellFrequency cell)⁻¹ * ‖vector‖) := by
          rw [mul_inv]
          ring
      _ = wordBound (cartesianOrder index.toCartesian) * (ballVolumeSqrt * 4⁻¹) *
          (axisWeight parameters grade cell * (cellFrequency cell)⁻¹ * ‖vector‖) := by
          rw [← pow_add, Nat.sub_add_cancel orderLe]
          rfl
  apply le_trans (Finset.sum_le_sum (fun index _ => termBound index))
  rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- The coordinate-profile grade row costs the axis weight with two full
inverse-frequency gains, uniformly in the cell and inserted value. -/
theorem profileOne_row_bound (parameters : PhaseParameters) (coordinate : Fin 2)
    (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (cell : ℤ) (dimension : ℕ)
      (vector : ComplexEuclidean dimension),
      ‖cellGradeRowLinear (grade := grade) parameters cell
          (profileJetOne coordinate cell vector)‖ ≤
        bound * (axisWeight parameters grade cell *
          ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) * ‖vector‖) := by
  have productSmooth : ContDiff ℝ ∞ (fun target : SpatialPlane =>
      coordinateLinear coordinate target * jetBump target) :=
    ((coordinateLinear coordinate).contDiff).mul jetBump.contDiff
  have productCompact : HasCompactSupport (fun target : SpatialPlane =>
      coordinateLinear coordinate target * jetBump target) :=
    HasCompactSupport.mul_left jetBump.hasCompactSupport
  choose wordBound wordBoundNonneg wordBoundLe using
    fun order => dilated_product_word_bound (parameters := parameters)
      (fun target => coordinateLinear coordinate target * jetBump target)
      productSmooth productCompact order
  refine ⟨(∑ index : GradeMultiIndex grade,
      wordBound (cartesianOrder index.toCartesian)) * (ballVolumeSqrt * 4⁻¹),
    ?_, ?_⟩
  · apply mul_nonneg (Finset.sum_nonneg fun index _ => wordBoundNonneg _)
    exact mul_nonneg ballVolumeSqrt_nonneg (by norm_num)
  intro cell dimension vector
  have lambdaPos : (0 : ℝ) < cellFrequency cell := cellFrequency_pos cell
  have radiusNonneg : (0 : ℝ) ≤ (4 * cellFrequency cell)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (by norm_num) lambdaPos.le)
  apply le_trans (row_le_content_sum parameters cell
    (profileJetOne coordinate cell vector))
  have termBound : ∀ index : GradeMultiIndex grade,
      cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell (profileJetOne coordinate cell vector))
          index.toCartesian)‖ ≤
      wordBound (cartesianOrder index.toCartesian) * (ballVolumeSqrt * 4⁻¹) *
        (axisWeight parameters grade cell *
          ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) * ‖vector‖) := by
    intro index
    have orderLe : cartesianOrder index.toCartesian ≤ grade := index.property
    have supNonneg : (0 : ℝ) ≤ (cellFrequency cell)⁻¹ *
        (wordBound (cartesianOrder index.toCartesian) *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ cartesianOrder index.toCartesian) * ‖vector‖ :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr lambdaPos.le)
        (mul_nonneg (mul_nonneg (wordBoundNonneg _) (Real.exp_pos _).le)
          (pow_nonneg lambdaPos.le _))) (norm_nonneg _)
    have l2Bound : ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell (profileJetOne coordinate cell vector))
        index.toCartesian)‖ ≤
        (cellFrequency cell)⁻¹ *
          (wordBound (cartesianOrder index.toCartesian) *
            Real.exp (parameters.sigma0 * cellFrequency cell) *
            cellFrequency cell ^ cartesianOrder index.toCartesian) * ‖vector‖ *
          ((4 * cellFrequency cell)⁻¹ * ballVolumeSqrt) := by
      apply l2_norm_le_sup_ball _ radiusNonneg supNonneg
      · intro point outside
        exact phasedOne_word_vanish coordinate cell vector index.toCartesian
          point outside
      · intro point
        apply phasedOne_word_sup coordinate cell vector index.toCartesian point
        intro target
        exact wordBoundLe (cartesianOrder index.toCartesian) cell target
    calc cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell (profileJetOne coordinate cell vector))
          index.toCartesian)‖ ≤
        cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
          ((cellFrequency cell)⁻¹ *
            (wordBound (cartesianOrder index.toCartesian) *
              Real.exp (parameters.sigma0 * cellFrequency cell) *
              cellFrequency cell ^ cartesianOrder index.toCartesian) * ‖vector‖ *
            ((4 * cellFrequency cell)⁻¹ * ballVolumeSqrt)) :=
          mul_le_mul_of_nonneg_left l2Bound (pow_nonneg lambdaPos.le _)
      _ = wordBound (cartesianOrder index.toCartesian) * (ballVolumeSqrt * 4⁻¹) *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            (cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
              cellFrequency cell ^ cartesianOrder index.toCartesian) *
            ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) * ‖vector‖) := by
          rw [mul_inv]
          ring
      _ = wordBound (cartesianOrder index.toCartesian) * (ballVolumeSqrt * 4⁻¹) *
          (axisWeight parameters grade cell *
            ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) * ‖vector‖) := by
          rw [← pow_add, Nat.sub_add_cancel orderLe]
          rfl
  apply le_trans (Finset.sum_le_sum (fun index _ => termBound index))
  rw [← Finset.sum_mul, ← Finset.sum_mul]

end Grad.AxisJet
