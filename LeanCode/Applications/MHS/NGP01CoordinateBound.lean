import FP17Bijection
import FC6Monotone

noncomputable section

set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Grad.CartesianState

open Grad.ClosedJets

local instance ngp01CellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

local instance ngp01ClosedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

/-- The phase-zero grade coordinates bundled in the actual outer `ℓ2` space. -/
def ordinaryGradeCoordinates {dimension : ℕ} (grade : ℕ)
    (coefficients : OrdinaryCoefficientCore dimension) :
    lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2 :=
  ⟨ordinaryRawGradeCoordinates grade coefficients.1,
    coefficients.property grade⟩

/-- The fixed one-cell-frequency loss, bundled in `ℓ2(ℤ)`. -/
def inverseCellFrequencyLp : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun cell => (cellFrequency cell)⁻¹, by
    apply (memlp_iff_summable_sq _).2
    simpa [Real.norm_eq_abs, abs_of_pos (cellFrequency_pos _)] using
      inverseCellFrequency_sq_summable⟩

/-- One fixed A08 coordinate of the M15 grade, as an actual outer `ℓ2`
vector. -/
def m15CoordinateLp {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (slot : Fin 6) :
    lp (fun _ : ℤ => DiskL2 dimension) 2 :=
  ⟨fun cell => ordinaryRawGradeCoordinates (m15Grade word cellOrder)
      coefficients.1 cell (m15GradeIndex (cellOrder := cellOrder) word slot), by
    apply (coefficients.property (m15Grade word cellOrder)).mono'
    intro cell
    exact PiLp.norm_apply_le
      (ordinaryRawGradeCoordinates (m15Grade word cellOrder)
        coefficients.1 cell)
      (m15GradeIndex (cellOrder := cellOrder) word slot)⟩

theorem m15CoordinateLp_norm_le {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (slot : Fin 6) :
    ‖m15CoordinateLp coefficients word cellOrder slot‖ ≤
      ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ := by
  apply lp.norm_mono (by norm_num)
  intro cell
  exact PiLp.norm_apply_le
    (ordinaryRawGradeCoordinates (m15Grade word cellOrder)
      coefficients.1 cell)
    (m15GradeIndex (cellOrder := cellOrder) word slot)

/-- Quantitative Cauchy--Schwarz for the exact outer M15 coordinate. -/
theorem m15_inverse_coordinate_holder {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (slot : Fin 6) :
    Summable (fun cell : ℤ =>
      (cellFrequency cell)⁻¹ *
        ‖m15CoordinateLp coefficients word cellOrder slot cell‖) ∧
    ∑' cell : ℤ,
        (cellFrequency cell)⁻¹ *
          ‖m15CoordinateLp coefficients word cellOrder slot cell‖ ≤
      ‖inverseCellFrequencyLp‖ *
        ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ := by
  let coordinate := m15CoordinateLp coefficients word cellOrder slot
  have inverseHasSum := lp.hasSum_norm (by norm_num) inverseCellFrequencyLp
  have coordinateHasSum := lp.hasSum_norm (by norm_num) coordinate
  obtain ⟨C, Cnonnegative, Cbound, ChasSum⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg
      (show (2 : ℝ).HolderConjugate 2 by
        rw [Real.holderConjugate_iff]
        norm_num)
      (norm_nonneg inverseCellFrequencyLp) (norm_nonneg coordinate)
      (fun cell : ℤ => inv_nonneg.mpr (cellFrequency_pos cell).le)
      (fun cell : ℤ => norm_nonneg (coordinate cell))
      (by simpa [inverseCellFrequencyLp, Real.norm_eq_abs,
          abs_of_pos (cellFrequency_pos _)] using inverseHasSum)
      coordinateHasSum
  constructor
  · simpa [coordinate] using ChasSum.summable
  · rw [show (∑' cell : ℤ,
        (cellFrequency cell)⁻¹ *
          ‖m15CoordinateLp coefficients word cellOrder slot cell‖) = C by
      simpa [coordinate] using ChasSum.tsum_eq]
    exact Cbound.trans (mul_le_mul_of_nonneg_left
      (m15CoordinateLp_norm_le coefficients word cellOrder slot)
      (norm_nonneg inverseCellFrequencyLp))

theorem m15_weightedDerivative_le_inverse_coordinate
    {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (slot : Fin 6)
    (cell : ℤ) :
    cellFrequency cell ^ cellOrder *
        ‖closedDerivativeL2 (diskSupMultiIndex slot)
          (shiftedClosedJet (coefficients.1 cell) word)‖ ≤
      (cellFrequency cell)⁻¹ *
        ‖m15CoordinateLp coefficients word cellOrder slot cell‖ := by
  let grade := m15Grade word cellOrder
  let index : GradeMultiIndex grade :=
    m15GradeIndex (cellOrder := cellOrder) word slot
  have exponentBound := m15GradeIndex_weight_exponent
    (cellOrder := cellOrder) word slot
  have frequencyPowerBound :
      cellFrequency cell ^ (cellOrder + 1) ≤
        cellFrequency cell ^
          (grade - cartesianOrder index.toCartesian) :=
    pow_le_pow_right₀ (cellFrequency_one_le cell) exponentBound
  have derivativeIdentity :
      closedDerivativeL2 (diskSupMultiIndex slot)
          (shiftedClosedJet (coefficients.1 cell) word) =
        closedContinuousToDiskL2
          (closedMultiDerivative (coefficients.1 cell)
            index.toCartesian) := by
    rw [shiftedClosedDerivativeL2_eq_m15Coordinate]
    rw [show index.toCartesian = m15DiskSupIndex word slot by
      exact m15GradeIndex_toCartesian word slot]
  have coordinateNorm :
      ‖m15CoordinateLp coefficients word cellOrder slot cell‖ =
        cellFrequency cell ^
            (grade - cartesianOrder index.toCartesian) *
          ‖closedContinuousToDiskL2
            (closedMultiDerivative (coefficients.1 cell)
              index.toCartesian)‖ := by
    change ‖(cellFrequency cell : ℂ) ^
        (grade - cartesianOrder index.toCartesian) •
          closedContinuousToDiskL2
            (closedMultiDerivative (coefficients.1 cell)
              index.toCartesian)‖ = _
    rw [norm_smul, Complex.norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell)]
  rw [derivativeIdentity, coordinateNorm]
  have frequencyNonzero : cellFrequency cell ≠ 0 :=
    ne_of_gt (cellFrequency_pos cell)
  calc
    cellFrequency cell ^ cellOrder *
          ‖closedContinuousToDiskL2
            (closedMultiDerivative (coefficients.1 cell)
              index.toCartesian)‖ =
        (cellFrequency cell)⁻¹ *
          (cellFrequency cell ^ (cellOrder + 1) *
            ‖closedContinuousToDiskL2
              (closedMultiDerivative (coefficients.1 cell)
                index.toCartesian)‖) := by
      rw [pow_succ]
      field_simp
    _ ≤ (cellFrequency cell)⁻¹ *
          (cellFrequency cell ^
              (grade - cartesianOrder index.toCartesian) *
            ‖closedContinuousToDiskL2
              (closedMultiDerivative (coefficients.1 cell)
                index.toCartesian)‖) := by
      gcongr
      exact inv_nonneg.mpr (cellFrequency_pos cell).le

/-- One A08 derivative coordinate is bounded quantitatively by the exact
ordinary grade norm, with the fixed one-dimensional Cauchy--Schwarz
constant. -/
theorem m15_singleCoordinate_tsum_le {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (slot : Fin 6) :
    ∑' cell : ℤ,
        cellFrequency cell ^ cellOrder *
          ‖closedDerivativeL2 (diskSupMultiIndex slot)
            (shiftedClosedJet (coefficients.1 cell) word)‖ ≤
      ‖inverseCellFrequencyLp‖ *
        ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ := by
  have holder := m15_inverse_coordinate_holder coefficients word cellOrder slot
  exact (m15_singleCoordinate_summable coefficients word cellOrder slot).tsum_le_tsum
    (m15_weightedDerivative_le_inverse_coordinate coefficients word cellOrder slot)
    holder.1 |>.trans holder.2

/-- The uniform constant for the exact three-grade-loss M15 estimate.  The
finite sum is deliberately left literal: its six summands are the six A08
disk-Sobolev coordinates. -/
def m15EvaluationConstant : ℝ :=
  diskSupConstant * ∑ _slot : Fin 6, ‖inverseCellFrequencyLp‖

theorem m15EvaluationConstant_nonneg : 0 ≤ m15EvaluationConstant := by
  exact mul_nonneg diskSupConstant_pos.le
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem m15_frequencyWeighted_sup_le_coordinateSum
    {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (cell : ℤ) :
    cellFrequency cell ^ cellOrder *
        ‖closedDerivative (coefficients.1 cell) order word‖ ≤
      diskSupConstant *
        ∑ slot : Fin 6,
          cellFrequency cell ^ cellOrder *
            ‖closedDerivativeL2 (diskSupMultiIndex slot)
              (shiftedClosedJet (coefficients.1 cell) word)‖ := by
  have derivativeSupBound :
      ‖closedDerivative (coefficients.1 cell) order word‖ ≤
        diskSupConstant *
          Real.sqrt (diskSupEnergy
            (shiftedClosedJet (coefficients.1 cell) word)) := by
    rw [ContinuousMap.norm_le _
      (mul_nonneg diskSupConstant_pos.le (Real.sqrt_nonneg _))]
    intro point
    exact diskSup_bound (shiftedClosedJet (coefficients.1 cell) word) point
  calc
    cellFrequency cell ^ cellOrder *
          ‖closedDerivative (coefficients.1 cell) order word‖ ≤
        cellFrequency cell ^ cellOrder *
          (diskSupConstant *
            Real.sqrt (diskSupEnergy
              (shiftedClosedJet (coefficients.1 cell) word))) := by
      exact mul_le_mul_of_nonneg_left derivativeSupBound
        (pow_nonneg (cellFrequency_pos cell).le _)
    _ ≤ cellFrequency cell ^ cellOrder *
          (diskSupConstant *
            ∑ slot : Fin 6,
              ‖closedDerivativeL2 (diskSupMultiIndex slot)
                (shiftedClosedJet (coefficients.1 cell) word)‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sqrt_diskSupEnergy_le_sum _)
          diskSupConstant_pos.le)
        (pow_nonneg (cellFrequency_pos cell).le _)
    _ = diskSupConstant *
        ∑ slot : Fin 6,
          cellFrequency cell ^ cellOrder *
            ‖closedDerivativeL2 (diskSupMultiIndex slot)
              (shiftedClosedJet (coefficients.1 cell) word)‖ := by
      rw [← Finset.mul_sum]
      ring

/-- Quantitative M15 in the uniform closed-disk norm, at the literal grade
`|word| + cellOrder + 3`. -/
theorem m15_frequencyWeighted_sup_tsum_le {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    ∑' cell : ℤ,
        cellFrequency cell ^ cellOrder *
          ‖closedDerivative (coefficients.1 cell) order word‖ ≤
      m15EvaluationConstant *
        ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ := by
  let coordinateTerm : Fin 6 → ℤ → ℝ := fun slot cell =>
    cellFrequency cell ^ cellOrder *
      ‖closedDerivativeL2 (diskSupMultiIndex slot)
        (shiftedClosedJet (coefficients.1 cell) word)‖
  have eachCoordinate : ∀ slot : Fin 6, Summable (coordinateTerm slot) :=
    fun slot => m15_singleCoordinate_summable coefficients word cellOrder slot
  have finiteCoordinateSum : ∀ slots : Finset (Fin 6),
      Summable (fun cell : ℤ =>
        ∑ slot ∈ slots, coordinateTerm slot cell) := by
    intro slots
    induction slots using Finset.induction_on with
    | empty => simp
    | @insert slot slots fresh inductionHypothesis =>
      simpa [Finset.sum_insert fresh] using
        (eachCoordinate slot).add inductionHypothesis
  have coordinateSum : Summable (fun cell : ℤ =>
      ∑ slot : Fin 6, coordinateTerm slot cell) := by
    simpa using finiteCoordinateSum Finset.univ
  have finiteSwap : ∀ slots : Finset (Fin 6),
      (∑' cell : ℤ, ∑ slot ∈ slots, coordinateTerm slot cell) =
        ∑ slot ∈ slots, ∑' cell : ℤ, coordinateTerm slot cell := by
    intro slots
    induction slots using Finset.induction_on with
    | empty => simp
    | @insert slot slots fresh inductionHypothesis =>
      simp only [Finset.sum_insert fresh]
      rw [Summable.tsum_add (eachCoordinate slot)
        (finiteCoordinateSum slots)]
      exact congrArg ((∑' cell : ℤ, coordinateTerm slot cell) + ·)
        inductionHypothesis
  have coordinateSwap :
      (∑' cell : ℤ, ∑ slot : Fin 6, coordinateTerm slot cell) =
        ∑ slot : Fin 6, ∑' cell : ℤ, coordinateTerm slot cell := by
    simpa using finiteSwap Finset.univ
  have majorantSummable : Summable (fun cell : ℤ =>
      diskSupConstant * ∑ slot : Fin 6, coordinateTerm slot cell) :=
    coordinateSum.mul_left diskSupConstant
  calc
    (∑' cell : ℤ,
        cellFrequency cell ^ cellOrder *
          ‖closedDerivative (coefficients.1 cell) order word‖) ≤
        ∑' cell : ℤ,
          diskSupConstant * ∑ slot : Fin 6, coordinateTerm slot cell :=
      (m15_frequencyWeighted_sup_summable coefficients word cellOrder).tsum_le_tsum
        (m15_frequencyWeighted_sup_le_coordinateSum coefficients word
          cellOrder) majorantSummable
    _ = diskSupConstant *
        ∑ slot : Fin 6, ∑' cell : ℤ, coordinateTerm slot cell := by
      rw [tsum_mul_left, coordinateSwap]
    _ ≤ diskSupConstant *
        ∑ slot : Fin 6,
          (‖inverseCellFrequencyLp‖ *
            ‖ordinaryGradeCoordinates (m15Grade word cellOrder)
              coefficients‖) := by
      apply mul_le_mul_of_nonneg_left _ diskSupConstant_pos.le
      apply Finset.sum_le_sum
      intro slot _membership
      exact m15_singleCoordinate_tsum_le coefficients word cellOrder slot
    _ = m15EvaluationConstant *
        ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ := by
      unfold m15EvaluationConstant
      rw [← Finset.sum_mul]
      ring

theorem ordinaryDerivativeExtension_norm_le_m15 {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    ‖ordinaryDerivativeExtension coefficients word cellOrder‖ ≤
      m15EvaluationConstant *
        ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ := by
  let term : ℤ → C(DiskCellDomain, ComplexEuclidean dimension) := fun cell =>
    ordinaryDerivativeDiskCellTerm word cellOrder cell (coefficients.1 cell)
  have derivativeMajorant :=
    physicalDerivative_series_summable coefficients word cellOrder
  have termNormSummable : Summable (fun cell : ℤ => ‖term cell‖) := by
    exact Summable.of_nonneg_of_le (fun cell => norm_nonneg (term cell))
      (fun cell => ordinaryDerivativeDiskCellTerm_norm_le word cellOrder cell
        (coefficients.1 cell)) derivativeMajorant
  have frequencyMajorant :=
    m15_frequencyWeighted_sup_summable coefficients word cellOrder
  change ‖∑' cell : ℤ, term cell‖ ≤ _
  calc
    ‖∑' cell : ℤ, term cell‖ ≤ ∑' cell : ℤ, ‖term cell‖ :=
      norm_tsum_le_tsum_norm termNormSummable
    _ ≤ ∑' cell : ℤ,
        cellFrequency cell ^ cellOrder *
          ‖closedDerivative (coefficients.1 cell) order word‖ := by
      apply termNormSummable.tsum_le_tsum _ frequencyMajorant
      intro cell
      exact (ordinaryDerivativeDiskCellTerm_norm_le word cellOrder cell
        (coefficients.1 cell)).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (cell_abs_le_frequency cell)
            cellOrder)
          (norm_nonneg _))
    _ ≤ _ := m15_frequencyWeighted_sup_tsum_le coefficients word cellOrder

theorem ordinaryGradeCoordinates_weighted_norm {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) :
    ‖ordinaryGradeCoordinates grade
        (weightedCoefficientCoreEquiv parameters field)‖ =
      ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply congrArg norm
  apply Subtype.ext
  exact ordinary_coordinates_phaseWeighted parameters field.1

/-- The quantitative coordinate-derivative estimate in the original analytic
grade.  The hypothesis `order + cellOrder ≤ j` is exactly the total physical
derivative-order condition, and the source norm is literally `A^(j+3)`. -/
theorem originalGrade_coordinateDerivative_bound
    {dimension order j : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension (j + 3))
    (word : CartesianWord order) (cellOrder : ℕ)
    (totalOrder : order + cellOrder ≤ j) :
    ‖ordinaryDerivativeExtension
        (weightedCoefficientCoreEquiv parameters field.toCore)
        word cellOrder‖ ≤
      m15EvaluationConstant * ‖field‖ := by
  let coefficients := weightedCoefficientCoreEquiv parameters field.toCore
  have gradeLe : m15Grade word cellOrder ≤ j + 3 := by
    unfold m15Grade
    omega
  have lowNormIdentity :
      ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ =
        ‖GradeCore.ofCoreLinear (grade := m15Grade word cellOrder)
          field.toCore‖ := by
    rw [show coefficients = weightedCoefficientCoreEquiv parameters field.toCore by rfl,
      ordinaryGradeCoordinates_weighted_norm,
      gradeCore_norm_eq_cartesianGradeSeminorm,
      cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
    rfl
  have gradeNormBound :
      ‖ordinaryGradeCoordinates (m15Grade word cellOrder) coefficients‖ ≤
        ‖field‖ := by
    rw [lowNormIdentity]
    simpa only [GradeCore.ofCore_toCore] using
      cartesianGrade_norm_mono parameters gradeLe field.toCore
  exact (ordinaryDerivativeExtension_norm_le_m15 coefficients word cellOrder).trans
    (mul_le_mul_of_nonneg_left gradeNormBound m15EvaluationConstant_nonneg)

end Grad.CartesianState
