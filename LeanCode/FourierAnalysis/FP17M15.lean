import FP17DerivativeShift
import FT3Reconstruction

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The ordinary grade used by M15 for a planar derivative word and `b`
cell derivatives. -/
def m15Grade {order : ℕ} (_word : CartesianWord order) (cellOrder : ℕ) : ℕ :=
  order + cellOrder + 3

/-- The canonical ordinary multi-index of one of A08's six derivatives after
fixing the requested planar derivative word. -/
def m15DiskSupIndex {order : ℕ} (word : CartesianWord order)
    (slot : Fin 6) : CartesianMultiIndex :=
  shiftedCartesianIndex word (diskSupMultiIndex slot)

theorem m15DiskSupIndex_order {order : ℕ} (word : CartesianWord order)
    (slot : Fin 6) :
    cartesianOrder (m15DiskSupIndex word slot) =
      cartesianOrder (diskSupMultiIndex slot) + order :=
  shiftedCartesianIndex_order word (diskSupMultiIndex slot)

theorem m15DiskSupIndex_order_le {order cellOrder : ℕ}
    (word : CartesianWord order) (slot : Fin 6) :
    cartesianOrder (m15DiskSupIndex word slot) ≤
      m15Grade word cellOrder := by
  rw [m15DiskSupIndex_order]
  have slotBound := diskSupMultiIndex_order_le_two slot
  unfold m15Grade
  omega

/-- A08's shifted derivative as an actual coordinate of the ordinary grade
row. -/
def m15GradeIndex {order cellOrder : ℕ} (word : CartesianWord order)
    (slot : Fin 6) : GradeMultiIndex (m15Grade word cellOrder) :=
  (gradeMultiIndexEquiv (m15Grade word cellOrder)).symm
    ⟨m15DiskSupIndex word slot, m15DiskSupIndex_order_le word slot⟩

@[simp] theorem m15GradeIndex_toCartesian {order cellOrder : ℕ}
    (word : CartesianWord order) (slot : Fin 6) :
    (m15GradeIndex (cellOrder := cellOrder) word slot).toCartesian =
      m15DiskSupIndex word slot := by
  have identity := (gradeMultiIndexEquiv (m15Grade word cellOrder)).apply_symm_apply
    ⟨m15DiskSupIndex word slot, m15DiskSupIndex_order_le word slot⟩
  exact congrArg Subtype.val identity

theorem m15GradeIndex_weight_exponent {order cellOrder : ℕ}
    (word : CartesianWord order) (slot : Fin 6) :
    cellOrder + 1 ≤
      m15Grade word cellOrder -
        cartesianOrder
          (m15GradeIndex (cellOrder := cellOrder) word slot).toCartesian := by
  rw [m15GradeIndex_toCartesian, m15DiskSupIndex_order]
  have slotBound := diskSupMultiIndex_order_le_two slot
  unfold m15Grade
  omega

theorem shiftedClosedDerivativeL2_eq_m15Coordinate {dimension order : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord order)
    (slot : Fin 6) :
    closedDerivativeL2 (diskSupMultiIndex slot)
        (shiftedClosedJet field word) =
      closedContinuousToDiskL2
        (closedMultiDerivative field (m15DiskSupIndex word slot)) := by
  change closedContinuousToDiskL2
      (closedMultiDerivative (shiftedClosedJet field word)
        (diskSupMultiIndex slot)) = _
  rw [shiftedClosedJet_closedMultiDerivative]
  rfl

/-- The inverse cell-frequency square is the accepted one-dimensional
summable comparison sequence. -/
theorem inverseCellFrequency_sq_summable :
    Summable (fun cell : ℤ => (cellFrequency cell)⁻¹ ^ 2) := by
  apply Grad.FourierGrade.integerSquareDecay_summable.congr
  intro cell
  rw [Grad.FourierGrade.integerSquareDecay, cellFrequency_formula]
  have radicandNonnegative : 0 ≤ 1 + (cell : ℝ) ^ 2 := by positivity
  rw [inv_pow, Real.sq_sqrt radicandNonnegative]

/-- One fixed A08 coordinate has the weighted absolute summability needed
for M15. -/
theorem m15_singleCoordinate_summable {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) (slot : Fin 6) :
    Summable (fun cell : ℤ =>
      cellFrequency cell ^ cellOrder *
        ‖closedDerivativeL2 (diskSupMultiIndex slot)
          (shiftedClosedJet (coefficients.1 cell) word)‖) := by
  let grade := m15Grade word cellOrder
  let index : GradeMultiIndex grade :=
    m15GradeIndex (cellOrder := cellOrder) word slot
  let coordinate : ℤ → DiskL2 dimension := fun cell =>
    ordinaryRawGradeCoordinates grade coefficients.1 cell index
  have coordinateMem : Memℓp coordinate 2 := by
    apply (coefficients.property grade).mono'
    intro cell
    exact PiLp.norm_apply_le
      (ordinaryRawGradeCoordinates grade coefficients.1 cell) index
  have coordinateSquare : Summable (fun cell : ℤ => ‖coordinate cell‖ ^ 2) :=
    (memlp_iff_summable_sq coordinate).mp coordinateMem
  have coordinateRpow : Summable (fun cell : ℤ =>
      ‖coordinate cell‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using coordinateSquare
  have inverseRpow : Summable (fun cell : ℤ =>
      (cellFrequency cell)⁻¹ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two] using inverseCellFrequency_sq_summable
  have productSummable : Summable (fun cell : ℤ =>
      (cellFrequency cell)⁻¹ * ‖coordinate cell‖) := by
    exact Real.summable_mul_of_Lp_Lq_of_nonneg
      (show (2 : ℝ).HolderConjugate 2 by
        rw [Real.holderConjugate_iff]
        norm_num)
      (fun cell => inv_nonneg.mpr (cellFrequency_pos cell).le)
      (fun cell => norm_nonneg (coordinate cell))
      inverseRpow coordinateRpow
  apply Summable.of_nonneg_of_le
    (fun cell => mul_nonneg
      (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
    _ productSummable
  intro cell
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
      ‖coordinate cell‖ =
        cellFrequency cell ^
            (grade - cartesianOrder index.toCartesian) *
          ‖closedContinuousToDiskL2
            (closedMultiDerivative (coefficients.1 cell)
              index.toCartesian)‖ := by
    rw [show coordinate cell =
        (cellFrequency cell : ℂ) ^
            (grade - cartesianOrder index.toCartesian) •
          closedContinuousToDiskL2
            (closedMultiDerivative (coefficients.1 cell)
              index.toCartesian) by rfl]
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
    _ = (cellFrequency cell)⁻¹ *
        (cellFrequency cell ^
            (grade - cartesianOrder index.toCartesian) *
          ‖closedContinuousToDiskL2
            (closedMultiDerivative (coefficients.1 cell)
              index.toCartesian)‖) := rfl

theorem sqrt_diskSupEnergy_le_sum {dimension : ℕ}
    (field : ClosedJet dimension) :
    Real.sqrt (diskSupEnergy field) ≤
      ∑ slot : Fin 6,
        ‖closedDerivativeL2 (diskSupMultiIndex slot) field‖ := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · exact Finset.sum_sq_le_sq_sum_of_nonneg
      (fun _ _ => norm_nonneg _)

theorem m15_frequencyWeighted_sup_summable {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ =>
      cellFrequency cell ^ cellOrder *
        ‖closedDerivative (coefficients.1 cell) order word‖) := by
  have eachCoordinate : ∀ slot : Fin 6,
      Summable (fun cell : ℤ =>
        cellFrequency cell ^ cellOrder *
          ‖closedDerivativeL2 (diskSupMultiIndex slot)
            (shiftedClosedJet (coefficients.1 cell) word)‖) :=
    fun slot => m15_singleCoordinate_summable coefficients word cellOrder slot
  have coordinateSum : Summable (fun cell : ℤ =>
      ∑ slot : Fin 6,
        cellFrequency cell ^ cellOrder *
          ‖closedDerivativeL2 (diskSupMultiIndex slot)
            (shiftedClosedJet (coefficients.1 cell) word)‖) := by
    have finiteSum : ∀ slots : Finset (Fin 6),
        Summable (fun cell : ℤ =>
          ∑ slot ∈ slots,
            cellFrequency cell ^ cellOrder *
              ‖closedDerivativeL2 (diskSupMultiIndex slot)
                (shiftedClosedJet (coefficients.1 cell) word)‖) := by
      intro slots
      induction slots using Finset.induction_on with
      | empty => simp
      | @insert slot slots notMember inductionHypothesis =>
        simpa [Finset.sum_insert notMember] using
          (eachCoordinate slot).add inductionHypothesis
    simpa using finiteSum Finset.univ
  have majorantSummable : Summable (fun cell : ℤ =>
      diskSupConstant *
        ∑ slot : Fin 6,
          cellFrequency cell ^ cellOrder *
            ‖closedDerivativeL2 (diskSupMultiIndex slot)
              (shiftedClosedJet (coefficients.1 cell) word)‖) :=
    coordinateSum.mul_left diskSupConstant
  apply Summable.of_nonneg_of_le
    (fun cell => mul_nonneg
      (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
    _ majorantSummable
  intro cell
  have derivativeSupBound :
      ‖closedDerivative (coefficients.1 cell) order word‖ ≤
        diskSupConstant *
          Real.sqrt (diskSupEnergy
            (shiftedClosedJet (coefficients.1 cell) word)) := by
    rw [ContinuousMap.norm_le _
      (mul_nonneg diskSupConstant_pos.le
        (Real.sqrt_nonneg _))]
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

theorem cell_abs_le_frequency (cell : ℤ) :
    |(cell : ℝ)| ≤ cellFrequency cell := by
  rw [cellFrequency_formula]
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs]
  linarith

/-- Exact M15 summability cost `|alpha| + b + 3`: every requested planar
closed derivative, after `b` cell derivatives, is absolutely summable in the
uniform disk norm. -/
theorem physicalDerivative_series_summable {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ =>
      |(cell : ℝ)| ^ cellOrder *
        ‖closedDerivative (coefficients.1 cell) order word‖) := by
  apply Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (abs_nonneg _) _)
      (norm_nonneg _))
    _ (m15_frequencyWeighted_sup_summable coefficients word cellOrder)
  intro cell
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (cell_abs_le_frequency cell) cellOrder)
    (norm_nonneg _)

end Grad.CartesianState
