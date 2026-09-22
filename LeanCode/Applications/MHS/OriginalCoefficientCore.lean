import GC14WeightedSup

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Grad.CartesianState

open Grad.ClosedJets

theorem originalClosedDerivative_norm_le_phaseOutside {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    ‖closedDerivative field order word‖ ≤
      ‖phaseOutsideClosedDerivative parameters cell field order word‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro point
  calc
    ‖closedDerivative field order word point‖ ≤
        cartesianWeight parameters cell point.val *
          ‖closedDerivative field order word point‖ :=
      le_mul_of_one_le_left (norm_nonneg _)
        (cartesianWeight_one_le parameters cell point)
    _ = ‖phaseOutsideClosedDerivative parameters cell field order word point‖ := by
      change _ = ‖cartesianWeight parameters cell point.val •
        closedDerivative field order word point‖
      rw [norm_smul, Real.norm_of_nonneg (cartesianWeight_pos parameters cell point.val).le]
    _ ≤ ‖phaseOutsideClosedDerivative parameters cell field order word‖ :=
      ContinuousMap.norm_coe_le_norm _ point

theorem originalClosedDerivative_frequency_summable {dimension order : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ => cellFrequency cell ^ cellOrder *
      ‖closedDerivative (field.1 cell) order word‖) := by
  exact Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
    (fun cell => mul_le_mul_of_nonneg_left
      (originalClosedDerivative_norm_le_phaseOutside parameters cell (field.1 cell) order word)
      (pow_nonneg (cellFrequency_pos cell).le _))
    (phaseOutsideClosedDerivative_frequency_summable parameters field word cellOrder)

theorem originalClosedDerivative_frequency_tsum_bound {dimension order j : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension (j + 3))
    (word : CartesianWord order) (cellOrder : ℕ) (orderLe : order + cellOrder ≤ j) :
    ∑' cell : ℤ, cellFrequency cell ^ cellOrder *
        ‖closedDerivative (field.toCore.1 cell) order word‖ ≤
      originalDerivativeSumConstant parameters order * ‖field‖ := by
  refine ((originalClosedDerivative_frequency_summable parameters field.toCore word cellOrder).tsum_le_tsum
    (fun cell => mul_le_mul_of_nonneg_left
      (originalClosedDerivative_norm_le_phaseOutside parameters cell
        (field.toCore.1 cell) order word)
      (pow_nonneg (cellFrequency_pos cell).le _))
      (phaseOutsideClosedDerivative_frequency_summable parameters field.toCore word cellOrder)).trans ?_
  exact phaseOutsideClosedDerivative_frequency_tsum_bound parameters field word cellOrder orderLe

theorem originalClosedDerivative_frequency_sq_summable {dimension order : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ => cellFrequency cell ^ (2 * cellOrder) *
      ‖closedDerivative (field.1 cell) order word‖ ^ 2) := by
  let sequence (cell : ℤ) := cellFrequency cell ^ cellOrder *
    ‖closedDerivative (field.1 cell) order word‖
  have sequenceNonnegative (cell : ℤ) : 0 ≤ sequence cell :=
    mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)
  have oneMember : Memℓp sequence 1 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_of_nonneg
      (sequenceNonnegative _)] using
      originalClosedDerivative_frequency_summable parameters field word cellOrder
  have twoMember : Memℓp sequence 2 :=
    oneMember.of_exponent_ge (by norm_num)
  have squares := twoMember.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply squares.congr
  intro cell
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat,
    Real.norm_of_nonneg (sequenceNonnegative cell)]
  dsimp [sequence]
  ring

theorem originalClosedDerivativeL2_frequency_sq_summable {dimension order : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ => cellFrequency cell ^ (2 * cellOrder) *
      ‖closedContinuousToDiskL2 (closedDerivative (field.1 cell) order word)‖ ^ 2) := by
  let diskMass := (volume.restrict openUnitDisk).real Set.univ
  have uniformSummable :=
    originalClosedDerivative_frequency_sq_summable parameters field word cellOrder
  apply Summable.of_nonneg_of_le
    (fun cell => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (sq_nonneg _))
    _ (uniformSummable.mul_left diskMass)
  intro cell
  have l2Bound := closedContinuousToDiskL2_norm_sq_le
    (closedDerivative (field.1 cell) order word)
  calc
    _ ≤ cellFrequency cell ^ (2 * cellOrder) *
        (diskMass * ‖closedDerivative (field.1 cell) order word‖ ^ 2) :=
      mul_le_mul_of_nonneg_left l2Bound (pow_nonneg (cellFrequency_pos cell).le _)
    _ = diskMass * (cellFrequency cell ^ (2 * cellOrder) *
        ‖closedDerivative (field.1 cell) order word‖ ^ 2) := by ring

theorem originalCoefficient_gradeCoordinate_summable {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : GradeMultiIndex grade) :
    Summable (fun cell : ℤ =>
      ‖ordinaryRawGradeCoordinates grade field.1 cell index‖ ^ 2) := by
  let weightOrder := grade - cartesianOrder index.toCartesian
  have source := originalClosedDerivativeL2_frequency_sq_summable parameters field
    (cartesianMultiIndexWord index.toCartesian) weightOrder
  apply source.congr
  intro cell
  rw [show ordinaryRawGradeCoordinates grade field.1 cell index =
      (cellFrequency cell : ℂ) ^ weightOrder •
        closedContinuousToDiskL2
          (closedMultiDerivative (field.1 cell) index.toCartesian) by rfl,
    norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell)]
  change _ = (cellFrequency cell ^ weightOrder *
    ‖closedContinuousToDiskL2
      (closedDerivative (field.1 cell) (cartesianOrder index.toCartesian)
        (cartesianMultiIndexWord index.toCartesian))‖) ^ 2
  ring

theorem originalCoefficient_mem_ordinary_all_grades {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    Memℓp (ordinaryRawGradeCoordinates grade field.1) 2 := by
  apply (memlp_iff_summable_sq _).2
  have allCoordinates : Summable (fun cell : ℤ =>
      ∑ index : GradeMultiIndex grade,
        ‖ordinaryRawGradeCoordinates grade field.1 cell index‖ ^ 2) :=
    (hasSum_sum (fun index _ =>
      (originalCoefficient_gradeCoordinate_summable parameters field index).hasSum)).summable
  apply allCoordinates.congr
  intro cell
  exact (PiLp.norm_sq_eq_of_L2
    (fun _ : GradeMultiIndex grade => DiskL2 dimension)
    (ordinaryRawGradeCoordinates grade field.1 cell)).symm

/-- The original coefficients, with no phase multiplication, lie in the
ordinary all-grade core. -/
def originalCoefficientCore {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) : OrdinaryCoefficientCore dimension :=
  ⟨field.1, originalCoefficient_mem_ordinary_all_grades parameters field⟩

@[simp] theorem originalCoefficientCore_apply {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (cell : ℤ) :
    (originalCoefficientCore parameters field).1 cell = field.1 cell := rfl

def originalPhysicalClosedJet {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) : DiskCellClosedJet dimension :=
  ordinaryReconstructedClosedJet (originalCoefficientCore parameters field)

/-- Exact recovery of the original cell coefficient, including cell zero. -/
theorem originalPhysicalClosedJet_fourierCoefficient {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (cell : ℤ) :
    diskCellFourierCoefficientJet (originalPhysicalClosedJet parameters field) cell =
      field.1 cell := by
  exact diskCellFourierCoefficientJet_ordinaryReconstructedClosedJet
    (originalCoefficientCore parameters field) cell

end Grad.CartesianState
