import GC14FamilyAssembly

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set
open scoped BigOperators Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

def seedConstantValue {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) :
    C(ClosedDisk, OperatorValue inputDimension outputDimension) :=
  ContinuousMap.const ClosedDisk value

theorem seedConstant_lift_eventually {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) (point : SpatialPlane)
    (inside : point ∈ openUnitDisk) :
    closedDiskLift (seedConstantValue value) =ᶠ[𝓝 point] fun _ : SpatialPlane => value := by
  filter_upwards [openUnitDisk_isOpen.mem_nhds inside] with candidate candidateInside
  unfold closedDiskLift
  rw [dif_pos (openDiskMembershipClosed candidate candidateInside)]
  rfl

def seedConstantDerivative {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) (index : CartesianMultiIndex) :
    C(ClosedDisk, OperatorValue inputDimension outputDimension) :=
  if cartesianOrder index = 0 then seedConstantValue value else 0

theorem seedConstantDerivative_spec {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) (index : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (seedConstantValue value) index
      (seedConstantDerivative value index) := by
  intro point inside
  have localEquality := seedConstant_lift_eventually value point.val inside
  unfold seedConstantDerivative
  by_cases orderZero : cartesianOrder index = 0
  · rw [if_pos orderZero]
    rcases index with ⟨first, second⟩
    change first + second = 0 at orderZero
    have firstZero : first = 0 := by omega
    have secondZero : second = 0 := by omega
    subst first
    subst second
    change value = closedDiskLift (seedConstantValue value) point.val
    unfold closedDiskLift
    rw [dif_pos (openDiskMembershipClosed point.val inside)]
    rfl
  · rw [if_neg orderZero]
    unfold cartesianMultiDerivative cartesianDerivative
    rw [(localEquality.iteratedFDeriv ℝ (cartesianOrder index)).eq_of_nhds,
      iteratedFDeriv_const_of_ne orderZero value]
    rfl

def seedConstantJet {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) :
    SmoothOperatorJet inputDimension outputDimension where
  value := seedConstantValue value
  smoothInterior := by
    intro point inside
    exact (contDiffAt_const.congr_of_eventuallyEq
      (seedConstant_lift_eventually value point inside)).contDiffWithinAt
  derivativeExists := fun index => ⟨seedConstantDerivative value index,
    seedConstantDerivative_spec value index⟩

theorem seedConstantJet_derivative {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) (index : CartesianMultiIndex) :
    smoothOperatorDerivative (seedConstantJet value) index =
      seedConstantDerivative value index :=
  smoothOperatorDerivative_eq_of_spec _ _ _ (seedConstantDerivative_spec value index)

/-- A literal single Fourier mode with no spatial dependence. -/
def seedConstantCell (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (value : OperatorValue inputDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  familyCell L sigma gamma ell grade (fun _ => seedConstantJet value) cell

theorem seedConstantCell_derivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ} (cell other : ℤ)
    (value : OperatorValue inputDimension outputDimension) (index : DerivativeIndex grade)
    (point : ClosedDisk) :
    coefficientDerivative (seedConstantCell L sigma gamma ell grade cell value) other index point =
      if other = cell then
        if derivativeOrder index = 0 then value else 0
      else 0 := by
  change ((coefficientScale L sigma gamma ell grade other index point : ℂ)⁻¹) •
    weightedSingle L sigma gamma ell grade cell (seedConstantJet value) (other, index) point = _
  rw [weightedSingle_apply]
  by_cases same : other = cell
  · subst other
    rw [if_pos rfl, if_pos rfl]
    change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        smoothOperatorDerivative (seedConstantJet value) (derivativeMultiIndex index) point) = _
    rw [← mul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade cell index point).ne'), one_smul,
      seedConstantJet_derivative]
    unfold seedConstantDerivative
    change (if derivativeOrder index = 0 then seedConstantValue value else 0) point = _
    split_ifs <;> rfl
  · rw [if_neg same, if_neg same]
    apply ContinuousLinearMap.ext
    intro vector
    simp

theorem seedEnvelope_upper {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (point : ClosedDisk) :
    originalEnvelope sigma gamma ell cell point.val ≤ Real.exp (sigma * |(cell : ℝ)|) := by
  apply Real.exp_le_exp.mpr
  have positive : 0 ≤ gamma * ell * ‖point.val‖ * |(cell : ℝ)| :=
    mul_nonneg (mul_nonneg (mul_nonneg admissible.2.1.le admissible.2.2.2.1.le)
      (norm_nonneg point.val)) (abs_nonneg _)
  nlinarith

theorem seedConstantDerivative_point_norm_le {inputDimension outputDimension : ℕ}
    (value : OperatorValue inputDimension outputDimension) (index : CartesianMultiIndex)
    (point : ClosedDisk) : ‖seedConstantDerivative value index point‖ ≤ ‖value‖ := by
  by_cases zeroOrder : cartesianOrder index = 0
  · simp [seedConstantDerivative, zeroOrder, seedConstantValue]
  · simp [seedConstantDerivative, zeroOrder]

theorem seedConstantWeighted_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (cell : ℤ) (value : OperatorValue inputDimension outputDimension) (index : DerivativeIndex grade) :
    ‖weightedSmoothDerivative L sigma gamma ell grade cell (seedConstantJet value) index‖ ≤
      Real.exp (sigma * |(cell : ℝ)|) * cellFrequency cell ^ grade * ‖value‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (cellFrequency_pos cell).le _))
    (norm_nonneg value))).2
  intro point
  change ‖(coefficientScale L sigma gamma ell grade cell index point : ℂ) •
    smoothOperatorDerivative (seedConstantJet value) (derivativeMultiIndex index) point‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (coefficientScale_pos L sigma gamma ell grade cell index point).le,
    seedConstantJet_derivative]
  apply mul_le_mul _ (seedConstantDerivative_point_norm_le value _ point) (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (cellFrequency_pos cell).le _))
  unfold coefficientScale
  exact mul_le_mul (seedEnvelope_upper admissible cell point)
    ((pow_le_pow_left₀ (Real.sqrt_nonneg _) (scaledCellWeight_le_frequency admissible cell) _).trans
      (pow_le_pow_right₀ (cellFrequency_one_le cell) (Nat.sub_le _ _)))
    (pow_nonneg (Real.sqrt_nonneg _) _) (Real.exp_pos _).le

theorem seedConstantCell_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (cell : ℤ) (value : OperatorValue inputDimension outputDimension) :
    ‖seedConstantCell L sigma gamma ell grade cell value‖ ≤
      Fintype.card (DerivativeIndex grade) *
        (Real.exp (sigma * |(cell : ℝ)|) * cellFrequency cell ^ grade * ‖value‖) := by
  exact (familyCell_norm_le L sigma gamma ell grade (fun _ => seedConstantJet value) cell).trans
    ((Finset.sum_le_sum fun index _ => seedConstantWeighted_norm_le admissible cell value index).trans_eq
      (by simp))

theorem seedConstantCell_fourier {L sigma gamma ell : ℝ}
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (value : OperatorValue inputDimension outputDimension) (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (seedConstantCell L sigma gamma ell 0 cell value) angle point =
      fourierPhase cell angle • value := by
  change (∑' other : ℤ, fourierPhase other angle •
    coefficientDerivative (seedConstantCell L sigma gamma ell 0 cell value)
      other zeroDerivativeIndex point) = _
  simp_rw [seedConstantCell_derivative]
  have zeroTerm (other : ℤ) :
      fourierPhase other angle • (0 : OperatorValue inputDimension outputDimension) = 0 := by
    apply ContinuousLinearMap.ext
    intro vector
    simp
  simp [derivativeOrder, zeroDerivativeIndex, smul_ite, zeroTerm]

end Grad.GaugeCoefficients.Physical.Frame
