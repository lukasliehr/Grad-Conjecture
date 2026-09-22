import SC2PhysicalCofactor

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Frame

/-- A one-column operator has no larger norm than its column vector. -/
theorem columnEmbedding_norm_le {input output : ℕ} (column : Fin input)
    (value : ComplexEuclidean output) :
    ‖columnEmbedding input output column value‖ ≤ ‖value‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg value)
  intro argument
  rw [columnEmbedding_apply, norm_smul]
  calc
    ‖argument column‖ * ‖value‖ ≤ ‖argument‖ * ‖value‖ :=
      mul_le_mul_of_nonneg_right (PiLp.norm_apply_le argument column) (norm_nonneg value)
    _ = ‖value‖ * ‖argument‖ := mul_comm _ _

theorem referenceStateValue_norm_le (point : ClosedDisk) :
    ‖referenceStateValue point‖ ≤ 1 := by
  have normIdentity : ‖referenceStateValue point‖ = ‖point.val‖ := by
    unfold referenceStateValue
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    simp [Fin.sum_univ_three, Fin.sum_univ_two]
  rw [normIdentity]
  exact point.property

/-- The explicit full-disk frame perturbation constant obtained from the
original Fourier `C¹` estimate. -/
def originalFrameMarginConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  let zero := originalDerivativeSumConstant parameters 0
  let one := originalDerivativeSumConstant parameters 1
  2 * one + ‖(L : ℂ)⁻¹‖ *
    (zero + ‖physicalRotation‖ * zero + ‖physicalRotation‖)

theorem originalFrameMarginConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) :
    0 ≤ originalFrameMarginConstant parameters L := by
  unfold originalFrameMarginConstant
  exact add_nonneg
    (mul_nonneg (by norm_num) (originalDerivativeSumConstant_nonnegative parameters 1))
    (mul_nonneg (norm_nonneg _)
      (add_nonneg
        (add_nonneg (originalDerivativeSumConstant_nonnegative parameters 0)
          (mul_nonneg (norm_nonneg physicalRotation)
            (originalDerivativeSumConstant_nonnegative parameters 0)))
        (norm_nonneg physicalRotation)))

/-- The actual smaller low ball used for the global frame. -/
def originalFrameLowRadius (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  (2 * (originalFrameMarginConstant parameters L + 1))⁻¹

theorem originalFrameLowRadius_pos (parameters : PhaseParameters) (L : ℝ) :
    0 < originalFrameLowRadius parameters L := by
  unfold originalFrameLowRadius
  exact inv_pos.mpr (mul_pos (by norm_num)
    (by linarith [originalFrameMarginConstant_nonnegative parameters L]))

/-- Uniform full-disk estimate for the literal physical frame perturbation.
There is no cap scale and no analytic-width change. -/
theorem originalPhysicalFrameDeviation_norm_le (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1)
    (axialAngle : ℝ) (point : ClosedDisk) :
    ‖originalPhysicalFrameDeviation parameters L epsilon field axialAngle point‖ ≤
      originalFrameMarginConstant parameters L *
        (originalGradeNorm 4 field + |epsilon|) := by
  let coefficients := originalCoefficientCore parameters field
  let location : DiskCellDomain := (point, (axialAngle : CellCircle))
  let field4 : GradeCore parameters 3 4 := GradeCore.ofCoreLinear field
  let first := ordinaryDerivativeExtension coefficients firstPlanarDerivativeWord 0
  let second := ordinaryDerivativeExtension coefficients secondPlanarDerivativeWord 0
  let axial := ordinaryDerivativeExtension coefficients emptyCartesianWord 1
  let value := ordinaryDerivativeExtension coefficients emptyCartesianWord 0
  have fieldNorm : ‖field4‖ = originalGradeNorm 4 field := rfl
  have firstBound : ‖first location‖ ≤
      originalDerivativeSumConstant parameters 1 * ‖field4‖ :=
    (ContinuousMap.norm_coe_le_norm first location).trans
      (originalField_coordinateDerivative_bound parameters field4
        firstPlanarDerivativeWord 0 (by norm_num))
  have secondBound : ‖second location‖ ≤
      originalDerivativeSumConstant parameters 1 * ‖field4‖ :=
    (ContinuousMap.norm_coe_le_norm second location).trans
      (originalField_coordinateDerivative_bound parameters field4
        secondPlanarDerivativeWord 0 (by norm_num))
  have axialBound : ‖axial location‖ ≤
      originalDerivativeSumConstant parameters 0 * ‖field4‖ :=
    (ContinuousMap.norm_coe_le_norm axial location).trans
      (originalField_coordinateDerivative_bound parameters field4
        emptyCartesianWord 1 (by norm_num))
  have valueBound : ‖value location‖ ≤
      originalDerivativeSumConstant parameters 0 * ‖field4‖ :=
    (ContinuousMap.norm_coe_le_norm value location).trans
      (originalField_coordinateDerivative_bound parameters field4
        emptyCartesianWord 0 (by norm_num))
  have rotationBound :
      ‖physicalRotation (referenceStateValue point + value location)‖ ≤
        ‖physicalRotation‖ * (1 +
          originalDerivativeSumConstant parameters 0 * ‖field4‖) := by
    calc
      _ ≤ ‖physicalRotation‖ * ‖referenceStateValue point + value location‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖physicalRotation‖ *
          (‖referenceStateValue point‖ + ‖value location‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖physicalRotation‖ *
          (1 + originalDerivativeSumConstant parameters 0 * ‖field4‖) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (referenceStateValue_norm_le point) valueBound)
          (norm_nonneg physicalRotation)
  have perturbationBound :
      ‖originalPhysicalFrameDeviation parameters L epsilon field axialAngle point‖ ≤
        2 * originalDerivativeSumConstant parameters 1 * ‖field4‖ +
          ‖(L : ℂ)⁻¹‖ *
            (originalDerivativeSumConstant parameters 0 * ‖field4‖ +
              |epsilon| * ‖physicalRotation‖ *
                (1 + originalDerivativeSumConstant parameters 0 * ‖field4‖)) := by
    have thirdBound :
        ‖columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
          (axial location + (epsilon : ℂ) •
            physicalRotation (referenceStateValue point + value location)))‖ ≤
          ‖(L : ℂ)⁻¹‖ *
            (‖axial location‖ + |epsilon| *
              ‖physicalRotation (referenceStateValue point + value location)‖) := by
      calc
        _ ≤ ‖(L : ℂ)⁻¹ •
            (axial location + (epsilon : ℂ) •
              physicalRotation (referenceStateValue point + value location))‖ :=
          columnEmbedding_norm_le _ _
        _ = ‖(L : ℂ)⁻¹‖ *
            ‖axial location + (epsilon : ℂ) •
              physicalRotation (referenceStateValue point + value location)‖ := norm_smul _ _
        _ ≤ ‖(L : ℂ)⁻¹‖ *
            (‖axial location‖ + |epsilon| *
              ‖physicalRotation (referenceStateValue point + value location)‖) := by
          rw [show |epsilon| = ‖(epsilon : ℂ)‖ by simp]
          exact mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add le_rfl (norm_smul _ _).le))
            (norm_nonneg _)
    change ‖columnEmbedding 3 3 0 (first location) +
        columnEmbedding 3 3 1 (second location) +
        columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
          (axial location + (epsilon : ℂ) •
            physicalRotation (referenceStateValue point + value location)))‖ ≤ _
    calc
      _ ≤ ‖columnEmbedding 3 3 0 (first location)‖ +
          ‖columnEmbedding 3 3 1 (second location)‖ +
          ‖columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
            (axial location + (epsilon : ℂ) •
              physicalRotation (referenceStateValue point + value location)))‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖first location‖ + ‖second location‖ +
          ‖(L : ℂ)⁻¹‖ *
            (‖axial location‖ + |epsilon| *
              ‖physicalRotation (referenceStateValue point + value location)‖) := by
        exact add_le_add
          (add_le_add (columnEmbedding_norm_le _ _) (columnEmbedding_norm_le _ _))
          thirdBound
      _ ≤ _ := by
        have firstSecond : ‖first location‖ + ‖second location‖ ≤
            2 * originalDerivativeSumConstant parameters 1 * ‖field4‖ := by
          calc
            _ ≤ originalDerivativeSumConstant parameters 1 * ‖field4‖ +
                originalDerivativeSumConstant parameters 1 * ‖field4‖ :=
              add_le_add firstBound secondBound
            _ = _ := by ring
        have inside : ‖axial location‖ + |epsilon| *
              ‖physicalRotation (referenceStateValue point + value location)‖ ≤
            originalDerivativeSumConstant parameters 0 * ‖field4‖ +
              |epsilon| * ‖physicalRotation‖ *
                (1 + originalDerivativeSumConstant parameters 0 * ‖field4‖) := by
          apply add_le_add axialBound
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left rotationBound (abs_nonneg epsilon)
        exact add_le_add firstSecond
          (mul_le_mul_of_nonneg_left inside (norm_nonneg _))
  rw [fieldNorm] at perturbationBound
  have zeroNonnegative := originalDerivativeSumConstant_nonnegative parameters 0
  have oneNonnegative := originalDerivativeSumConstant_nonnegative parameters 1
  have fieldNonnegative := originalGradeNorm_nonnegative 4 field
  have epsilonNonnegative := abs_nonneg epsilon
  have rotationNonnegative := norm_nonneg physicalRotation
  have inverseNonnegative := norm_nonneg ((L : ℂ)⁻¹)
  have cross := mul_le_mul_of_nonneg_right epsilonSmall
    (mul_nonneg rotationNonnegative
      (mul_nonneg zeroNonnegative fieldNonnegative))
  calc
    _ ≤ _ := perturbationBound
    _ ≤ 2 * originalDerivativeSumConstant parameters 1 * originalGradeNorm 4 field +
          ‖(L : ℂ)⁻¹‖ *
            (originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field +
              ‖physicalRotation‖ * |epsilon| +
              ‖physicalRotation‖ * originalDerivativeSumConstant parameters 0 *
                originalGradeNorm 4 field) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ inverseNonnegative
      calc
        originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field +
            |epsilon| * ‖physicalRotation‖ *
              (1 + originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field) =
            originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field +
              (‖physicalRotation‖ * |epsilon| +
                |epsilon| * (‖physicalRotation‖ *
                  (originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field))) := by ring
        _ ≤ originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field +
              (‖physicalRotation‖ * |epsilon| +
                ‖physicalRotation‖ * originalDerivativeSumConstant parameters 0 *
                  originalGradeNorm 4 field) := by
          exact add_le_add le_rfl (add_le_add le_rfl
            (by simpa only [mul_assoc, one_mul] using cross))
        _ = originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field +
              ‖physicalRotation‖ * |epsilon| +
              ‖physicalRotation‖ * originalDerivativeSumConstant parameters 0 *
                originalGradeNorm 4 field := by ring
    _ ≤ originalFrameMarginConstant parameters L *
        (originalGradeNorm 4 field + |epsilon|) := by
      let extra := 2 * originalDerivativeSumConstant parameters 1 * |epsilon| +
        ‖(L : ℂ)⁻¹‖ *
          (originalDerivativeSumConstant parameters 0 * |epsilon| +
            ‖physicalRotation‖ * originalDerivativeSumConstant parameters 0 * |epsilon| +
            ‖physicalRotation‖ * originalGradeNorm 4 field)
      have extraNonnegative : 0 ≤ extra := by
        dsimp only [extra]
        positivity
      have identity : originalFrameMarginConstant parameters L *
            (originalGradeNorm 4 field + |epsilon|) =
          (2 * originalDerivativeSumConstant parameters 1 * originalGradeNorm 4 field +
            ‖(L : ℂ)⁻¹‖ *
              (originalDerivativeSumConstant parameters 0 * originalGradeNorm 4 field +
                ‖physicalRotation‖ * |epsilon| +
                ‖physicalRotation‖ * originalDerivativeSumConstant parameters 0 *
                  originalGradeNorm 4 field)) + extra := by
        dsimp only [originalFrameMarginConstant, extra]
        ring
      rw [identity]
      exact le_add_of_nonneg_right extraNonnegative

theorem originalPhysicalFrameDeviation_norm_lt_one_of_low
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (axialAngle : ℝ) (point : ClosedDisk) :
    ‖originalPhysicalFrameDeviation parameters L epsilon field axialAngle point‖ < 1 := by
  have epsilonSmall : |epsilon| ≤ 1 := by
    have radiusLe : originalFrameLowRadius parameters L ≤ 1 := by
      unfold originalFrameLowRadius
      have constantNonnegative := originalFrameMarginConstant_nonnegative parameters L
      rw [inv_le_one₀ (by positivity : 0 < 2 *
        (originalFrameMarginConstant parameters L + 1))]
      nlinarith
    exact (le_add_of_nonneg_left (originalGradeNorm_nonnegative 4 field)).trans
      (low.trans radiusLe)
  have bound := originalPhysicalFrameDeviation_norm_le parameters L epsilon field epsilonSmall
    axialAngle point
  apply bound.trans_lt
  unfold originalFrameLowRadius at low
  have constantNonnegative := originalFrameMarginConstant_nonnegative parameters L
  calc
    originalFrameMarginConstant parameters L *
        (originalGradeNorm 4 field + |epsilon|) ≤
      originalFrameMarginConstant parameters L *
        (2 * (originalFrameMarginConstant parameters L + 1))⁻¹ :=
      mul_le_mul_of_nonneg_left low constantNonnegative
    _ < 1 := by
      rw [mul_inv_lt_iff₀ (by positivity : 0 < 2 *
        (originalFrameMarginConstant parameters L + 1))]
      nlinarith

end Grad.SourceCollar
