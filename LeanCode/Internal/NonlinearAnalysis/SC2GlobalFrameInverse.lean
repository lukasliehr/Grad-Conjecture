import SC2GlobalFrameMargin

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 700000

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.NonlinearProduct
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

theorem referenceFrame_add_injective_of_norm_lt_one
    (deviation : OperatorValue 3 3) (small : ‖deviation‖ < 1) :
    Function.Injective (referenceFrame + deviation) := by
  intro first second same
  let difference : PhysicalValue 3 := first - second
  have totalZero : (referenceFrame + deviation) difference = 0 := by
    dsimp only [difference]
    rw [map_sub, same, sub_self]
  have sumZero : referenceFrame difference + deviation difference = 0 := by
    exact totalZero
  have referenceEq : referenceFrame difference = -deviation difference :=
    eq_neg_of_add_eq_zero_left sumZero
  have differenceEq : difference = -referenceFrame (deviation difference) := by
    calc
      difference = referenceFrame (referenceFrame difference) := by
        have square := congrArg (fun mapping : OperatorValue 3 3 => mapping difference)
          referenceFrame_square
        exact square.symm
      _ = referenceFrame (-deviation difference) := congrArg referenceFrame referenceEq
      _ = -referenceFrame (deviation difference) := map_neg _ _
  have normEq : ‖difference‖ = ‖deviation difference‖ := by
    calc
      ‖difference‖ = ‖-referenceFrame (deviation difference)‖ :=
        congrArg norm differenceEq
      _ = ‖referenceFrame (deviation difference)‖ := norm_neg _
      _ = ‖deviation difference‖ := referenceFrame_norm_map _
  have differenceZero : difference = 0 := by
    by_contra nonzero
    have positive : 0 < ‖difference‖ := norm_pos_iff.mpr nonzero
    have bound := ContinuousLinearMap.le_opNorm deviation difference
    have strict : ‖deviation‖ * ‖difference‖ < ‖difference‖ := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right small positive
    have impossible : ‖difference‖ < ‖difference‖ := by
      calc
        ‖difference‖ = ‖deviation difference‖ := normEq
        _ ≤ ‖deviation‖ * ‖difference‖ := bound
        _ < ‖difference‖ := strict
    exact (lt_irrefl _ impossible)
  exact sub_eq_zero.mp differenceZero

theorem operatorMatrix_mulVec {input output : ℕ}
    (mapping : OperatorValue input output) (value : Fin input → ℂ) :
    WithLp.toLp 2 ((operatorMatrix mapping).mulVec value) =
      mapping (WithLp.toLp 2 value) := by
  apply PiLp.ext
  intro row
  change (∑ column : Fin input, mapping (operatorBasis column) row * value column) =
    mapping (WithLp.toLp 2 value) row
  conv_rhs => rw [← operatorBasis_expansion (WithLp.toLp 2 value), map_sum]
  change (∑ column : Fin input, mapping (operatorBasis column) row * value column) =
    (PiLp.proj 2 (fun _ : Fin output => ℂ) row : PhysicalValue output →L[ℂ] ℂ)
      (∑ column : Fin input,
        mapping ((WithLp.toLp 2 value) column • operatorBasis column))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [map_smul]
  change mapping (operatorBasis column) row * value column =
    value column * mapping (operatorBasis column) row
  ring

/-- The literal global frame is nonsingular everywhere on the original disk
inside the explicit low ball. -/
theorem originalPhysicalFrameMatrix_isUnit_det_of_low
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (axialAngle : ℝ) (point : ClosedDisk) :
    IsUnit (originalPhysicalFrameMatrix parameters L epsilon field axialAngle point).det := by
  let deviation := originalPhysicalFrameDeviation parameters L epsilon field axialAngle point
  let mapping : OperatorValue 3 3 := referenceFrame + deviation
  have mappingInjective : Function.Injective mapping :=
    referenceFrame_add_injective_of_norm_lt_one deviation
      (originalPhysicalFrameDeviation_norm_lt_one_of_low parameters L epsilon field low
        axialAngle point)
  have matrixInjective : Function.Injective (operatorMatrix mapping).mulVec := by
    intro first second same
    have mappedSame : mapping (WithLp.toLp 2 first) = mapping (WithLp.toLp 2 second) := by
      rw [← operatorMatrix_mulVec, ← operatorMatrix_mulVec, same]
    have inputSame := mappingInjective mappedSame
    funext coordinate
    exact congrArg (fun value : PhysicalValue 3 => value coordinate) inputSame
  have matrixUnit : IsUnit (operatorMatrix mapping) :=
    Matrix.mulVec_injective_iff_isUnit.mp matrixInjective
  have determinantUnit : IsUnit (operatorMatrix mapping).det :=
    (Matrix.isUnit_iff_isUnit_det (operatorMatrix mapping)).mp matrixUnit
  exact determinantUnit

theorem originalPhysicalFrameMatrix_mul_inv_of_low
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (axialAngle : ℝ) (point : ClosedDisk) :
    originalPhysicalFrameMatrix parameters L epsilon field axialAngle point *
        (originalPhysicalFrameMatrix parameters L epsilon field axialAngle point)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _
    (originalPhysicalFrameMatrix_isUnit_det_of_low parameters L epsilon field low axialAngle point)

theorem originalPhysicalFrameMatrix_inv_mul_of_low
    (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (low : originalGradeNorm 4 field + |epsilon| ≤ originalFrameLowRadius parameters L)
    (axialAngle : ℝ) (point : ClosedDisk) :
    (originalPhysicalFrameMatrix parameters L epsilon field axialAngle point)⁻¹ *
        originalPhysicalFrameMatrix parameters L epsilon field axialAngle point = 1 := by
  exact Matrix.nonsing_inv_mul _
    (originalPhysicalFrameMatrix_isUnit_det_of_low parameters L epsilon field low axialAngle point)

end Grad.SourceCollar
