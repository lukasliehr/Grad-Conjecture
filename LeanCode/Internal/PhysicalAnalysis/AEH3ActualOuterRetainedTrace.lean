import AEH2RetainedBoundaryMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularVariational Grad.AnnularUniformBoundary Grad.AnnularTiltedReference
open Grad.AnnularGrades Grad.CircularHighWeak
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse

section OuterTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (angular cell : ℕ)

/-- The normalized current trace used by the physical boundary equation:
first decode the literal `b_m⁻¹` energy, take the SAME accepted outer trace,
and insert its high coefficients in the full AH16 positive trace. -/
def actualCurrentHighOuterTrace :
    annularEnergySpace lower length positive →L[ℂ]
      PositiveTrace parameters angular cell 1 :=
  (highBoundaryIntoPositive parameters angular cell).toContinuousLinearMap.comp
    ((uniformOuterTrace lower length positive lowerHalf lengthPositive).comp
      (bEnergyDecode lower length positive))

theorem actualCurrentHighOuterTrace_bound
    (field : annularEnergySpace lower length positive) :
    ‖actualCurrentHighOuterTrace parameters lower length positive lowerHalf
      lengthPositive angular cell field‖ ≤
      uniformOuterTraceConstant length * ‖field‖ := by
  change ‖highBoundaryIntoPositive parameters angular cell
    (uniformOuterTrace lower length positive lowerHalf lengthPositive
      (bEnergyDecode lower length positive field))‖ ≤ _
  rw [(highBoundaryIntoPositive parameters angular cell).norm_map]
  have traceBound :=
    (uniformOuterTrace lower length positive lowerHalf lengthPositive).le_opNorm
      (bEnergyDecode lower length positive field)
  have operatorBound :=
    (uniformOuterTrace_exists lower length positive lowerHalf lengthPositive).choose_spec.2
  have decodeBound : ‖bEnergyDecode lower length positive field‖ ≤ ‖field‖ := by
    simpa only [bEnergyDecode, one_mul] using
      annularEnergyDiagonal_bound lower length positive
        (fun mode => Real.sqrt (highMultiplier mode.val.1)) 1 (by norm_num)
        bEnergyDecode_bound field
  exact traceBound.trans ((mul_le_mul_of_nonneg_right operatorBound
    (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left decodeBound
      (uniformOuterTraceConstant_nonnegative length)))

/-- The trace above is exactly the already accepted AAG outer endpoint map;
the new construction only completes the physical Fourier index set. -/
theorem actualCurrentHighOuterTrace_same
    (field : annularEnergySpace lower length positive) :
    actualCurrentHighOuterTrace parameters lower length positive lowerHalf
      lengthPositive angular cell field =
    highBoundaryIntoPositive parameters angular cell
      (annularEnergyTrace lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive 1
        (bEnergyDecode lower length positive field)) := by
  change highBoundaryIntoPositive parameters angular cell
      (uniformOuterTrace lower length positive lowerHalf lengthPositive
        (bEnergyDecode lower length positive field)) = _
  rw [uniformOuterTrace_eq_annularEnergyTrace lower length positive lowerHalf
    (lowerHalf.trans_lt (by norm_num)) lengthPositive]

theorem actualCurrentHighOuterTrace_high
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    actualCurrentHighOuterTrace parameters lower length positive lowerHalf
      lengthPositive angular cell field mode.val =
    uniformOuterTrace lower length positive lowerHalf lengthPositive
      (bEnergyDecode lower length positive field) mode :=
  highBoundaryIntoPositive_high parameters angular cell _ mode

theorem actualCurrentHighOuterTrace_low
    (field : annularEnergySpace lower length positive) (mode : ℤ × ℤ)
    (low : ¬ 3 ≤ |mode.1|) :
    actualCurrentHighOuterTrace parameters lower length positive lowerHalf
      lengthPositive angular cell field mode = 0 :=
  highBoundaryIntoPositive_low parameters angular cell _ mode low

end OuterTrace

section RetainedVector

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (angular cell : ℕ)

private def retainedSevenSlotLinearMap :
    PositiveTrace parameters angular cell 1 →ₗ[ℂ]
      SevenSlotTrace parameters angular cell where
  toFun xi := actualSevenSlotTrace parameters length angular cell 0 xi 0
  map_add' := by
    intro first second
    apply PiLp.ext
    intro slot
    have left := actualSevenSlotTrace_components parameters length angular cell
      0 (first + second) 0
    have firstComponents := actualSevenSlotTrace_components parameters length angular cell
      0 first 0
    have secondComponents := actualSevenSlotTrace_components parameters length angular cell
      0 second 0
    fin_cases slot <;>
      simp [congrFun left, congrFun firstComponents, congrFun secondComponents, map_add]
  map_smul' := by
    intro scalar xi
    apply PiLp.ext
    intro slot
    have left := actualSevenSlotTrace_components parameters length angular cell
      0 (scalar • xi) 0
    have right := actualSevenSlotTrace_components parameters length angular cell
      0 xi 0
    fin_cases slot <;> simp [congrFun left, congrFun right, map_smul]

include lengthPositive

private theorem retainedSevenSlotLinearMap_bound
    (xi : PositiveTrace parameters angular cell 1) :
    ‖retainedSevenSlotLinearMap parameters length angular cell xi‖ ≤ 2 * ‖xi‖ := by
  have square := actualSevenSlotTrace_bound_sq parameters length lengthPositive
    angular cell 0 xi 0
  change ‖actualSevenSlotTrace parameters length angular cell 0 xi 0‖ ≤ _
  norm_num at square
  nlinarith [norm_nonneg (actualSevenSlotTrace parameters length angular cell 0 xi 0),
    norm_nonneg xi]

def retainedSevenSlotTrace :
    PositiveTrace parameters angular cell 1 →L[ℂ]
      SevenSlotTrace parameters angular cell :=
  (retainedSevenSlotLinearMap parameters length angular cell).mkContinuous 2
    (retainedSevenSlotLinearMap_bound parameters length lengthPositive angular cell)

@[simp] theorem retainedSevenSlotTrace_apply
    (xi : PositiveTrace parameters angular cell 1) :
    retainedSevenSlotTrace parameters length lengthPositive angular cell xi =
      actualSevenSlotTrace parameters length angular cell 0 xi 0 := rfl

/-- The literal three retained slots `(R xi, xi_zeta, xi)` as a bounded
linear map of the original positive trace. -/
def originalRetainedBoundaryLinear :
    PositiveTrace parameters angular cell 1 →L[ℂ]
      NegativeTrace parameters angular cell 3 :=
  (fullNegativeKernelAction parameters angular cell
    (retainedTupleProjectionKernel parameters)).comp
      ((sevenSlotFlatten parameters angular cell).comp
        (retainedSevenSlotTrace parameters length lengthPositive angular cell))

@[simp] theorem originalRetainedBoundaryLinear_apply
    (xi : PositiveTrace parameters angular cell 1) :
    originalRetainedBoundaryLinear parameters length lengthPositive angular cell xi =
      originalRetainedBoundaryVector parameters length angular cell xi := rfl

def originalRetainedBoundaryConstant : ℝ :=
  2 * fullKernelMoment parameters (angular + cell + 1)
    (retainedTupleProjectionKernel parameters)

omit lengthPositive in
theorem originalRetainedBoundaryConstant_nonnegative :
    0 ≤ originalRetainedBoundaryConstant parameters angular cell :=
  mul_nonneg (by norm_num) (fullKernelMoment_nonnegative parameters _ _)

theorem originalRetainedBoundaryLinear_bound
    (xi : PositiveTrace parameters angular cell 1) :
    ‖originalRetainedBoundaryLinear parameters length lengthPositive angular cell xi‖ ≤
      originalRetainedBoundaryConstant parameters angular cell * ‖xi‖ := by
  apply (fullNegativeKernelAction_bound parameters angular cell
    (retainedTupleProjectionKernel parameters)
    (sevenSlotFlatten parameters angular cell
      (retainedSevenSlotTrace parameters length lengthPositive angular cell xi))).trans
  rw [sevenSlotFlatten_norm]
  have slots := retainedSevenSlotLinearMap_bound parameters length lengthPositive
    angular cell xi
  unfold originalRetainedBoundaryConstant
  exact (mul_le_mul_of_nonneg_left slots
    (fullKernelMoment_nonnegative parameters _ _)).trans_eq (by ring)

end RetainedVector

end Grad.AnnularCurrentBoundary
