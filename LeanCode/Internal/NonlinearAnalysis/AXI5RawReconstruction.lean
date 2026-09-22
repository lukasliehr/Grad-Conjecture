import AXI4CoordinateInjectivity

noncomputable section

namespace Grad.RawSourceFaithfulness

open Grad.CartesianState Grad.AxisCore Grad.QuotientProjection Grad.RawForward

def rowProjection (parameters : PhaseParameters) (coordinate : Fin 4) :
    ZAmbient parameters 0 →L[ℂ] AGrade parameters 1 0 :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => AGrade parameters 1 0) coordinate

def rawReconstructionCompleted (parameters : PhaseParameters) :
    ZAmbient parameters 0 →L[ℂ] ZAmbient parameters 0 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => AGrade parameters 1 0)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (2 * Complex.I)⁻¹ •
        ((starZCompleted (dimension := 1) parameters).comp (rowProjection parameters 0) -
          (zCompleted (dimension := 1) parameters).comp (rowProjection parameters 1)),
      (1 / 2 : ℂ) •
        ((starZCompleted (dimension := 1) parameters).comp (rowProjection parameters 0) +
          (zCompleted (dimension := 1) parameters).comp (rowProjection parameters 1)),
      rowProjection parameters 3,
      (radiusSquaredCompleted (dimension := 1) parameters).comp (rowProjection parameters 2)])

theorem rawReconstructionCompleted_apply (parameters : PhaseParameters)
    (field : ZAmbient parameters 0) :
    (fun coordinate => rawReconstructionCompleted parameters field coordinate) =
      ![(2 * Complex.I)⁻¹ • (starZCompleted parameters (field 0) - zCompleted parameters (field 1)),
        (1 / 2 : ℂ) • (starZCompleted parameters (field 0) + zCompleted parameters (field 1)),
        field 3, radiusSquaredCompleted parameters (field 2)] := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem rawReconstructionCompleted_core (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    rawReconstructionCompleted parameters (quotientEta parameters 0 field) =
      quotientEta parameters 0 (rawReconstructionCore parameters field) := by
  apply PiLp.ext
  intro coordinate
  have literal := congrFun (rawReconstructionCompleted_apply parameters
    (quotientEta parameters 0 field)) coordinate
  rw [literal, rawReconstructionCore_apply]
  fin_cases coordinate
  · change (2 * Complex.I)⁻¹ •
        (starZCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear (field 0))) -
          zCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear (field 1)))) = _
    rw [starZCompleted_core, zCompleted_core]
    change _ = aGradeEta parameters (GradeCore.ofCoreLinear
      ((2 * Complex.I)⁻¹ •
        (Grad.NonlinearQuotientBounds.starZMulCore parameters (field 0) -
          Grad.NonlinearQuotientBounds.zMulCore parameters (field 1))))
    rw [map_smul, map_smul, map_sub, map_sub]
  · change (1 / 2 : ℂ) •
        (starZCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear (field 0))) +
          zCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear (field 1)))) = _
    rw [starZCompleted_core, zCompleted_core]
    change _ = aGradeEta parameters (GradeCore.ofCoreLinear
      ((1 / 2 : ℂ) •
        (Grad.NonlinearQuotientBounds.starZMulCore parameters (field 0) +
          Grad.NonlinearQuotientBounds.zMulCore parameters (field 1))))
    rw [map_smul, map_smul, map_add, map_add]
  · rfl
  · exact radiusSquaredCompleted_core parameters (field 2)

theorem rawReconstructionCompleted_injective (parameters : PhaseParameters) :
    Function.Injective (rawReconstructionCompleted parameters) := by
  suffices kernel : ∀ field, rawReconstructionCompleted parameters field = 0 → field = 0 by
    intro first second equality
    exact sub_eq_zero.mp (kernel (first - second) (by simp only [map_sub, equality, sub_self]))
  intro field equality
  have row (coordinate : Fin 4) := congrArg (fun output : ZAmbient parameters 0 => output coordinate) equality
  have difference : starZCompleted parameters (field 0) - zCompleted parameters (field 1) = 0 := by
    have equation := row 0
    rw [show rawReconstructionCompleted parameters field 0 = _ from
      congrFun (rawReconstructionCompleted_apply parameters field) 0] at equation
    exact (smul_eq_zero.mp equation).resolve_left (by norm_num)
  have sum : starZCompleted parameters (field 0) + zCompleted parameters (field 1) = 0 := by
    have equation := row 1
    rw [show rawReconstructionCompleted parameters field 1 = _ from
      congrFun (rawReconstructionCompleted_apply parameters field) 1] at equation
    exact (smul_eq_zero.mp equation).resolve_left (by norm_num)
  have starZero : starZCompleted parameters (field 0) = 0 := by
    rw [sub_eq_zero.mp difference] at sum ⊢
    rw [← two_smul ℂ] at sum
    exact (smul_eq_zero.mp sum).resolve_left (by norm_num)
  have zZero : zCompleted parameters (field 1) = 0 := by
    rw [← sub_eq_zero.mp difference]
    exact starZero
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · exact starZCompleted_injective parameters
      (starZero.trans (map_zero (starZCompleted parameters)).symm)
  · exact zCompleted_injective parameters (zZero.trans (map_zero _).symm)
  · exact radiusSquaredCompleted_injective parameters
      ((row 3).trans (map_zero (radiusSquaredCompleted parameters)).symm)
  · exact row 2

end Grad.RawSourceFaithfulness
