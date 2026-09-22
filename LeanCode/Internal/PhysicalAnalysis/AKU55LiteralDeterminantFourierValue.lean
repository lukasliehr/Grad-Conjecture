import AKU54OriginalTripleFourierSum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem determinant_phase_factors {parameters : PhaseParameters}
    (first second third : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) (cells : Fin 3 → ℤ) :
    Grad.NonlinearQuotient.complexDeterminant
      (axialPhase (cells 0) angle • (first.val (cells 0)).value point)
      (axialPhase (cells 1) angle • (second.val (cells 1)).value point)
      (axialPhase (cells 2) angle • (third.val (cells 2)).value point) =
    axialPhase (∑ index, cells index) angle * Grad.NonlinearQuotient.complexDeterminant
      ((first.val (cells 0)).value point) ((second.val (cells 1)).value point) ((third.val (cells 2)).value point) := by
  simp only [Fin.sum_univ_three,axialPhase_add,Grad.NonlinearQuotient.complexDeterminant_eq,
    PiLp.smul_apply,smul_eq_mul]
  ring

theorem determinant_originalCoefficient_hasSum {parameters : PhaseParameters}
    (first second third : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) (cell : ℤ) :
    HasSum (fun assignment : CellAssignments 3 cell => axialPhase cell angle *
      Grad.NonlinearQuotient.complexDeterminant ((first.val (assignment.val 0)).value point)
        ((second.val (assignment.val 1)).value point) ((third.val (assignment.val 2)).value point))
      (axialPhase cell angle * ((determinantOperation parameters first second third).val cell).value point 0) := by
  have actual : ((determinantOperation parameters first second third).val cell).value point =
      productCoefficientValue determinantMultilinear ![first,second,third] cell point :=
    actualMultilinearProduct_isActual parameters determinantMultilinear ![first,second,third] cell point
  have sum := (productValue_summable (by decide : 0 < 3) determinantMultilinear ![first,second,third] cell point).hasSum
  have scalar := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).hasSum sum
  change HasSum (fun assignment : CellAssignments 3 cell => determinantMultilinear
    (fun index => ((![first,second,third] index).val (assignment.val index)).value point) 0)
      (productCoefficientValue determinantMultilinear ![first,second,third] cell point 0) at scalar
  rw [← actual] at scalar
  have terms (assignment : CellAssignments 3 cell) :
      (fun index => ((![first,second,third] index).val (assignment.val index)).value point) =
      ![(first.val (assignment.val 0)).value point,(second.val (assignment.val 1)).value point,
        (third.val (assignment.val 2)).value point] := by funext index; fin_cases index <;> rfl
  simpa only [terms,determinantMultilinear_value] using scalar.mul_left (axialPhase cell angle)

/-- The actual retained triple convolution equals the literal physical
column determinant after full Fourier synthesis. -/
theorem coreValue_determinantOperation {parameters : PhaseParameters}
    (first second third : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) :
    coreValue (determinantOperation parameters first second third) point angle 0 =
      Grad.NonlinearQuotient.complexDeterminant (coreValue first point angle)
        (coreValue second point angle) (coreValue third point angle) := by
  have allCells := determinant_fullCells_hasSum first second third point angle
  simp only [determinant_phase_factors] at allCells
  have fibers := (Equiv.sigmaFiberEquiv (fun cells : Fin 3 → ℤ => ∑ index, cells index)).hasSum_iff.mpr allCells
  have fiberSum : HasSum (fun cell => axialPhase cell angle *
      ((determinantOperation parameters first second third).val cell).value point 0)
      (Grad.NonlinearQuotient.complexDeterminant (coreValue first point angle)
        (coreValue second point angle) (coreValue third point angle)) := by
    apply fibers.sigma
    intro cell
    apply (determinant_originalCoefficient_hasSum first second third point angle cell).congr_fun
    intro assignment
    change axialPhase (∑ index, assignment.val index) angle *
      Grad.NonlinearQuotient.complexDeterminant ((first.val (assignment.val 0)).value point)
        ((second.val (assignment.val 1)).value point) ((third.val (assignment.val 2)).value point) = _
    rw [assignment.property]
  exact (coreValue_component_hasSum (determinantOperation parameters first second third) point angle 0).unique fiberSum

end Grad.FinitePhysicalJetLift
