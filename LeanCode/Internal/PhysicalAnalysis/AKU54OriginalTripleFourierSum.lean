import AKU51ActualScalarTimeTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

def tripleCellsEquiv : (Fin 3 → ℤ) ≃ ((ℤ × ℤ) × ℤ) where
  toFun cells := ((cells 0,cells 1),cells 2)
  invFun cells := ![cells.1.1,cells.1.2,cells.2]
  left_inv cells := by funext index; fin_cases index <;> rfl
  right_inv cells := rfl

theorem scalarTriple_hasSum (first second third : ℤ → ℂ) (firstValue secondValue thirdValue : ℂ)
    (firstSum : HasSum first firstValue) (secondSum : HasSum second secondValue) (thirdSum : HasSum third thirdValue)
    (firstNorm : Summable (fun cell => ‖first cell‖)) (secondNorm : Summable (fun cell => ‖second cell‖))
    (thirdNorm : Summable (fun cell => ‖third cell‖)) :
    HasSum (fun cells : Fin 3 → ℤ => first (cells 0) * second (cells 1) * third (cells 2))
      (firstValue*secondValue*thirdValue) := by
  have pairNorm : Summable (fun cells : ℤ×ℤ => ‖first cells.1 * second cells.2‖) := by
    simpa only [norm_mul] using firstNorm.mul_of_nonneg secondNorm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have pairs := firstSum.mul secondSum (summable_mul_of_summable_norm firstNorm secondNorm)
  have triples := pairs.mul thirdSum (summable_mul_of_summable_norm pairNorm thirdNorm)
  exact tripleCellsEquiv.hasSum_iff.mpr triples

theorem coreValue_component_absolute {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) (component : Fin dimension) :
    Summable (fun cell => ‖axialPhase cell angle * (field.val cell).value point component‖) := by
  let projection := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) component
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => ?_) ((Gauges.originalValueNorm_summable parameters field point).mul_left ‖projection‖)
  have bound := projection.le_opNorm (axialPhase cell angle • (field.val cell).value point)
  simpa only [projection,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,norm_smul,norm_axialPhase,one_mul] using bound

theorem coreValue_component_hasSum {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) (component : Fin dimension) :
    HasSum (fun cell => axialPhase cell angle * (field.val cell).value point component)
      (coreValue field point angle component) :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) component).hasSum (coreValue_summable field point angle).hasSum

/-- Absolute full-cell triple Fourier synthesis for the literal physical
column determinant; no truncation or rearrangement assumption is introduced. -/
theorem determinant_fullCells_hasSum {parameters : PhaseParameters}
    (first second third : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) :
    HasSum (fun cells : Fin 3 → ℤ => Grad.NonlinearQuotient.complexDeterminant
      (axialPhase (cells 0) angle • (first.val (cells 0)).value point)
      (axialPhase (cells 1) angle • (second.val (cells 1)).value point)
      (axialPhase (cells 2) angle • (third.val (cells 2)).value point))
      (Grad.NonlinearQuotient.complexDeterminant (coreValue first point angle)
        (coreValue second point angle) (coreValue third point angle)) := by
  have monomial (a b c : Fin 3) := scalarTriple_hasSum
    (fun cell => axialPhase cell angle * (first.val cell).value point a)
    (fun cell => axialPhase cell angle * (second.val cell).value point b)
    (fun cell => axialPhase cell angle * (third.val cell).value point c)
    (coreValue first point angle a) (coreValue second point angle b) (coreValue third point angle c)
    (coreValue_component_hasSum first point angle a) (coreValue_component_hasSum second point angle b)
    (coreValue_component_hasSum third point angle c) (coreValue_component_absolute first point angle a)
    (coreValue_component_absolute second point angle b) (coreValue_component_absolute third point angle c)
  have total := (((((monomial 0 1 2).sub (monomial 0 2 1)).sub (monomial 1 0 2)).add
    (monomial 2 0 1)).add (monomial 1 2 0)).sub (monomial 2 1 0)
  have expanded (a b c : ComplexEuclidean 3) : Grad.NonlinearQuotient.complexDeterminant a b c =
      a 0*b 1*c 2-a 0*b 2*c 1-a 1*b 0*c 2+a 2*b 0*c 1+a 1*b 2*c 0-a 2*b 1*c 0 := by
    rw [Grad.NonlinearQuotient.complexDeterminant_eq]
    ring
  simpa only [expanded,PiLp.smul_apply,smul_eq_mul] using total

end Grad.FinitePhysicalJetLift
