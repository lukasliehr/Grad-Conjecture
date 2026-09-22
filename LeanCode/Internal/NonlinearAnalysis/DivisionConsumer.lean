import DivisionClosedIdentity

noncomputable section

namespace Grad.NonlinearDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds

/-- The accepted Laplacian core is cellwise the Laplacian jet. -/
theorem laplacianCore_val {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) :
    (laplacianCore parameters field).val cell = laplacianJet (field.val cell) := rfl

/-- Goal-only consumer on the accepted original core: the very same
`radialCore ∘ laplacianCore` map is radial division with loss two, with the
axis value one quarter of the Laplacian and the accepted two-grade estimate.
The rotational invariance and the zero axis value are assumed on the closed
disk only; no collar, no smooth extension hypothesis, no assumed identity. -/
theorem actualCoreRadialDivision {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension)
    (radial : ∀ cell, IsRotationInvariant (field.val cell))
    (origin : ∀ cell, (field.val cell).value closedOrigin = 0) :
    (∀ (cell : ℤ) (point : ClosedDisk), (field.val cell).value point =
      ‖point.val‖ ^ 2 • ((radialCore parameters (laplacianCore parameters field)).val cell).value point) ∧
    (∀ cell, ((radialCore parameters (laplacianCore parameters field)).val cell).value closedOrigin =
      (1 / 4 : ℝ) • ((laplacianCore parameters field).val cell).value closedOrigin) ∧
    ∀ grade, originalGradeNorm grade (radialCore parameters (laplacianCore parameters field)) ≤
      dilationGradeConstant grade * laplacianGradeConstant grade * originalGradeNorm (grade + 2) field := by
  have goal : RadialDivisionGoal := actualRadialDivision
  refine ⟨?_, ?_, ?_⟩
  · intro cell point
    rw [radialCore_actual parameters (laplacianCore parameters field) cell point, laplacianCore_val]
    exact (goal dimension (field.val cell) (radial cell) (origin cell)).1 point
  · intro cell
    rw [radialCore_actual parameters (laplacianCore parameters field) cell closedOrigin,
      laplacianCore_actual parameters field cell, laplacianCore_val]
    exact (goal dimension (field.val cell) (radial cell) (origin cell)).2
  · intro grade
    exact (radialCore_bound parameters grade _).trans
      ((mul_le_mul_of_nonneg_left (laplacianCore_bound parameters field grade)
        (dilationGradeConstant_nonnegative _)).trans_eq (mul_assoc _ _ _).symm)

/-- Goal-only consumer for one closed jet: the literal O11 identity at every
closed point together with the O12 axis value, read off the public goal. -/
theorem actualJetRadialDivision {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0)
    (point : ClosedDisk) :
    field.value point = ‖point.val‖ ^ 2 • integralCoefficient (laplacianJet field) point ∧
    integralCoefficient (laplacianJet field) closedOrigin =
      (1 / 4 : ℝ) • laplacianCoefficient field closedOrigin :=
  ⟨(actualRadialDivision dimension field radial origin).1 point,
    (actualRadialDivision dimension field radial origin).2⟩

end Grad.NonlinearDivision
