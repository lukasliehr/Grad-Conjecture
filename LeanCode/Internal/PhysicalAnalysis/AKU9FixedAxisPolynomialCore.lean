import AKU8OriginalFlatSourceHessian

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearProduct

/-- Insert an actual scalar axis coefficient into a fixed closed Cartesian jet. -/
def fixedAxisJetRaw {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters 1) (profile : ClosedJet dimension) :
    ℤ → ClosedJet dimension := fun cell => (data.val cell 0) • profile

theorem fixedAxisJet_row_bound {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters 1) (profile : ClosedJet dimension)
    (grade : ℕ) {constant : ℝ} (bound : ∀ cell,
      ‖cellGradeRowLinear (grade := grade) parameters cell profile‖ ≤
        constant * axisWeight parameters grade cell) (cell : ℤ) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (fixedAxisJetRaw data profile cell)‖ ≤
      constant * (axisWeight parameters grade cell * ‖data.val cell‖) := by
  rw [fixedAxisJetRaw,map_smul,norm_smul]
  calc _ ≤ ‖data.val cell‖ * (constant * axisWeight parameters grade cell) :=
    mul_le_mul (PiLp.norm_apply_le _ _) (bound cell) (norm_nonneg _) (norm_nonneg _)
  _ = _ := by ring

theorem fixedAxisJet_mem {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters 1) (profile : ClosedJet dimension) :
    fixedAxisJetRaw data profile ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨constant,nonnegative,bound⟩ := fixedJet_row_bound parameters profile grade
  apply ((lp.memℓp (Grad.AxisCore.axisEta parameters 1 grade data)).const_smul (constant : ℂ)).mono'
  intro cell
  change ‖cellGradeRowLinear (grade := grade) parameters cell (fixedAxisJetRaw data profile cell)‖ ≤ _
  apply (fixedAxisJet_row_bound data profile grade bound cell).trans_eq
  rw [Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg nonnegative,
    Grad.AxisCore.axisEta_apply,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le]
  rfl

def fixedAxisJetCore {parameters : PhaseParameters} {dimension : ℕ}
    (profile : ClosedJet dimension) : Grad.AxisCore.AxisSmoothCore parameters 1 →ₗ[ℂ] ACore parameters dimension where
  toFun data := ⟨fixedAxisJetRaw data profile,fixedAxisJet_mem data profile⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact add_smul _ _ _
  map_smul' scalar data := by
    apply Subtype.ext
    funext cell
    exact mul_smul _ _ _

theorem fixedAxisJetCore_val {parameters : PhaseParameters} {dimension : ℕ}
    (profile : ClosedJet dimension) (data : Grad.AxisCore.AxisSmoothCore parameters 1) (cell : ℤ) :
    (fixedAxisJetCore profile data).val cell = (data.val cell 0) • profile := rfl

/-- Same original analytic width and same grade; phase derivatives are paid by
exactly the existing axis weight in the accepted fixed-profile row bound. -/
theorem fixedAxisJetCore_bound {parameters : PhaseParameters} {dimension : ℕ}
    (profile : ClosedJet dimension) (grade : ℕ) : ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ data : Grad.AxisCore.AxisSmoothCore parameters 1,
        originalGradeNorm grade (fixedAxisJetCore profile data) ≤
          constant * ‖Grad.AxisCore.axisEta parameters 1 grade data‖ := by
  obtain ⟨constant,nonnegative,bound⟩ := fixedJet_row_bound parameters profile grade
  refine ⟨constant,nonnegative,fun data => ?_⟩
  exact originalGradeNorm_le_of_axis_row _ grade constant nonnegative data grade
    (fixedAxisJet_row_bound data profile grade bound)

end Grad.FinitePhysicalJetLift
