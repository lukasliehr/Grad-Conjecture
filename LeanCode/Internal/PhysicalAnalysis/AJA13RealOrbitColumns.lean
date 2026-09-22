import AJA8ActualFullFormOrbit
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace Grad.AnnularHighInverseOrbit
open Grad.AnnularKernelOrbit

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def orbitColumns (angular cell : E) : OrbitParameter →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight angular + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight cell

theorem orbitColumns_apply (angular cell : E) (step : OrbitParameter) :
    orbitColumns angular cell step = step.1 • angular + step.2 • cell := rfl

theorem orbitColumns_norm_le (angular cell : E) :
    ‖orbitColumns angular cell‖ ≤ ‖angular‖ + ‖cell‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro step
  change ‖step.1 • angular + step.2 • cell‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add
    ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (norm_fst_le step) (norm_nonneg angular)))
    ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (norm_snd_le step) (norm_nonneg cell)))).trans_eq (by ring))

theorem orbitColumns_comp (mapping : E →L[ℝ] F) (angular cell : E) :
    mapping.comp (orbitColumns angular cell) = orbitColumns (mapping angular) (mapping cell) := by
  apply ContinuousLinearMap.ext
  intro step
  change mapping (step.1 • angular + step.2 • cell) = _
  rw [map_add, map_smul, map_smul]
  rfl

theorem orbitDifferential_comp [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (mapping : E →L[ℝ] F) (angular cell : E) :
    mapping.comp (orbitDifferential angular cell) = orbitColumns (mapping angular) (mapping cell) :=
  orbitColumns_comp mapping angular cell

theorem orbitColumns_add (first second third fourth : E) :
    orbitColumns first second + orbitColumns third fourth = orbitColumns (first + third) (second + fourth) := by
  apply ContinuousLinearMap.ext
  intro step
  change (step.1 • first + step.2 • second) + (step.1 • third + step.2 • fourth) =
    step.1 • (first + third) + step.2 • (second + fourth)
  simp only [smul_add]
  abel

private theorem addDerivative {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (first second : P → E) (df dg : P →L[ℝ] E) (point : P)
    (hf : HasFDerivAt first df point) (hg : HasFDerivAt second dg point) :
    HasFDerivAt (fun tau => first tau + second tau) (df + dg) point := hf.add hg

theorem sumOrbit_hasFDerivAt (first second : OrbitParameter → E) (firstAngular firstCell secondAngular secondCell : E)
    (point : OrbitParameter) (hf : HasFDerivAt first (orbitColumns firstAngular firstCell) point)
    (hg : HasFDerivAt second (orbitColumns secondAngular secondCell) point) :
    HasFDerivAt (fun tau => first tau + second tau)
      (orbitColumns (firstAngular + secondAngular) (firstCell + secondCell)) point := by
  have derivative := addDerivative first second _ _ point hf hg
  apply derivative.congr_fderiv
  exact orbitColumns_add _ _ _ _

/-- Every member of an actual two-parameter jet tower is smooth. -/
theorem orbitTower_contDiff_nat (jet : ℕ → ℕ → OrbitParameter → E)
    (derivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
      (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)
    (order angular cell : ℕ) : ContDiff ℝ order (jet angular cell) := by
  induction order generalizing angular cell with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun point => (derivative angular cell point).continuousAt)
  | succ order ih =>
    rw [show ((order + 1 : ℕ) : WithTop ℕ∞) = (order : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨fun point => (derivative angular cell point).differentiableAt, ?_, ?_⟩
    · intro impossible
      simp at impossible
    · intro direction
      have equality : (fun point => fderiv ℝ (jet angular cell) point direction) =
          fun point => direction.1 • jet (angular + 1) cell point + direction.2 • jet angular (cell + 1) point := by
        funext point
        rw [(derivative angular cell point).fderiv]
        rfl
      rw [equality]
      exact ((ih (angular + 1) cell).const_smul direction.1).add ((ih angular (cell + 1)).const_smul direction.2)

theorem orbitTower_contDiff (jet : ℕ → ℕ → OrbitParameter → E)
    (derivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
      (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)
    (angular cell : ℕ) : ContDiff ℝ ∞ (jet angular cell) := by
  rw [contDiff_infty]
  intro order
  exact orbitTower_contDiff_nat jet derivative order angular cell

end Grad.AnnularHighInverseOrbit
