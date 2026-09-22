import AJA16ActualHighInverseSmooth
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
noncomputable section
set_option autoImplicit false
namespace Grad.AnnularCrossOrbit
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem complex_smul_parts (scalar : ℂ) (field : E) :
    scalar • field = scalar.re • field + scalar.im • (Complex.I • field) := by
  rw [← IsScalarTower.algebraMap_smul ℂ scalar.re field,
    ← IsScalarTower.algebraMap_smul ℂ scalar.im (Complex.I • field)]
  rw [smul_smul, ← add_smul]
  congr 1
  exact scalar.re_add_im.symm

def complexOfReal (mapping : E →L[ℝ] F)
    (commutes : ∀ field, mapping (Complex.I • field) = Complex.I • mapping field) : E →L[ℂ] F where
  toFun := mapping
  map_add' := mapping.map_add
  map_smul' scalar field := by
    change mapping (scalar • field) = scalar • mapping field
    rw [complex_smul_parts scalar field, map_add, map_smul, map_smul, commutes,
      complex_smul_parts scalar (mapping field)]
  cont := mapping.continuous

def imaginaryAction : E →L[ℝ] E := Complex.I • ContinuousLinearMap.id ℝ E

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem imaginary_twice (field : E) : Complex.I • (Complex.I • field) = -field := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

def complexPartReal (mapping : E →L[ℝ] F) : E →L[ℝ] F :=
  (1 / 2 : ℝ) • (mapping - Complex.I • mapping.comp imaginaryAction)

theorem complexPartReal_commutes (mapping : E →L[ℝ] F) (field : E) :
    complexPartReal mapping (Complex.I • field) = Complex.I • complexPartReal mapping field := by
  change (1 / 2 : ℝ) • (mapping (Complex.I • field) - Complex.I • mapping (Complex.I • (Complex.I • field))) =
    Complex.I • ((1 / 2 : ℝ) • (mapping field - Complex.I • mapping (Complex.I • field)))
  rw [imaginary_twice, map_neg, smul_neg, sub_neg_eq_add, smul_comm Complex.I (1 / 2 : ℝ),
    smul_sub, imaginary_twice, sub_neg_eq_add, add_comm]

def complexPart (mapping : E →L[ℝ] F) : E →L[ℂ] F :=
  complexOfReal (complexPartReal mapping) (complexPartReal_commutes mapping)

theorem complexPart_restrict (mapping : E →L[ℂ] F) : complexPart (mapping.restrictScalars ℝ) = mapping := by
  apply ContinuousLinearMap.ext
  intro field
  change (1 / 2 : ℝ) • (mapping field - Complex.I • mapping (Complex.I • field)) = mapping field
  rw [map_smul, imaginary_twice, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num

theorem complexPart_apply_bound (mapping : E →L[ℝ] F) (field : E) :
    ‖complexPart mapping field‖ ≤ ‖mapping‖ * ‖field‖ := by
  have first := mapping.le_opNorm field
  have second := mapping.le_opNorm (Complex.I • field)
  have triangle := norm_sub_le (mapping field) (Complex.I • mapping (Complex.I • field))
  simp only [norm_smul, Complex.norm_I, one_mul] at second triangle
  change ‖(1 / 2 : ℝ) • (mapping field - Complex.I • mapping (Complex.I • field))‖ ≤ _
  rw [norm_smul, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
  nlinarith only [first, second, triangle]

def complexPartLinear : (E →L[ℝ] F) →ₗ[ℝ] (E →L[ℂ] F) where
  toFun := complexPart
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro field
    change (1 / 2 : ℝ) • ((first field + second field) -
      Complex.I • (first (Complex.I • field) + second (Complex.I • field))) =
      (1 / 2 : ℝ) • (first field - Complex.I • first (Complex.I • field)) +
      (1 / 2 : ℝ) • (second field - Complex.I • second (Complex.I • field))
    rw [smul_add, add_sub_add_comm, smul_add]
  map_smul' scalar mapping := by
    apply ContinuousLinearMap.ext
    intro field
    change (1 / 2 : ℝ) • (scalar • mapping field - Complex.I • (scalar • mapping (Complex.I • field))) =
      scalar • ((1 / 2 : ℝ) • (mapping field - Complex.I • mapping (Complex.I • field)))
    rw [smul_comm Complex.I scalar, ← smul_sub, smul_comm (1 / 2 : ℝ) scalar]

/-- A norm-one real-linear retraction back to the original complex operator space. -/
def complexPartCLM : (E →L[ℝ] F) →L[ℝ] (E →L[ℂ] F) :=
  complexPartLinear.mkContinuous 1 (fun mapping => by
    change ‖complexPart mapping‖ ≤ 1 * ‖mapping‖
    rw [one_mul]
    exact ContinuousLinearMap.opNorm_le_bound (complexPart mapping) (norm_nonneg mapping)
      (complexPart_apply_bound mapping))

theorem complexPartCLM_restrict (mapping : E →L[ℂ] F) :
    complexPartCLM (mapping.restrictScalars ℝ) = mapping := complexPart_restrict mapping

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Smoothness of the real restriction returns smoothness in the SAME complex operator norm. -/
theorem complexOperator_contDiff_of_restrict (order : WithTop ℕ∞) (family : P → E →L[ℂ] F)
    (smooth : ContDiff ℝ order (fun point => (family point).restrictScalars ℝ)) :
    ContDiff ℝ order family := by
  have composed := (complexPartCLM (E := E) (F := F)).contDiff.comp smooth
  simpa only [Function.comp_def, complexPartCLM_restrict] using composed

end Grad.AnnularCrossOrbit
