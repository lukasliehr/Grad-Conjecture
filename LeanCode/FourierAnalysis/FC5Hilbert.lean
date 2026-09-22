import FC5Definite

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

/-- The definite pullback inner product supplied by the injective COR03
coordinate map. -/
@[instance_reducible]
def cartesianGradeInnerCore {dimension grade : ℕ} (parameters : PhaseParameters) :
    InnerProductSpace.Core ℂ (GradeCore parameters dimension grade) where
  toCore := cartesianGradePreInnerCore parameters
  definite field equality := by
    apply gradeCore_eq_zero_of_coordinates_eq_zero parameters
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    change inner ℂ (gradeCoreCoordinates parameters field)
      (gradeCoreCoordinates parameters field) = 0
    exact equality

/-- The norm topology on the grade-tagged core induced by the literal M2
inner product.  This makes no completeness claim. -/
noncomputable instance gradeCoreNormedAddCommGroup {dimension grade : ℕ}
    {parameters : PhaseParameters} :
    NormedAddCommGroup (GradeCore parameters dimension grade) := by
  letI : InnerProductSpace.Core ℂ (GradeCore parameters dimension grade) :=
    cartesianGradeInnerCore parameters
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The intended complex inner-product-space boundary on `GradeCore`. -/
noncomputable instance gradeCoreInnerProductSpace {dimension grade : ℕ}
    {parameters : PhaseParameters} :
    InnerProductSpace ℂ (GradeCore parameters dimension grade) :=
  InnerProductSpace.ofCore
    (cartesianGradePreInnerCore (dimension := dimension) (grade := grade) parameters)

/-- The installed inner product is literally the COR04 pullback. -/
theorem gradeCore_inner_eq_cartesianGradeInner {dimension grade : ℕ}
    (parameters : PhaseParameters) (first second : GradeCore parameters dimension grade) :
    inner ℂ first second = cartesianGradeInner parameters first second := rfl

/-- The installed norm is exactly the literal COR04 M2 seminorm. -/
theorem gradeCore_norm_eq_cartesianGradeSeminorm {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    ‖field‖ = cartesianGradeSeminorm parameters field := by
  change Real.sqrt (Complex.re (cartesianGradeInner parameters field field)) = _
  rw [cartesianGradeInner_self]
  exact Real.sqrt_sq (apply_nonneg (cartesianGradeSeminorm parameters) field)

/-- Literal definiteness of the original grade seminorm. -/
theorem cartesianGradeSeminorm_eq_zero_iff {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    cartesianGradeSeminorm parameters field = 0 ↔ field = 0 := by
  rw [← gradeCore_norm_eq_cartesianGradeSeminorm, norm_eq_zero]

/-- The coordinate embedding is an actual complex-linear isometry. -/
def gradeCoreCoordinateIsometry {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →ₗᵢ[ℂ]
      lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2 :=
  LinearIsometry.mk
    (gradeCoreCoordinates (dimension := dimension) (grade := grade) parameters)
    (fun field => by
    rw [gradeCore_norm_eq_cartesianGradeSeminorm,
      cartesianGradeSeminorm_apply])

theorem gradeCoreCoordinateIsometry_injective {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    Function.Injective (gradeCoreCoordinateIsometry parameters :
      GradeCore parameters dimension grade →
        lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2) :=
  (gradeCoreCoordinateIsometry parameters).injective

end Grad.CartesianState
