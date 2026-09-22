import SM8GradeCalculus

noncomputable section

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.COR12Extension

/-- The explicitly supplied same-grade real projection in P23. This does
not assert the existence of any unconstructed full-domain N projection. -/
structure SameGradeRealProjection (parameters : PhaseParameters) (dimension : ℕ) where
  map : ACore parameters dimension →ₗ[ℝ] ACore parameters dimension
  idempotent : ∀ field, map (map field) = map field
  bound : ℕ → ℝ
  boundNonnegative : ∀ grade, 0 ≤ bound grade
  bounded : ∀ grade, 3 ≤ grade → ∀ field,
    ‖GradeCore.ofCoreLinear (grade := grade) (map field)‖ ≤
      bound grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖
  real : ∀ field, cartesianCoreConjugation parameters (map field) =
    map (cartesianCoreConjugation parameters field)

namespace SameGradeRealProjection

variable {parameters : PhaseParameters} {dimension : ℕ}

theorem fixed (projection : SameGradeRealProjection parameters dimension)
    (field : projection.map.range) : projection.map field = field := by
  obtain ⟨source, equality⟩ := field.property
  rw [← equality, projection.idempotent]

/-- A concrete supplied projection for the ambient consumer. -/
def identity (parameters : PhaseParameters) (dimension : ℕ) :
    SameGradeRealProjection parameters dimension where
  map := LinearMap.id
  idempotent _ := rfl
  bound _ := 1
  boundNonnegative _ := zero_le_one
  bounded _ _ _ := by simp
  real _ := rfl

def gradeMap (projection : SameGradeRealProjection parameters dimension)
    (grade : ℕ) (gradeAdmissible : 3 ≤ grade) :
    GradeCore parameters dimension grade →L[ℝ] GradeCore parameters dimension grade :=
  ((GradeCore.ofCoreLinear.restrictScalars ℝ).comp
    (projection.map.comp (GradeCore.toCoreLinear.restrictScalars ℝ))).mkContinuous
      (projection.bound grade) (fun field => projection.bounded grade gradeAdmissible field.toCore)

end SameGradeRealProjection

def constrainedSmoothing {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) :
    projection.map.range →ₗ[ℝ] projection.map.range where
  toFun field := ⟨projection.map (ambientSmoothing parameters scale field),
    ⟨ambientSmoothing parameters scale field, rfl⟩⟩
  map_add' first second := by
    apply Subtype.ext
    exact (projection.map.comp ((ambientSmoothing parameters scale).restrictScalars ℝ)).map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    exact (projection.map.comp ((ambientSmoothing parameters scale).restrictScalars ℝ)).map_smul scalar field

def constrainedScaleDerivative {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (order : ℕ) (scale : ℝ) :
    projection.map.range →ₗ[ℝ] projection.map.range where
  toFun field := ⟨projection.map (ambientScaleDerivative parameters order scale field),
    ⟨ambientScaleDerivative parameters order scale field, rfl⟩⟩
  map_add' first second := by
    apply Subtype.ext
    exact (projection.map.comp ((ambientScaleDerivative parameters order scale).restrictScalars ℝ)).map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    exact (projection.map.comp ((ambientScaleDerivative parameters order scale).restrictScalars ℝ)).map_smul scalar field

theorem constrainedSmoothing_apply {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) (field : projection.map.range) :
    (constrainedSmoothing projection scale field).1 = projection.map (ambientSmoothing parameters scale field) := rfl

/-- The P24 remainder identity uses only `P h=h`, never a commutator. -/
theorem constrainedRemainder_apply {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) (field : projection.map.range) :
    field.1 - (constrainedSmoothing projection scale field).1 =
      projection.map (field.1 - ambientSmoothing parameters scale field.1) := by
  rw [map_sub, projection.fixed, constrainedSmoothing_apply]

theorem constrainedSmoothing_norm_le {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) (gradeAdmissible : 3 ≤ upper)
    (field : projection.map.range) :
    ‖GradeCore.ofCoreLinear (grade := upper) (constrainedSmoothing projection scale field).1‖ ≤
      (projection.bound upper * (sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ (upper - lower))) *
        scale ^ (upper - lower) * ‖GradeCore.ofCoreLinear (grade := lower) field.1‖ := by
  calc
    _ ≤ projection.bound upper *
        ‖GradeCore.ofCoreLinear (grade := upper) (ambientSmoothing parameters scale field.1)‖ :=
      projection.bounded upper gradeAdmissible _
    _ ≤ projection.bound upper *
        ((sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ (upper - lower)) *
          scale ^ (upper - lower) * ‖GradeCore.ofCoreLinear (grade := lower) field.1‖) :=
      mul_le_mul_of_nonneg_left (ambientSmoothing_norm_le parameters scale scalePositive lower upper ordered field.1)
        (projection.boundNonnegative upper)
    _ = _ := by ring

theorem constrainedRemainder_norm_le {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) (gradeAdmissible : 3 ≤ lower)
    (field : projection.map.range) :
    ‖GradeCore.ofCoreLinear (grade := lower) (field.1 - (constrainedSmoothing projection scale field).1)‖ ≤
      (projection.bound lower * (sameGradeConstant lower * sameGradeConstant upper)) *
        scale ^ ((lower : ℝ) - (upper : ℝ)) * ‖GradeCore.ofCoreLinear (grade := upper) field.1‖ := by
  rw [constrainedRemainder_apply]
  calc
    _ ≤ projection.bound lower *
        ‖GradeCore.ofCoreLinear (grade := lower) (field.1 - ambientSmoothing parameters scale field.1)‖ :=
      projection.bounded lower gradeAdmissible _
    _ ≤ projection.bound lower * ((sameGradeConstant lower * sameGradeConstant upper) *
        scale ^ ((lower : ℝ) - (upper : ℝ)) * ‖GradeCore.ofCoreLinear (grade := upper) field.1‖) :=
      mul_le_mul_of_nonneg_left (ambientRemainder_norm_le parameters scale scalePositive lower upper ordered field.1)
        (projection.boundNonnegative lower)
    _ = _ := by ring

theorem constrainedScaleDerivative_norm_le {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (lower upper order : ℕ) (positiveOrder : 0 < order) (gradeAdmissible : 3 ≤ upper)
    (field : projection.map.range) :
    ‖GradeCore.ofCoreLinear (grade := upper) (constrainedScaleDerivative projection order scale field).1‖ ≤
      (projection.bound upper * (sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ upper * profileBound order)) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) * ‖GradeCore.ofCoreLinear (grade := lower) field.1‖ := by
  calc
    _ ≤ projection.bound upper *
        ‖GradeCore.ofCoreLinear (grade := upper) (ambientScaleDerivative parameters order scale field.1)‖ :=
      projection.bounded upper gradeAdmissible _
    _ ≤ projection.bound upper *
        ((sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ upper * profileBound order) *
          scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) * ‖GradeCore.ofCoreLinear (grade := lower) field.1‖) :=
      mul_le_mul_of_nonneg_left
        (ambientScaleDerivative_norm_le parameters scale scalePositive lower upper order positiveOrder field.1)
        (projection.boundNonnegative upper)
    _ = _ := by ring

theorem constrainedScaleDerivative_hasDerivAt_grade {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (order grade : ℕ) (gradeAdmissible : 3 ≤ grade)
    (scale : ℝ) (positive : 0 < scale) (field : projection.map.range) :
    HasDerivAt (fun parameter => GradeCore.ofCoreLinear (grade := grade)
      (constrainedScaleDerivative projection order parameter field).1)
      (GradeCore.ofCoreLinear (grade := grade)
        (constrainedScaleDerivative projection (order + 1) scale field).1) scale :=
  (projection.gradeMap grade gradeAdmissible).hasFDerivAt.comp_hasDerivAt scale
    (ambientScaleDerivative_hasDerivAt_grade parameters order grade scale positive field.1)

end Grad.SmoothingFamily
