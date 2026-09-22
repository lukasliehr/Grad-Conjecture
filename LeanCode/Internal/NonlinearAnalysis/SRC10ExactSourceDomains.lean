import SRC9BS36Consumer

noncomputable section

namespace Grad.SourceCollarBulk

open Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarAngular
open Grad.CompatibleCompletion

private theorem q23CLMSmul_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (scalar : ℂ) (mapping : E →L[ℂ] F) (input : E) :
    (scalar • mapping) input = scalar • mapping input := rfl

/-- The literal planar-domain BS36 map.  Its domain is exactly the original
Cartesian `A^(t+2)` two-vector, rather than the encompassing fourfold source. -/
def completedPlanarForceS11
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ) :
    AGrade parameters 2 (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (annularS11 lower positive).comp
    (completedTangentialContraction lower positive bounded parameters
      (tangential + 1) 1)

theorem completedPlanarForceS11_bound
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (field : AGrade parameters 2 (tangential + 2)) :
    ‖completedPlanarForceS11 lower positive bounded parameters tangential field‖ ≤
      planarBulkConstant tangential * ‖field‖ := by
  exact (annularS11_norm_le lower positive _).trans
    (completedTangentialContraction_bound lower positive bounded parameters
      (tangential + 1) 1 field)

theorem completedPlanarForceS11_core
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (field : ACore parameters 2) :
    completedPlanarForceS11 lower positive bounded parameters tangential
        (aGradeEta parameters
          (GradeCore.ofCoreLinear (grade := tangential + 2) field)) =
      annularS11 lower positive
        (completedTangentialContraction lower positive bounded parameters
          (tangential + 1) 1
          (aGradeEta parameters
            (GradeCore.ofCoreLinear (grade := tangential + 2) field))) := rfl

/-- Exact factorization of the whole-source F0 map through its actual
two-component Cartesian source norm. -/
theorem completedForceS11_factor
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ) :
    completedForceS11 lower positive bounded parameters tangential =
      (completedPlanarForceS11 lower positive bounded parameters tangential).comp
        (originalSourcePlanar parameters (tangential + 2)) := rfl

/-- The exact lower-grade fourth-source operator required by BS36:
`A^(t+1)(h) -> S^(1;0)_t`, with no unused extra source derivative. -/
def completedFourthFromOriginal
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (tangential : ℕ) :
    AGrade parameters 1 (tangential + 1) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (L : ℂ)⁻¹ •
    completedRestriction (dimension := 1) lower positive bounded parameters tangential 1

theorem completedFourthFromOriginal_bound
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) (field : AGrade parameters 1 (tangential + 1)) :
    ‖completedFourthFromOriginal lower positive bounded parameters L tangential field‖ ≤
      (L⁻¹ * restrictionGraphConstant tangential 1) * ‖field‖ := by
  unfold completedFourthFromOriginal
  change ‖(L : ℂ)⁻¹ • completedRestriction lower positive bounded parameters
    tangential 1 field‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg LPositive.le]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (completedRestriction_bound lower positive bounded parameters tangential 1 field)
      (inv_nonneg.mpr LPositive.le))

theorem completedFourthFromOriginal_core_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (tangential : ℕ)
    (field : ACore parameters 1) (index : Fin 2) (mode : ℤ × ℤ) :
    (completedFourthFromOriginal lower positive bounded parameters L tangential
      (aGradeEta parameters
        (GradeCore.ofCoreLinear (grade := tangential + 1) field))).val index mode =
      (L : ℂ)⁻¹ • restrictionModeLp lower tangential index.val parameters field mode := by
  unfold completedFourthFromOriginal
  have core := completedRestriction_core lower positive bounded parameters tangential 1
    (GradeCore.ofCoreLinear (grade := tangential + 1) field) index mode
  rw [q23CLMSmul_apply]
  have scalarEvaluation :
      (((L : ℂ)⁻¹ • completedRestriction lower positive bounded parameters tangential 1
          (aGradeEta parameters
            (GradeCore.ofCoreLinear (grade := tangential + 1) field))).val index mode) =
        (L : ℂ)⁻¹ •
          (completedRestriction lower positive bounded parameters tangential 1
            (aGradeEta parameters
              (GradeCore.ofCoreLinear (grade := tangential + 1) field))).val index mode := by
    rfl
  simpa only [GradeCore.toCore_ofCore] using
    scalarEvaluation.trans (congrArg ((L : ℂ)⁻¹ • ·) core)

/-- Exact factorization of the old fourfold-source operator through the
standalone grade-`t+1` fourth component. -/
theorem completedFourthSource_factor
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (tangential : ℕ) :
    completedFourthSource lower positive bounded parameters L tangential =
      (completedFourthFromOriginal lower positive bounded parameters L tangential).comp
        ((completedInclusion parameters
          (show tangential + 1 ≤ tangential + 2 by omega)).comp
          (originalSourceComponent parameters (tangential + 2) 3)) := by
  apply ContinuousLinearMap.ext
  intro source
  rfl

/-- Exact source-domain form of BS36, uniform in the annular lower radius. -/
theorem actualBS36ExactSourceDomains
    (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) :
    (∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
      (field : AGrade parameters 2 (tangential + 2)),
      ‖completedPlanarForceS11 lower positive bounded parameters tangential field‖ ≤
        planarBulkConstant tangential * ‖field‖) ∧
    (∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
      (field : AGrade parameters 1 (tangential + 1)),
      ‖completedFourthFromOriginal lower positive bounded parameters L tangential field‖ ≤
        (L⁻¹ * restrictionGraphConstant tangential 1) * ‖field‖) := by
  exact ⟨fun lower positive bounded field =>
      completedPlanarForceS11_bound lower positive bounded parameters tangential field,
    fun lower positive bounded field =>
      completedFourthFromOriginal_bound lower positive bounded parameters L LPositive tangential field⟩

end Grad.SourceCollarBulk
