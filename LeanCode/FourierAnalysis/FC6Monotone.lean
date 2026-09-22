import FC5Proof

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The literal inclusion of unordered Cartesian multi-indices from grade
`lower` into grade `upper`.  It changes only the proof of the grade bound. -/
def gradeMultiIndexEmbedding {lower upper : ℕ} (gradeLe : lower ≤ upper) :
    GradeMultiIndex lower ↪ GradeMultiIndex upper where
  toFun index :=
    ⟨(⟨index.val.1.val, by omega⟩, ⟨index.val.2.val, by omega⟩), by
      change index.val.1.val + index.val.2.val ≤ upper
      exact index.property.trans gradeLe⟩
  inj' := by
    intro first second equality
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun index : GradeMultiIndex upper => index.val.1.val) equality
    · apply Fin.ext
      exact congrArg (fun index : GradeMultiIndex upper => index.val.2.val) equality

theorem gradeMultiIndexEmbedding_toCartesian {lower upper : ℕ}
    (gradeLe : lower ≤ upper) (index : GradeMultiIndex lower) :
    (gradeMultiIndexEmbedding gradeLe index).toCartesian = index.toCartesian := rfl

/-- One literal nonnegative summand before the finite multi-index sum. -/
def m2IndexEnergy {dimension grade : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ)
    (index : GradeMultiIndex grade) : ℝ :=
  cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
    ‖closedContinuousToDiskL2
      (closedMultiDerivative (phaseWeightedJet parameters cell (coefficients cell))
        index.toCartesian)‖ ^ 2

theorem m2IndexEnergy_nonneg {dimension grade : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ)
    (index : GradeMultiIndex grade) :
    0 ≤ m2IndexEnergy parameters coefficients cell index := by
  exact mul_nonneg (pow_nonneg (le_trans zero_le_one (cellFrequency_one_le cell)) _)
    (sq_nonneg _)

theorem m2IndexEnergy_grade_mono {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ)
    (index : GradeMultiIndex lower) :
    m2IndexEnergy parameters coefficients cell index ≤
      m2IndexEnergy parameters coefficients cell
        (gradeMultiIndexEmbedding gradeLe index) := by
  unfold m2IndexEnergy
  rw [gradeMultiIndexEmbedding_toCartesian]
  apply mul_le_mul_of_nonneg_right
  · apply pow_le_pow_right₀ (cellFrequency_one_le cell)
    exact Nat.mul_le_mul_left 2
      (Nat.sub_le_sub_right gradeLe (cartesianOrder index.toCartesian))
  · exact sq_nonneg _

/-- Every cell's lower-grade finite unordered multi-index energy is bounded
by the higher-grade energy with constant one and the identical phase. -/
theorem m2CellEnergy_grade_mono {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    m2CellEnergy parameters lower coefficients cell ≤
      m2CellEnergy parameters upper coefficients cell := by
  change (∑ index : GradeMultiIndex lower,
      m2IndexEnergy parameters coefficients cell index) ≤
    ∑ index : GradeMultiIndex upper,
      m2IndexEnergy parameters coefficients cell index
  calc
    _ ≤ ∑ index : GradeMultiIndex lower,
        m2IndexEnergy parameters coefficients cell
          (gradeMultiIndexEmbedding gradeLe index) := by
      apply Finset.sum_le_sum
      intro index _membership
      exact m2IndexEnergy_grade_mono parameters gradeLe coefficients cell index
    _ = ∑ index ∈ Finset.univ.image (gradeMultiIndexEmbedding gradeLe),
        m2IndexEnergy parameters coefficients cell index := by
      exact (Finset.sum_image
        (gradeMultiIndexEmbedding gradeLe).injective.injOn).symm
    _ ≤ ∑ index : GradeMultiIndex upper,
        m2IndexEnergy parameters coefficients cell index := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro index _membership _outside
      exact m2IndexEnergy_nonneg parameters coefficients cell index

/-- The literal M2 series is monotone between original grades, with the same
phase parameters and the same all-grade coefficient sequence. -/
theorem cartesianGradeCoordinates_norm_sq_mono {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper)
    (field : ACore parameters dimension) :
    ‖cartesianGradeCoordinates parameters lower field‖ ^ 2 ≤
      ‖cartesianGradeCoordinates parameters upper field‖ ^ 2 := by
  rw [cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  have summableLower :=
    (mem_originalCore_iff parameters field.1).mp field.property lower
  have summableUpper :=
    (mem_originalCore_iff parameters field.1).mp field.property upper
  exact summableLower.tsum_le_tsum
    (m2CellEnergy_grade_mono parameters gradeLe field.1) summableUpper

/-- Exact constant-one monotonicity of the installed original grade norms. -/
theorem cartesianGrade_norm_mono {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper)
    (field : ACore parameters dimension) :
    ‖GradeCore.ofCoreLinear (grade := lower) field‖ ≤
      ‖GradeCore.ofCoreLinear (grade := upper) field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gradeCore_norm_eq_cartesianGradeSeminorm,
    gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact cartesianGradeCoordinates_norm_sq_mono parameters gradeLe field

/-- The identity-on-coefficients complex-linear map between grade tags. -/
def gradeCoreInclusionLinear {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (_gradeLe : lower ≤ upper) :
    GradeCore parameters dimension upper →ₗ[ℂ]
      GradeCore parameters dimension lower :=
  GradeCore.ofCoreLinear.comp GradeCore.toCoreLinear

theorem gradeCoreInclusionLinear_toCore {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper)
    (field : GradeCore parameters dimension upper) :
    (gradeCoreInclusionLinear parameters gradeLe field).toCore = field.toCore := rfl

/-- The identity-on-coefficients inclusion as a bounded map of norm at most
one.  This is still a core map; no completed injectivity is asserted here. -/
def gradeCoreInclusion {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper) :
    GradeCore parameters dimension upper →L[ℂ]
      GradeCore parameters dimension lower :=
  (gradeCoreInclusionLinear parameters gradeLe).mkContinuous 1 (by
    intro field
    rw [one_mul]
    change ‖GradeCore.ofCoreLinear (grade := lower) field.toCore‖ ≤ ‖field‖
    simpa only [GradeCore.ofCore_toCore] using
      cartesianGrade_norm_mono parameters gradeLe field.toCore)

theorem gradeCoreInclusion_toCore {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper)
    (field : GradeCore parameters dimension upper) :
    (gradeCoreInclusion parameters gradeLe field).toCore = field.toCore := rfl

theorem gradeCoreInclusion_norm_le_one {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (gradeLe : lower ≤ upper) :
    ‖gradeCoreInclusion (dimension := dimension) parameters gradeLe‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

end Grad.CartesianState
