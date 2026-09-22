import AKN26OriginalCircleMeanConstraints

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints Grad.BoundaryTrace

theorem row_mode_zero_of_originalCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (mode : ℤ × ℤ)
    (zero : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      originalRowCoefficient parameters power lower field radius mode = 0) : field mode = 0 := by
  apply Lp.ext
  filter_upwards [zero, ae_restrict_mem measurableSet_Icc, Lp.coeFn_zero (E := ComplexEuclidean dimension)
    (p := 2) (μ := volume.restrict (Icc lower 1))] with radius equality inside zeroValue
  rw [zeroValue]
  have nonzero : (originalRowWeight parameters power radius mode : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (originalRowWeight_pos parameters power radius (positive.trans_le inside.1) mode).ne')
  exact (smul_eq_zero.mp equality).resolve_left nonzero

theorem restrictedCore_row_mean_zero {dimension grade power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (mean : angularCore parameters 0 field = 0)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (paid : power + 0 ≤ grade) (mode : ℤ × ℤ) (modeZero : mode.1 = 0) :
    completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) mode = 0 := by
  rw [restrictionRow_core_grade_independent parameters field lower positive bounded paid
    (by omega : power + 0 ≤ grade + 3)]
  apply row_mode_zero_of_originalCoefficient parameters power lower positive _ mode
  filter_upwards [restrictedRow_original_coefficient (power := power) lower positive bounded parameters
    (by omega : power ≤ grade + 3) (by omega)
    (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 3) field)) mode,
    ae_restrict_mem measurableSet_Icc] with radius literal inside
  rw [literal inside]
  simp only [completedOriginalCell_core, GradeCore.toCore_ofCore, modeZero]
  exact originalScalarCircle_mean_zero parameters field mean mode.2 radius
    (positive.le.trans inside.1) inside.2

theorem restrictionCore_rows_compatible {dimension grade power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (paid : power + 0 ≤ grade) :
    RadialRowsCompatible lower power
      (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)))
      (completedRestrictionRow (power := 0) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) := by
  intro mode
  rw [completedRestrictionRow_core, completedRestrictionRow_core]
  change ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • _ =
    ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (((annularFrequency mode.1 mode.2 : ℂ) ^ 0) • _)
  simp only [pow_zero, one_smul]

theorem radialRestrictionCore_row_mean_zero {grade power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters 2)
    (mean : radialSourceCore parameters field = 0)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (paid : power + 0 ≤ grade) (mode : ℤ × ℤ) (modeZero : mode.1 = 0) :
    radialRowContraction lower positive power
      (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) mode = 0 := by
  rw [restrictionRow_core_grade_independent parameters field lower positive bounded paid
    (by omega : power + 0 ≤ grade + 3)]
  rw [(restrictionCore_rows_compatible parameters field lower positive bounded
    (by omega : power + 0 ≤ grade + 3)).radial positive mode]
  suffices zero : radialRowContraction lower positive 0
      (completedRestrictionRow (power := 0) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 3) field))) mode = 0 by
    rw [zero, smul_zero]
  apply row_mode_zero_of_originalCoefficient parameters 0 lower positive _ mode
  have restricted := ae_all_iff.mpr (fun other : ℤ × ℤ =>
    restrictedRow_original_coefficient (power := 0) lower positive bounded parameters (by omega) (by omega)
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 3) field)) other)
  filter_upwards [restricted,
    radialRowContraction_decoded_ae parameters lower positive
      (completedRestrictionRow (power := 0) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + 3) field))),
    ae_restrict_mem measurableSet_Icc] with radius literal radial inside
  rw [radial mode]
  simp_rw [literal _ inside]
  simp only [completedOriginalCell_core, GradeCore.toCore_ofCore]
  have continuousField : Continuous (fun angle => (field.val mode.2).value
      (Grad.SourceCollarDivision.polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) :=
    (field.val mode.2).value.continuous.comp
      ((polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _)
  rw [← radialPolarField_coefficient _ continuousField, modeZero]
  exact originalRadialCircle_mean_zero parameters field mean mode.2 radius
    (positive.le.trans inside.1) inside.2

end Grad.ExhaustionSourceAllocation
