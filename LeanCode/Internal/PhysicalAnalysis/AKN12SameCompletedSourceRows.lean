import AKN11RadialScaleTransport

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.BoundaryTrace

theorem VanishingJets.value_of_pos {dimension depth : ℕ} {field : ClosedJet dimension}
    (flat : VanishingJets depth field) (positive : 0 < depth) : field.value (ambientClosedDisk 0) = 0 := by
  have origin : ambientClosedDisk (0 : SpatialPlane) = sourceOrigin := ambientClosedDisk_coe sourceOrigin
  rw [origin]
  simpa only [closedDerivative_zero_order] using flat 0 positive emptyCartesianWord

theorem originalValueFlat_core_of_vanishing {dimension grade depth : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (large : 3 ≤ grade)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (positive : 0 < depth) :
    OriginalValueFlat parameters large (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) := by
  intro cell
  rw [completedOriginalCell_core]
  exact (flat cell).value_of_pos positive

theorem sourceTiltRow_sameRestriction {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (vanishing : 2 ≤ depth) :
    RadialScaleRelated lower (fun radius => ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ))
      (sourceTiltRow parameters field flat paid lower positive bounded 0 (by omega))
      (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [sourceTiltRow_ae parameters field flat paid lower positive bounded 0 (by omega),
    restrictedRow_literal lower positive bounded parameters (by omega : power ≤ grade) (by omega : 3 ≤ grade)
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) mode,
    ae_restrict_mem measurableSet_Icc] with radius weighted original inside
  rw [weighted, original inside]
  simp_rw [completedOriginalCell_core, GradeCore.toCore_ofCore]
  rw [sourceCircleCoefficient_literal parameters mode.2 (field.val mode.2) radius
    (positive.trans_le inside.1).le inside.2]
  simp only [sourceTiltFactor, max_eq_right inside.1, Nat.cast_zero, sub_zero]
  rw [Complex.coe_smul]
  rw [smul_comm (Real.sqrt radius) (radius ^ (-9 / 4 : ℝ))]
  exact smul_comm _ _ _

theorem sourceTiltRow_sameDivision {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (vanishing : 3 ≤ depth) :
    RadialScaleRelated lower (fun radius => ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ))
      (sourceTiltRow parameters field flat paid lower positive bounded 1 (by omega))
      (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [sourceTiltRow_ae parameters field flat paid lower positive bounded 1 (by omega),
    dividedRow_flat_literal lower positive bounded parameters (by omega : power + 3 ≤ grade)
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))
      (originalValueFlat_core_of_vanishing parameters field (by omega) flat (by omega)) mode,
    ae_restrict_mem measurableSet_Icc] with radius weighted original inside
  rw [weighted, original inside]
  simp_rw [completedOriginalCell_core, GradeCore.toCore_ofCore]
  have radialPositive := positive.trans_le inside.1
  have coefficient : angularCoefficient (fun angle =>
      cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
        (radius⁻¹ • (field.val mode.2).value (polarClosedPoint radius angle radialPositive.le inside.2))) mode.1 =
      radius⁻¹ • sourceCircleCoefficient parameters mode.2 (field.val mode.2) radius mode.1 := by
    rw [sourceCircleCoefficient_literal parameters mode.2 (field.val mode.2) radius radialPositive.le inside.2]
    conv_lhs => arg 1; intro angle; rw [smul_comm]
    exact SourceCollarFullSource.angularCoefficient_real_smul _ _ _
  rw [coefficient]
  have factor : sourceTiltFactor lower 1 radius = radius ^ (-9 / 4 : ℝ) * radius⁻¹ := by
    simp only [sourceTiltFactor, max_eq_right inside.1, Nat.cast_one]
    rw [← Real.rpow_neg_one, ← Real.rpow_add radialPositive]
    congr 1
  rw [factor, mul_smul, Complex.coe_smul]
  rw [smul_comm (Real.sqrt radius) (radius ^ (-9 / 4 : ℝ))]
  exact smul_comm _ _ _

end Grad.ExhaustionSourceAllocation
