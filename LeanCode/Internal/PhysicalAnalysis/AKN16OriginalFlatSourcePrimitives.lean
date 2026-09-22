import AKN15ActualTiltedKappaProducts

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarRestriction Grad.SourceCollarBulk Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection
open Grad.ConstrainedGrades

/-- The original EX flat Cartesian source jets: f,h vanish through order2
and g through order1. These are actual field jets, before phase weighting. -/
def SourceHigherVanishing {parameters : PhaseParameters} (source : SmoothQuotient parameters) : Prop :=
  (∀ cell, VanishingJets 3 ((cartesianSourceVector source).val cell)) ∧
  (∀ cell, VanishingJets 2 ((source 2).val cell)) ∧
  (∀ cell, VanishingJets 3 ((source 3).val cell))

theorem originalPlanarCore_norm_le (parameters : PhaseParameters) (grade : ℕ) (source : SmoothQuotient parameters) :
    ‖GradeCore.ofCoreLinear (grade := grade) (cartesianSourceVector source)‖ ≤ ‖quotientEta parameters grade source‖ := by
  have bound := originalSourcePlanar_bound parameters grade (quotientEta parameters grade source)
  rw [originalSourcePlanar_core, aGradeEta_norm] at bound
  exact bound

theorem originalScalarCore_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (source : SmoothQuotient parameters) (component : Fin 4) :
    ‖GradeCore.ofCoreLinear (grade := grade) (source component)‖ ≤ ‖quotientEta parameters grade source‖ := by
  have bound := PiLp.norm_apply_le (quotientEta parameters grade source) component
  change ‖aGradeEta parameters (GradeCore.ofCoreLinear (source component))‖ ≤ _ at bound
  rw [aGradeEta_norm] at bound
  exact bound

def tiltedDivisionConstant (power : ℕ) (L : ℝ) : ℝ :=
  (2 * 2 ^ power + |L⁻¹|) * Real.sqrt (remainderAngularBoundConstant 3 power 0)

theorem tiltedDivisionConstant_nonnegative (power : ℕ) (L : ℝ) : 0 ≤ tiltedDivisionConstant power L := by
  unfold tiltedDivisionConstant
  positivity

theorem actualDividedSourceRows_tilted_bound {grade power : ℕ}
    (parameters : PhaseParameters) (L : ℝ) (source : SmoothQuotient parameters)
    (flat : SourceHigherVanishing source) (paid : power + 5 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (component : Fin 3) :
    ‖divisionHighWeight lower positive bounded
      (dividedSourceRows (power := power) lower positive bounded parameters L (by omega)
        (quotientEta parameters grade source) component)‖ ≤
      tiltedDivisionConstant power L * ‖quotientEta parameters grade source‖ := by
  have radial := (originalTiltedDividedRadial_bound parameters (cartesianSourceVector source) flat.1
      (by omega : 3 + power + 2 ≤ grade) lower positive bounded le_rfl).trans
    (mul_le_mul_of_nonneg_left (originalPlanarCore_norm_le parameters grade source) (by positivity))
  have tangential := (originalTiltedDividedTangential_bound parameters (cartesianSourceVector source) flat.1
      (by omega : 3 + power + 2 ≤ grade) lower positive bounded le_rfl).trans
    (mul_le_mul_of_nonneg_left (originalPlanarCore_norm_le parameters grade source) (by positivity))
  have fourth := (originalTiltedDivision_bound parameters (source 3) flat.2.2
      (by omega : 3 + power + 2 ≤ grade) lower positive bounded le_rfl).trans
    (mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters grade source 3) (Real.sqrt_nonneg _))
  have rootNonnegative := Real.sqrt_nonneg (remainderAngularBoundConstant 3 power 0)
  have sourceNonnegative := norm_nonneg (quotientEta parameters grade source)
  fin_cases component
  · change ‖divisionHighWeight lower positive bounded
      (radialRowContraction lower positive power (dividedPlanar lower positive bounded parameters _ _))‖ ≤ _
    rw [dividedPlanar, originalSourcePlanar_core]
    apply radial.trans
    unfold tiltedDivisionConstant
    nlinarith only [mul_nonneg (abs_nonneg L⁻¹) (mul_nonneg rootNonnegative sourceNonnegative)]
  · change ‖divisionHighWeight lower positive bounded
      (tangentialRowContraction lower positive power (dividedPlanar lower positive bounded parameters _ _))‖ ≤ _
    rw [dividedPlanar, originalSourcePlanar_core]
    apply tangential.trans
    unfold tiltedDivisionConstant
    nlinarith only [mul_nonneg (abs_nonneg L⁻¹) (mul_nonneg rootNonnegative sourceNonnegative)]
  · change ‖divisionHighWeight lower positive bounded
      ((L : ℂ)⁻¹ • completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters _
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (source 3))))‖ ≤ _
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← abs_inv]
    apply (mul_le_mul_of_nonneg_left fourth (abs_nonneg L⁻¹)).trans
    unfold tiltedDivisionConstant
    nlinarith only [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * 2 ^ power) (mul_nonneg rootNonnegative sourceNonnegative)]

theorem actualDividedSourceRows_tilted_low_bound {grade : ℕ}
    (parameters : PhaseParameters) (L : ℝ) (source : SmoothQuotient parameters)
    (flat : SourceHigherVanishing source) (paid : 5 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (component : Fin 3) :
    ‖divisionHighWeight lower positive bounded
      (dividedSourceRows (power := 0) lower positive bounded parameters L (by omega)
        (quotientEta parameters grade source) component)‖ ≤
      tiltedDivisionConstant 0 L * ‖quotientEta parameters 5 source‖ := by
  rw [← dividedSourceRows_lower lower positive bounded parameters L (by norm_num : 0 + 3 ≤ 5) paid
    (quotientEta parameters grade source) component, zLowering_core]
  exact actualDividedSourceRows_tilted_bound parameters L source flat (by norm_num) lower positive bounded component

end Grad.ExhaustionSourceAllocation
