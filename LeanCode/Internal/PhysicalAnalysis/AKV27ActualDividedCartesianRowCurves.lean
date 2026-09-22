import AKV26GenuineKappaSourceCurveProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.SourceCollarBulk
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection

theorem cartesianRestrictionRow_exact {dimension grade power radial : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (paid : power+radial ≤ grade) (field : ACore parameters dimension) :
    completedRestrictionRow lower positive bounded.le parameters paid
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) =
      cartesianWeightedRadialRow parameters lower positive bounded field power radial := by
  rw [completedRestrictionRow_core]
  apply lp.ext
  funext mode
  rfl

def actualRestrictedCoreRadialCurves {dimension grade : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : ACore parameters dimension) :
    OriginalRowRadialCurves parameters lower
      (completedRestrictionRow (power := 0) (radial := 0) lower positive bounded.le parameters (by omega)
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) := by
  rw [cartesianRestrictionRow_exact parameters lower positive bounded]
  exact cartesianOriginalRowRadialCurves parameters lower positive bounded field

def actualDividedCoreRadialCurves {dimension grade : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (large : 3 ≤ grade) (field : ACore parameters dimension)
    (flat : OriginalValueFlat parameters large (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) :
    OriginalRowRadialCurves parameters lower
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded.le parameters large
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))) := by
  apply (actualRestrictedCoreRadialCurves (grade := grade) parameters lower positive bounded field).divide positive
  have divided (mode : ℤ × ℤ) := dividedRow_original_coefficient lower positive bounded.le parameters large
    (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) flat mode
  have restricted (mode : ℤ × ℤ) := restrictedRow_original_coefficient lower positive bounded.le parameters
    (Nat.zero_le grade) large (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)) mode
  filter_upwards [ae_all_iff.mpr divided,ae_all_iff.mpr restricted,ae_restrict_mem measurableSet_Icc] with radius divided restricted inside
  intro mode
  rw [divided mode inside,restricted mode inside]
  have scalar : (fun angle => radius⁻¹ • completedOriginalCell parameters large mode.2
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))
        (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) =
      (radius : ℂ)⁻¹ • (fun angle => completedOriginalCell parameters large mode.2
        (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field))
          (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) := by
    funext angle
    simp only [Pi.smul_apply,← Complex.ofReal_inv,Complex.coe_smul]
  rw [scalar,angularCoefficient_smul_continuous]

/-- The three original divided inputs, in their literal SCS order
(F1/r,F0/r,F2/r), are smooth at every original Fourier grade. -/
def actualDividedSourceRadialCurves {grade : ℕ} (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (large : 3 ≤ grade)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (component : Fin 3) :
    OriginalRowRadialCurves parameters lower
      (dividedSourceRows (power := 0) lower positive bounded.le parameters length large
        (quotientEta parameters grade source) component) := by
  have flatInputs := originalFlatSource_division_inputs parameters large source flat
  have planarFlat : OriginalValueFlat parameters large
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (cartesianSourceVector source))) := by
    rw [← originalSourcePlanar_core]
    exact flatInputs.1
  have planar := actualDividedCoreRadialCurves parameters lower positive bounded large (cartesianSourceVector source) planarFlat
  have fourth := actualDividedCoreRadialCurves parameters lower positive bounded large (source 3) flatInputs.2
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => Fin.elim0 impossible))) component
  · change OriginalRowRadialCurves parameters lower (radialRowContraction lower positive 0
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded.le parameters large
        (originalSourcePlanar parameters grade (quotientEta parameters grade source))))
    rw [originalSourcePlanar_core]
    exact planar.radial positive
  · change OriginalRowRadialCurves parameters lower (tangentialRowContraction lower positive 0
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded.le parameters large
        (originalSourcePlanar parameters grade (quotientEta parameters grade source))))
    rw [originalSourcePlanar_core]
    exact planar.tangential positive
  · exact fourth.smul ((length : ℂ)⁻¹)

end Grad.AnnularGeneralSourceRegularity
