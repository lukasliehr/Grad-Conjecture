import AOC1OuterSmoothComposition

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualOuterCollar
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.AnnularSourceGraph Grad.BoundaryLift

def outerSectionField (mode : ℤ) (sectionValue : RadialContinuousSection 1 (1 / 2)) :
    C(ClosedDisk, ComplexEuclidean 1) :=
  ⟨fun point => outerRadialField mode (radialSectionExtension 1 (1 / 2) (by norm_num) sectionValue) point.val,
    ((outerCharacter_smooth mode).continuous.comp continuous_subtype_val).smul
      ((radialSectionExtension 1 (1 / 2) (by norm_num) sectionValue).continuous.comp continuous_subtype_val.norm)⟩

theorem outerSectionField_continuous (mode : ℤ) : Continuous (outerSectionField mode) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun pair : RadialContinuousSection 1 (1 / 2) × ClosedDisk =>
    outerCharacter mode pair.2.val • pair.1 (radialClamp (1 / 2) (by norm_num) ‖pair.2.val‖))
  exact ((outerCharacter_smooth mode).continuous.comp (continuous_subtype_val.comp continuous_snd)).smul
    (continuous_eval.comp (continuous_fst.prodMk
      ((radialClamp_continuous (1 / 2) (by norm_num)).comp (continuous_subtype_val.comp continuous_snd).norm)))

def actualOuterModeValue (mode : ℤ) (field : diskGrade) : C(ClosedDisk, ComplexEuclidean 1) :=
  outerSectionField mode (diskRadialValueSection (1 / 2) (by norm_num) (by norm_num) mode field)

theorem actualOuterModeValue_continuous (mode : ℤ) : Continuous (actualOuterModeValue mode) :=
  (outerSectionField_continuous mode).comp
    ((weightedRadialSection 1 (1 / 2) (by norm_num) (by norm_num)).continuous.comp
      (diskRadial (1 / 2) (by norm_num) (by norm_num) mode).continuous)

theorem radialSection_core_value (mode : ℤ) (core : ClosedJet 1)
    (radius : ℝ) (inside : radius ∈ Icc (1 / 2 : ℝ) 1) :
    radialSectionExtension 1 (1 / 2) (by norm_num)
      (diskRadialValueSection (1 / 2) (by norm_num) (by norm_num) mode (diskCoreInto core)) radius =
      Grad.SourceCollarDivision.radialCoefficientJet
        (Grad.SourceCollarRestriction.originalPolarValue core) mode 0 radius := by
  unfold diskRadialValueSection
  rw [diskRadial_core]
  change radialSectionExtension 1 (1 / 2) (by norm_num)
    (weightedRadialSection 1 (1 / 2) (by norm_num) (by norm_num)
      (weightedRadialCoreInto 1 (1 / 2)
        (diskRadialSmoothCore mode core))) radius = _
  rw [weightedRadialSection_core]
  change Grad.SourceCollarDivision.radialCoefficientJet
    (Grad.SourceCollarRestriction.originalPolarValue core) mode 0
      (radialClamp (1 / 2) (by norm_num) radius).val = _
  rw [radialClamp_eq (1 / 2) (by norm_num) radius inside]

theorem polarCharacter (mode : ℤ) (radius : ℝ) (positive : 0 < radius)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    unitComplexCoordinate (Grad.Constraints.polarClosedPoint radius bounded angle).val ^ mode =
      angularCharacter mode (-angle) := by
  have pointLaw : (Grad.Constraints.polarClosedPoint radius bounded angle).val =
      radius • Grad.BoundaryTrace.boundaryCirclePoint (angle : CellCircle) := by
    rw [Grad.Constraints.polarClosedPoint_coordinates, Grad.BoundaryTrace.boundaryCirclePoint_coe]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [Grad.BoundaryTrace.collarPlane]
  rw [pointLaw, unitComplexCoordinate_polar radius positive, circle_zpow_fourier,
    angularCharacter_neg_angle]
  change cellCharacter mode (angle : CellCircle) = cellExponential (-(-mode)) angle
  rw [neg_neg, cellCharacter_coe]

theorem radialMode_core_value (mode : ℤ) (core : ClosedJet 1) (point : ClosedDisk)
    (positive : 0 < ‖point.val‖) :
    unitComplexCoordinate point.val ^ mode •
      Grad.SourceCollarDivision.radialCoefficientJet
        (Grad.SourceCollarRestriction.originalPolarValue core) mode 0 ‖point.val‖ =
      (angularClosedJet mode core).value point := by
  obtain ⟨angle, polar⟩ := closedPoint_has_polar_angle point
  have radial := radialCoefficient_projection_value core mode ‖point.val‖ (norm_nonneg _) point.property
  have axis : Grad.SourceCollarDivision.polarClosedPoint ‖point.val‖ 0 (norm_nonneg _) point.property =
      axisClosedPoint ‖point.val‖ (by rw [abs_norm]; exact point.property) := by
    apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [Grad.SourceCollarDivision.polarClosedPoint,
      Grad.SourceCollarDivision.polarPlane, Grad.BoundaryTrace.collarPlane, axisClosedPoint]
  rw [axis] at radial
  have characterAt : unitComplexCoordinate point.val ^ mode = angularCharacter mode (-angle) :=
    (congrArg (fun next : ClosedDisk => unitComplexCoordinate next.val ^ mode) polar).symm.trans
      (polarCharacter mode _ positive _ angle)
  rw [radial, characterAt]
  exact (angularClosedJet_rotation_value mode core angle _).symm.trans
    (congrArg (angularClosedJet mode core).value polar)

theorem actualOuterModeValue_core (mode : ℤ) (core : ClosedJet 1) (point : ClosedDisk) :
    actualOuterModeValue mode (diskCoreInto core) point =
      outerCutoffScalar point.val • (angularClosedJet mode core).value point := by
  change ((outerCutoffScalar point.val : ℂ) * unitComplexCoordinate point.val ^ mode) •
    radialSectionExtension 1 (1 / 2) (by norm_num)
      (diskRadialValueSection (1 / 2) (by norm_num) (by norm_num) mode (diskCoreInto core)) ‖point.val‖ = _
  by_cases small : ‖point.val‖ ≤ (7 / 12 : ℝ)
  · have zero : outerCutoffScalar point.val = 0 := by
      unfold outerCutoffScalar
      rw [interiorCutoff_one (by simpa only [Metric.mem_closedBall, dist_zero_right] using small), sub_self]
    simp only [zero, Complex.ofReal_zero, zero_mul, zero_smul]
  · have lower : (1 / 2 : ℝ) ≤ ‖point.val‖ := by linarith [lt_of_not_ge small]
    rw [radialSection_core_value mode core _ ⟨lower, point.property⟩, mul_smul,
      radialMode_core_value mode core point (lt_of_lt_of_le (by norm_num) lower)]
    rfl

end Grad.ActualOuterCollar
