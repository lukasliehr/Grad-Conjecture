import AKAC20FullPhysicalProjectionAndScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarAngular
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.AnnularGeneralSourceRegularity

 theorem doubleCoefficient_cosine {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => (Real.cos angles.1 : ℂ) • field angles) mode =
      (2 : ℂ)⁻¹ • (doubleCoefficient field (mode.1-1,mode.2)+doubleCoefficient field (mode.1+1,mode.2)) := by
  unfold doubleCoefficient
  have inner (polar : ℝ) :
      angularCoefficient (fun axial => (Real.cos polar : ℂ) • field (polar,axial)) mode.2 =
        (Real.cos polar : ℂ) • angularCoefficient (fun axial => field (polar,axial)) mode.2 := by
    change angularCoefficient ((Real.cos polar : ℂ) • (fun axial => field (polar,axial))) mode.2 = _
    rw [angularCoefficient_smul_continuous]
  simp_rw [inner]
  exact angularCoefficient_cos_mul _
    (Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter field continuousField mode.2) mode.1

 theorem doubleCoefficient_sine {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => (Real.sin angles.1 : ℂ) • field angles) mode =
      (2*Complex.I : ℂ)⁻¹ • (doubleCoefficient field (mode.1-1,mode.2)-doubleCoefficient field (mode.1+1,mode.2)) := by
  unfold doubleCoefficient
  have inner (polar : ℝ) :
      angularCoefficient (fun axial => (Real.sin polar : ℂ) • field (polar,axial)) mode.2 =
        (Real.sin polar : ℂ) • angularCoefficient (fun axial => field (polar,axial)) mode.2 := by
    change angularCoefficient ((Real.sin polar : ℂ) • (fun axial => field (polar,axial))) mode.2 = _
    rw [angularCoefficient_smul_continuous]
  simp_rw [inner]
  exact angularCoefficient_sin_mul _
    (Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter field continuousField mode.2) mode.1

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem SmoothLowPhysicalRow.fullField_cosine (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.cosine.fullField bounded (radius,angles) =
      (Real.cos angles.1 : ℂ) • curves.fullField bounded (radius,angles) := by
  apply congrFun (curves.cosine.fullField_eq_of_doubleCoefficient bounded radius inside
    (fun angles => (Real.cos angles.1 : ℂ) • curves.fullField bounded (radius,angles))
    ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).smul
      (curves.fullField_continuous_angles bounded radius inside)) _ _ _) angles
  · intro axial polar
    change (Real.cos (polar+2*Real.pi) : ℂ) • curves.fullField bounded (radius,polar+2*Real.pi,axial) = _
    rw [Real.cos_add_two_pi,curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    change (Real.cos polar : ℂ) • curves.fullField bounded (radius,polar,axial+2*Real.pi) = _
    rw [curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    rw [doubleCoefficient_cosine _ (curves.fullField_continuous_angles bounded radius inside),
      curves.fullField_doubleCoefficient bounded radius inside,
      curves.fullField_doubleCoefficient bounded radius inside,
      curves.cosine.physicalCurve_coefficient bounded 0 radius inside mode,
      curves.physicalCurve_coefficient bounded 0 radius inside,
      curves.physicalCurve_coefficient bounded 0 radius inside]
    change _ = _ • ((2 : ℂ)⁻¹ •
      (weightedAngularHilbertShift parameters dimension 0 1 (curves.curve 0 radius) mode +
        weightedAngularHilbertShift parameters dimension 0 (-1) (curves.curve 0 radius) mode))
    simp only [weightedAngularHilbertShift_apply,annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul,sub_neg_eq_add]
    rw [smul_add,smul_add,smul_add]
    congr 1 <;> exact smul_comm _ _ _

theorem SmoothLowPhysicalRow.fullField_sine (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.sine.fullField bounded (radius,angles) =
      (Real.sin angles.1 : ℂ) • curves.fullField bounded (radius,angles) := by
  apply congrFun (curves.sine.fullField_eq_of_doubleCoefficient bounded radius inside
    (fun angles => (Real.sin angles.1 : ℂ) • curves.fullField bounded (radius,angles))
    ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst)).smul
      (curves.fullField_continuous_angles bounded radius inside)) _ _ _) angles
  · intro axial polar
    change (Real.sin (polar+2*Real.pi) : ℂ) • curves.fullField bounded (radius,polar+2*Real.pi,axial) = _
    rw [Real.sin_add_two_pi,curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    change (Real.sin polar : ℂ) • curves.fullField bounded (radius,polar,axial+2*Real.pi) = _
    rw [curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    rw [doubleCoefficient_sine _ (curves.fullField_continuous_angles bounded radius inside),
      curves.fullField_doubleCoefficient bounded radius inside,
      curves.fullField_doubleCoefficient bounded radius inside,
      curves.sine.physicalCurve_coefficient bounded 0 radius inside mode,
      curves.physicalCurve_coefficient bounded 0 radius inside,
      curves.physicalCurve_coefficient bounded 0 radius inside]
    change _ = _ • ((2*Complex.I : ℂ)⁻¹ •
      (weightedAngularHilbertShift parameters dimension 0 1 (curves.curve 0 radius) mode -
        weightedAngularHilbertShift parameters dimension 0 (-1) (curves.curve 0 radius) mode))
    simp only [weightedAngularHilbertShift_apply,annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul,sub_neg_eq_add]
    rw [smul_sub,smul_sub,smul_sub]
    congr 1 <;> exact smul_comm _ _ _

end Grad.ActualSmoothPhysicalField
