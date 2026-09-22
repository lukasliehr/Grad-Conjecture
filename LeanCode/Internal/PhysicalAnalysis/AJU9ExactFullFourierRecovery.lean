import AJU8FullClosedJointSmoothness
import AAZJ11ExactDoubleFourierCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularJointRegularity Grad.AnnularRegularity
open Grad.SourceCollarFullSource Grad.SourceCollarAngular

/-- The literal two-frequency series, with the original normalized angular
integrals. This helper is used only for exact coefficient recovery. -/
def physicalCharacterSeries (values : (ℤ × ℤ) → ComplexEuclidean 1)
    (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  ∑' mode, (cellExponential mode.1 angles.1 * cellExponential mode.2 angles.2) • values mode

theorem physicalCharacterSeries_hasSum (values : (ℤ × ℤ) → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) (angles : ℝ × ℝ) :
    HasSum (fun mode => (cellExponential mode.1 angles.1 * cellExponential mode.2 angles.2) • values mode)
      (physicalCharacterSeries values angles) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded summable
  intro mode
  simp only [norm_smul, norm_mul, cellExponential_norm, one_mul, le_refl]

theorem physicalCharacterSeries_angular_hasSum (values : (ℤ × ℤ) → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) (axial : ℝ) (angular : ℤ) :
    HasSum (fun mode => if angular = mode.1 then cellExponential mode.2 axial • values mode else 0)
      (angularCoefficient (fun polar => physicalCharacterSeries values (polar, axial)) angular) := by
  have integrated := angularCoefficient_hasSum
    (fun mode : (ℤ × ℤ) => fun polar =>
      (cellExponential mode.1 polar * cellExponential mode.2 axial) • values mode)
    (fun polar => physicalCharacterSeries values (polar, axial))
    (fun mode => ((Grad.BoundaryTrace.cellExponential_smooth mode.1).continuous.mul continuous_const).smul continuous_const)
    (fun mode => ‖values mode‖) summable
    (fun mode polar _ => by simp only [norm_smul, norm_mul, cellExponential_norm, one_mul, le_refl])
    (fun polar _ => physicalCharacterSeries_hasSum values summable (polar, axial)) angular
  apply integrated.congr_fun
  intro mode
  simp only [mul_smul]
  rw [angularCoefficient_character_mul, angularCoefficient_constant]
  simp only [sub_eq_zero]

/-- Both original Fourier integrals recover the actual high-mode vector,
with no use of a formal coefficient label or an assumed reconstruction law. -/
theorem physicalCharacterSeries_coefficient (values : (ℤ × ℤ) → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) (query : (ℤ × ℤ)) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => physicalCharacterSeries values (polar, axial)) query.1) query.2 = values query := by
  classical
  let terms (mode : (ℤ × ℤ)) (axial : ℝ) : ComplexEuclidean 1 :=
    if query.1 = mode.1 then cellExponential mode.2 axial • values mode else 0
  have continuousTerms (mode : (ℤ × ℤ)) : Continuous (terms mode) := by
    unfold terms
    split_ifs
    · exact (Grad.BoundaryTrace.cellExponential_smooth mode.2).continuous.smul continuous_const
    · exact continuous_const
  have bound (mode : (ℤ × ℤ)) (axial : ℝ) : ‖terms mode axial‖ ≤ ‖values mode‖ := by
    unfold terms
    split_ifs
    · simp only [norm_smul, cellExponential_norm, one_mul, le_refl]
    · simpa only [norm_zero] using norm_nonneg (values mode)
  have integrated := angularCoefficient_hasSum terms
    (fun axial => angularCoefficient (fun polar => physicalCharacterSeries values (polar, axial)) query.1)
    continuousTerms (fun mode => ‖values mode‖) summable (fun mode axial _ => bound mode axial)
    (fun axial _ => physicalCharacterSeries_angular_hasSum values summable axial query.1) query.2
  have equality (mode : (ℤ × ℤ)) :
      angularCoefficient (terms mode) query.2 = if mode = query then values query else 0 := by
    by_cases first : query.1 = mode.1
    · simp only [terms, if_pos first]
      rw [angularCoefficient_character_mul, angularCoefficient_constant]
      by_cases second : query.2 = mode.2
      · have same : mode = query := Prod.ext first.symm second.symm
        subst mode
        simp
      · have different : mode ≠ query := fun same => second (congrArg (fun x : (ℤ × ℤ) => x.2) same).symm
        simp only [sub_eq_zero, if_neg second, if_neg different]
    · have different : mode ≠ query := fun same => first (congrArg (fun x : (ℤ × ℤ) => x.1) same).symm
      simp only [terms, if_neg first, if_neg different]
      simpa only [ite_self] using (angularCoefficient_constant (0 : ComplexEuclidean 1) query.2)
  have sumEquality : (fun mode => angularCoefficient (terms mode) query.2) =
      (fun mode => if mode = query then values query else 0) := funext equality
  rw [sumEquality] at integrated
  exact integrated.tsum_eq.symm.trans (by simp)

end Grad.AnnularPhysicalFourier
