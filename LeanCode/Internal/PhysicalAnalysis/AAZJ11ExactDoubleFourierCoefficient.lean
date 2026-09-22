import AAZJ10JointSmoothReconstruction
import SCS26FourierSumInterchange
import SCS35MeanFreeFourier
import TRM9LiteralFourierShift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity
open Grad.SourceCollarFullSource Grad.SourceCollarAngular

/-- The literal two-frequency series, with the original normalized angular
integrals. This helper is used only for exact coefficient recovery. -/
def annularCharacterSeries (values : HighAnnularMode → ComplexEuclidean 1)
    (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  ∑' mode, (cellExponential mode.val.1 angles.1 * cellExponential mode.val.2 angles.2) • values mode

theorem annularCharacterSeries_hasSum (values : HighAnnularMode → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) (angles : ℝ × ℝ) :
    HasSum (fun mode => (cellExponential mode.val.1 angles.1 * cellExponential mode.val.2 angles.2) • values mode)
      (annularCharacterSeries values angles) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded summable
  intro mode
  simp only [norm_smul, norm_mul, cellExponential_norm, one_mul, le_refl]

theorem annularCharacterSeries_angular_hasSum (values : HighAnnularMode → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) (axial : ℝ) (angular : ℤ) :
    HasSum (fun mode => if angular = mode.val.1 then cellExponential mode.val.2 axial • values mode else 0)
      (angularCoefficient (fun polar => annularCharacterSeries values (polar, axial)) angular) := by
  have integrated := angularCoefficient_hasSum
    (fun mode : HighAnnularMode => fun polar =>
      (cellExponential mode.val.1 polar * cellExponential mode.val.2 axial) • values mode)
    (fun polar => annularCharacterSeries values (polar, axial))
    (fun mode => ((Grad.BoundaryTrace.cellExponential_smooth mode.val.1).continuous.mul continuous_const).smul continuous_const)
    (fun mode => ‖values mode‖) summable
    (fun mode polar _ => by simp only [norm_smul, norm_mul, cellExponential_norm, one_mul, le_refl])
    (fun polar _ => annularCharacterSeries_hasSum values summable (polar, axial)) angular
  apply integrated.congr_fun
  intro mode
  simp only [mul_smul]
  rw [angularCoefficient_character_mul, angularCoefficient_constant]
  simp only [sub_eq_zero]

/-- Both original Fourier integrals recover the actual high-mode vector,
with no use of a formal coefficient label or an assumed reconstruction law. -/
theorem annularCharacterSeries_coefficient (values : HighAnnularMode → ComplexEuclidean 1)
    (summable : Summable (fun mode => ‖values mode‖)) (query : HighAnnularMode) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => annularCharacterSeries values (polar, axial)) query.val.1) query.val.2 = values query := by
  classical
  let terms (mode : HighAnnularMode) (axial : ℝ) : ComplexEuclidean 1 :=
    if query.val.1 = mode.val.1 then cellExponential mode.val.2 axial • values mode else 0
  have continuousTerms (mode : HighAnnularMode) : Continuous (terms mode) := by
    unfold terms
    split_ifs
    · exact (Grad.BoundaryTrace.cellExponential_smooth mode.val.2).continuous.smul continuous_const
    · exact continuous_const
  have bound (mode : HighAnnularMode) (axial : ℝ) : ‖terms mode axial‖ ≤ ‖values mode‖ := by
    unfold terms
    split_ifs
    · simp only [norm_smul, cellExponential_norm, one_mul, le_refl]
    · simpa only [norm_zero] using norm_nonneg (values mode)
  have integrated := angularCoefficient_hasSum terms
    (fun axial => angularCoefficient (fun polar => annularCharacterSeries values (polar, axial)) query.val.1)
    continuousTerms (fun mode => ‖values mode‖) summable (fun mode axial _ => bound mode axial)
    (fun axial _ => annularCharacterSeries_angular_hasSum values summable axial query.val.1) query.val.2
  have equality (mode : HighAnnularMode) :
      angularCoefficient (terms mode) query.val.2 = if mode = query then values query else 0 := by
    by_cases first : query.val.1 = mode.val.1
    · simp only [terms, if_pos first]
      rw [angularCoefficient_character_mul, angularCoefficient_constant]
      by_cases second : query.val.2 = mode.val.2
      · have same : mode = query := Subtype.ext (Prod.ext first.symm second.symm)
        subst mode
        simp
      · have different : mode ≠ query := fun same => second (congrArg (fun x : HighAnnularMode => x.val.2) same).symm
        simp only [sub_eq_zero, if_neg second, if_neg different]
    · have different : mode ≠ query := fun same => first (congrArg (fun x : HighAnnularMode => x.val.1) same).symm
      simp only [terms, if_neg first, if_neg different]
      simpa only [ite_self] using (angularCoefficient_constant (0 : ComplexEuclidean 1) query.val.2)
  have sumEquality : (fun mode => angularCoefficient (terms mode) query.val.2) =
      (fun mode => if mode = query then values query else 0) := funext equality
  rw [sumEquality] at integrated
  exact integrated.tsum_eq.symm.trans (by simp)

end Grad.AnnularJointRegularity
