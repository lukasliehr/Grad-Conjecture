import AKDZ2FiniteCellPolarTensorIntegral
import AKDZ3FixedCollarIntegralReflection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.DiskExtension.Operator

/-- The full tensor density is unchanged under the exact time/radius
reflection; signs in radial derivative words disappear only inside norms. -/
theorem originalPolarDensity_reflection {dimension : ℕ} (field : ClosedJet dimension)
    (grade : ℕ) (point : ℝ×ℝ) :
    polarJetSquaredDensity (smoothClosedExtension field ∘ collarPlane) grade point =
      polarJetSquaredDensity (originalPolarValue field) grade (1-point.1,point.2) := by
  have representation : (smoothClosedExtension field ∘ collarPlane)=
      fun source : ℝ×ℝ => originalPolarValue field (1-source.1,source.2) := by
    funext source
    simp only [Function.comp_apply,originalPolarValue,polarPlane,sub_sub_cancel]
  unfold polarJetSquaredDensity
  rw [representation]
  apply Finset.sum_congr rfl
  intro order _
  rw [reflectedPolarTensor_norm]

/-- The literal fixed-collar density equals the radial/angular integral
of the SAME original polar extension, with no collar or phase change. -/
theorem fixedCollarIntegral_originalDensity {dimension : ℕ}
    (lower : ℝ) (bounded : lower<1) (field : ClosedJet dimension) (grade : ℕ) :
    fixedCollarIntegral lower (polarJetSquaredDensity (smoothClosedExtension field ∘ collarPlane) grade)=
      ∫ radius in lower..1,∫ angle in -Real.pi..Real.pi,
        polarJetSquaredDensity (originalPolarValue field) grade (radius,angle) := by
  have identity : polarJetSquaredDensity (smoothClosedExtension field ∘ collarPlane) grade=
      fun point : ℝ×ℝ => polarJetSquaredDensity (originalPolarValue field) grade (1-point.1,point.2) :=
    funext (originalPolarDensity_reflection field grade)
  rw [identity]
  exact fixedCollarIntegral_reflection lower bounded _
    (polarJetSquaredDensity_continuous _ (originalPolarValue_smooth field) grade)

theorem radialAngularIntegral_finsetSum {Index : Type*} (indices : Finset Index)
    (lower : ℝ) (functions : Index→ℝ×ℝ→ℝ) (continuousFunctions : ∀ index,Continuous (functions index)) :
    (∫ radius in lower..1,∫ angle in -Real.pi..Real.pi,∑ index∈indices,functions index (radius,angle))=
      ∑ index∈indices,∫ radius in lower..1,∫ angle in -Real.pi..Real.pi,functions index (radius,angle) := by
  have inner (radius : ℝ) :
      (∫ angle in -Real.pi..Real.pi,∑ index∈indices,functions index (radius,angle))=
      ∑ index∈indices,∫ angle in -Real.pi..Real.pi,functions index (radius,angle) := by
    apply intervalIntegral.integral_finsetSum
    intro index _
    exact ((continuousFunctions index).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simp_rw [inner]
  apply intervalIntegral.integral_finsetSum
  intro index _
  exact (timeIntegral_continuous
    (fun point : ℝ×ℝ => functions index (point.2,point.1))
    ((continuousFunctions index).comp (continuous_snd.prodMk continuous_fst))
    (-Real.pi) Real.pi (neg_le_self Real.pi_pos.le)).intervalIntegrable lower 1

/-- Every order in the original polar density is integrated before the
finite order sum is combined with the finite axial support. -/
theorem fixedCollarIntegral_originalDensity_orders {dimension : ℕ}
    (lower : ℝ) (bounded : lower<1) (field : ClosedJet dimension) (grade : ℕ) :
    fixedCollarIntegral lower (polarJetSquaredDensity (smoothClosedExtension field ∘ collarPlane) grade)=
      ∑ order∈Finset.range (grade+1),∫ radius in lower..1,∫ angle in -Real.pi..Real.pi,
        ‖iteratedFDeriv ℝ order (originalPolarValue field) (radius,angle)‖^2 := by
  rw [fixedCollarIntegral_originalDensity lower bounded field grade]
  unfold polarJetSquaredDensity
  exact radialAngularIntegral_finsetSum (Finset.range (grade+1)) lower
    (fun order point => ‖iteratedFDeriv ℝ order (originalPolarValue field) point‖^2)
    (fun order => ((originalPolarValue_smooth field).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞)≤⊤))).norm.pow 2)

end Grad.OriginalCollarNorm
