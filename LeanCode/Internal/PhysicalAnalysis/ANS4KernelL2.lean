import ANS3KernelDerivatives

noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Interval Topology
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.RepresentedKernel.SpatialProduct
open Grad.PhysicalFamily Grad.GaugeCoefficients.Radial Grad.ActualSmoothPDE

def kernelDerivativeFamily {dimension order : ℕ} (weight : ℝ → ℂ) (field : ClosedJet dimension)
    (word : CartesianWord order) (angle : ℝ) : C(ClosedDisk, ComplexEuclidean dimension) :=
  weight angle • orthogonalDerivative (planeRotationEquiv angle) field order word

theorem kernelDerivativeFamily_continuous {dimension order : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet dimension) (word : CartesianWord order) :
    Continuous (kernelDerivativeFamily weight field word) := by
  let integrand : SpatialPlane × ℝ → ComplexEuclidean dimension := fun argument =>
    weight argument.2 •
      smoothClosedExtension field (planeRotationAction argument.2 argument.1)
  have integrandSmooth : ContDiff ℝ ∞ integrand :=
    kernelRotationIntegrand_smooth weight weightSmooth (smoothClosedExtension_smooth field)
  have derivativeContinuous : Continuous (sliceListDerivative (List.ofFn word) integrand) :=
    (sliceListDerivative_smooth (List.ofFn word) integrandSmooth).continuous
  apply ContinuousMap.continuous_of_continuous_uncurry
  have equality : (fun argument : ℝ × ClosedDisk =>
      kernelDerivativeFamily weight field word argument.1 argument.2) =
      fun argument => sliceListDerivative (List.ofFn word) integrand (argument.2.val, argument.1) := by
    funext argument
    have listEquality := congrFun
      (sliceListDerivative_eq (List.ofFn word) integrandSmooth argument.1) argument.2.val
    have sectionSmooth : ContDiff ℝ ∞ (fun source => integrand (source, argument.1)) :=
      integrandSmooth.comp (contDiff_id.prodMk contDiff_const)
    exact (globalRotatedKernel_derivative weight weightSmooth argument.1 field word argument.2).symm.trans
      ((listDerivative_ofFn isOpen_univ order word sectionSmooth.contDiffOn (mem_univ _)).symm.trans
        listEquality.symm)
  change Continuous (fun argument : ℝ × ClosedDisk =>
    kernelDerivativeFamily weight field word argument.1 argument.2)
  rw [equality]
  exact derivativeContinuous.comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

theorem kernelRotationJet_derivative_continuousMap {dimension order : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet dimension) (word : CartesianWord order) :
    closedDerivative (kernelRotationJet weight weightSmooth field) order word =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi), kernelDerivativeFamily weight field word angle := by
  apply ContinuousMap.ext
  intro point
  rw [kernelRotationJet_derivative]
  change _ = ((2 * Real.pi)⁻¹ : ℝ) •
    (∫ angle in Icc (0 : ℝ) (2 * Real.pi), kernelDerivativeFamily weight field word angle) point
  rw [ContinuousMap.integral_apply
    (kernelDerivativeFamily_continuous weight weightSmooth field word).continuousOn.integrableOn_Icc]
  rfl

theorem kernelRotationJet_preserves_zero_derivatives {dimension order : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet dimension)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (kernelRotationJet weight weightSmooth field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  rw [kernelRotationJet_derivative]
  have zeroTerm (angle : ℝ) :
      orthogonalDerivative (planeRotationEquiv angle) field order word
        ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
    rw [← orthogonalJet_derivative]
    exact orthogonalJet_preserves_zero_derivatives (planeRotationEquiv angle) field zeroJets word
  simp only [zeroTerm, smul_zero, integral_zero]

end Grad.ActualAngularInverse
