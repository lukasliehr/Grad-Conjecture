import AngularProjectionDerivatives
import ClosedJetIntegralL2

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.PhysicalFamily Grad.GaugeCoefficients.Radial
open Grad.RepresentedKernel.SpatialProduct

def angularDerivativeFamily {dimension order : ℕ} (mode : ℤ) (field : ClosedJet dimension)
    (word : CartesianWord order) (angle : ℝ) : C(ClosedDisk, ComplexEuclidean dimension) :=
  angularCharacter mode angle • orthogonalDerivative (planeRotationEquiv angle) field order word

theorem angularDerivativeFamily_continuous {dimension order : ℕ} (mode : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord order) :
    Continuous (angularDerivativeFamily mode field word) := by
  let integrand : SpatialPlane × ℝ → ComplexEuclidean dimension := fun argument =>
    angularCharacter mode argument.2 •
      smoothClosedExtension field (planeRotationAction argument.2 argument.1)
  have integrandSmooth : ContDiff ℝ ∞ integrand :=
    angularProjectionIntegrand_smooth mode (smoothClosedExtension_smooth field)
  have derivativeContinuous : Continuous (sliceListDerivative (List.ofFn word) integrand) :=
    (sliceListDerivative_smooth (List.ofFn word) integrandSmooth).continuous
  apply ContinuousMap.continuous_of_continuous_uncurry
  have equality : (fun argument : ℝ × ClosedDisk =>
      angularDerivativeFamily mode field word argument.1 argument.2) =
      fun argument => sliceListDerivative (List.ofFn word) integrand (argument.2.val, argument.1) := by
    funext argument
    have listEquality := congrFun
      (sliceListDerivative_eq (List.ofFn word) integrandSmooth argument.1) argument.2.val
    have sectionSmooth : ContDiff ℝ ∞ (fun source => integrand (source, argument.1)) :=
      integrandSmooth.comp (contDiff_id.prodMk contDiff_const)
    exact (globalRotatedCharacter_derivative mode argument.1 field word argument.2).symm.trans
      ((listDerivative_ofFn isOpen_univ order word sectionSmooth.contDiffOn (mem_univ _)).symm.trans
        listEquality.symm)
  change Continuous (fun argument : ℝ × ClosedDisk =>
    angularDerivativeFamily mode field word argument.1 argument.2)
  rw [equality]
  exact derivativeContinuous.comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

theorem angularClosedJet_derivative_continuousMap {dimension order : ℕ} (mode : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord order) :
    closedDerivative (angularClosedJet mode field) order word =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi), angularDerivativeFamily mode field word angle := by
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_derivative]
  change _ = ((2 * Real.pi)⁻¹ : ℝ) •
    (∫ angle in Icc (0 : ℝ) (2 * Real.pi), angularDerivativeFamily mode field word angle) point
  rw [ContinuousMap.integral_apply
    (angularDerivativeFamily_continuous mode field word).continuousOn.integrableOn_Icc]
  rfl

theorem angularClosedJet_preserves_zero_derivatives {dimension order : ℕ} (mode : ℤ)
    (field : ClosedJet dimension)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (angularClosedJet mode field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  rw [angularClosedJet_derivative]
  have zeroTerm (angle : ℝ) :
      orthogonalDerivative (planeRotationEquiv angle) field order word
        ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
    rw [← orthogonalJet_derivative]
    exact orthogonalJet_preserves_zero_derivatives (planeRotationEquiv angle) field zeroJets word
  simp only [zeroTerm, smul_zero, integral_zero]

end Grad.Constraints
