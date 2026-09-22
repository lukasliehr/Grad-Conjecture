import AKCQ15JointPhysicalKernelAllocation
import AJH4SamePolynomialInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness

/-- Extract one literal Fourier matrix entry from a bounded polynomial
operator. This observation is used only to prove derivative fidelity. -/
def fourierEntryObservation {source target : ℕ} (output input : ℤ × ℤ) :
    (CellL2 source →L[ℂ] CellL2 target) →L[ℂ]
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :=
  ((ContinuousLinearMap.compL ℂ (ComplexEuclidean source) (CellL2 target) (ComplexEuclidean target))
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean target) 2 output)).comp
      ((ContinuousLinearMap.compL ℂ (ComplexEuclidean source) (CellL2 source) (CellL2 target)).flip
        (lp.singleContinuousLinearMap ℂ (fun _ : ℤ × ℤ => ComplexEuclidean source) 2 input))

theorem fourierEntryObservation_apply {source target : ℕ} (output input : ℤ × ℤ)
    (mapping : CellL2 source →L[ℂ] CellL2 target) (value : ComplexEuclidean source) :
    fourierEntryObservation output input mapping value = mapping (lp.single 2 input value) output := rfl

/-- The observation returns the SAME full-kernel entry, at polynomial
power zero, without using a replacement kernel or analytic norm. -/
theorem fourierEntryObservation_kernel {source target : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters source target) (shift input : ℤ × ℤ) :
    fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (polynomialKernelAction parameters 0 kernel) = kernel.entry shift input := by
  apply ContinuousLinearMap.ext
  intro value
  rw [fourierEntryObservation_apply]
  have observed := polynomialKernelAction_coefficient parameters 0 kernel (lp.single 2 input value)
    ((twoFrequencyTranslation shift).symm input)
  apply observed.unique
  apply (hasSum_ite_eq shift (kernel.entry shift input value)).congr_fun
  intro other
  by_cases same : other = shift
  · subst other
    simp only [Equiv.apply_symm_apply]
    simp [polynomialWeightRatio,lp.single_apply]
  · have distinct : twoFrequencyTranslation other ((twoFrequencyTranslation shift).symm input) ≠ input := by
      intro equal
      have first := congrArg Prod.fst equal
      have second := congrArg Prod.snd equal
      change input.1+shift.1-other.1 = input.1 at first
      change input.2+shift.2-other.2 = input.2 at second
      apply same
      apply Prod.ext <;> omega
    simp only [polynomialWeightRatio,pow_zero,div_one,Complex.ofReal_one,one_smul,
      lp.single_apply,Pi.single_apply,if_neg distinct,map_zero,if_neg same]

/-- Genuine operator derivatives are observed by a bounded linear map,
so their matrix derivatives retain exactly the original entries. -/
theorem fourierEntryObservation_hasDerivAt {source target : ℕ} (output input : ℤ × ℤ)
    (family : ℝ → (CellL2 source →L[ℂ] CellL2 target))
    (slope : CellL2 source →L[ℂ] CellL2 target) (radius : ℝ)
    (derivative : HasDerivAt family slope radius) :
    HasDerivAt (fun point => fourierEntryObservation output input (family point))
      (fourierEntryObservation output input slope) radius :=
  ((fourierEntryObservation output input).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius derivative

end Grad.OriginalCartesianTameEstimate
