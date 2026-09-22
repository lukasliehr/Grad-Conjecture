import AKDH14EulerObservationFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.AnnularKernelL2
open Grad.SourceCollarCoefficients

theorem fourierEntryObservation_ext {source target : ℕ}
    (first second : CellL2 source →L[ℂ] CellL2 target)
    (same : ∀ output input, fourierEntryObservation output input first = fourierEntryObservation output input second) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro field
  have onSingle (input : ℤ × ℤ) : first (lp.single 2 input (field input)) = second (lp.single 2 input (field input)) := by
    apply lp.ext
    funext output
    exact congrArg (fun mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target => mapping (field input)) (same output input)
  have series := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) field
  have one := first.hasSum series
  have two := second.hasSum series
  exact (one.congr_fun (fun input => (onSingle input).symm)).unique two

theorem fourierEntryObservation_conjugated {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (shift input : ℤ × ℤ) :
    fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (conjugatedKernelAction parameters grade reserve radius kernel) =
      ((bulkWeightRatio parameters grade radius.val shift ((twoFrequencyTranslation shift).symm input) : ℂ) *
        frequencyReserveSymbol reserve input) • kernel.entry shift input := by
  apply ContinuousLinearMap.ext
  intro value
  rw [fourierEntryObservation_apply]
  have observed := conjugatedKernelAction_coefficient parameters grade reserve radius kernel
    (lp.single 2 input value) ((twoFrequencyTranslation shift).symm input)
  apply observed.unique
  apply (hasSum_ite_eq shift (((bulkWeightRatio parameters grade radius.val shift ((twoFrequencyTranslation shift).symm input) : ℂ) *
    frequencyReserveSymbol reserve input) • kernel.entry shift input value)).congr_fun
  intro other
  by_cases same : other = shift
  · subst other
    simp only [Equiv.apply_symm_apply]
    simp [lp.single_apply]
  · have distinct : twoFrequencyTranslation other ((twoFrequencyTranslation shift).symm input) ≠ input := by
      intro equal
      have first := congrArg Prod.fst equal
      have second := congrArg Prod.snd equal
      change input.1+shift.1-other.1 = input.1 at first
      change input.2+shift.2-other.2 = input.2 at second
      apply same
      apply Prod.ext <;> omega
    simp only [lp.single_apply,Pi.single_apply,if_neg distinct,map_zero,smul_zero,if_neg same]

end Grad.OriginalCartesianTameEstimate
