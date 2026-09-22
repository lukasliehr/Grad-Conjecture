import AKC15ConjugatedMatrixJetBounds
import AKC10ExactReservedMatrixSeries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open Set
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.PhaseAlgebra Grad.AnnularRadialSmoothness

theorem conjugatedCoefficientJet_zero {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (coefficients : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (shift input : ℤ × ℤ) (radius : ℝ) :
    conjugatedCoefficientJet parameters grade reserve coefficients 0 shift input radius =
      ((bulkWeightRatio parameters grade radius shift ((twoFrequencyTranslation shift).symm input) : ℂ) *
        frequencyReserveSymbol reserve input) • coefficients radius shift input := by
  unfold conjugatedCoefficientJet
  rw [iteratedDeriv_zero]
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro component
  change frequencyReserveSymbol reserve input *
    (polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input) •
      (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius •
        (coefficients radius shift input vector component))) =
    ((bulkWeightRatio parameters grade radius shift ((twoFrequencyTranslation shift).symm input) : ℂ) *
      frequencyReserveSymbol reserve input) * coefficients radius shift input vector component
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  have cast (real : ℝ) : (RCLike.ofReal real : ℂ) = (real : ℂ) := rfl
  simp only [cast]
  rw [bulkWeightRatio_phasePolynomial, Complex.ofReal_mul]
  ring

def conjugatedMatrixJetTerm {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (coefficients : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (rank : ℕ) (index : (ℤ × ℤ) × (ℤ × ℤ)) (radius : ℝ) : CellL2 source →L[ℂ] CellL2 target :=
  fourierMatrixPoint ((twoFrequencyTranslation index.1).symm index.2) index.2
    (conjugatedCoefficientJet parameters grade reserve coefficients rank index.1 index.2 radius)

theorem conjugatedMatrixJetTerm_hasDerivAt {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (coefficients : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (smooth : ∀ shift input, ContDiff ℝ ∞ (fun radius => coefficients radius shift input))
    (rank : ℕ) (index : (ℤ × ℤ) × (ℤ × ℤ)) (radius : ℝ) :
    HasDerivAt (conjugatedMatrixJetTerm parameters grade reserve coefficients rank index)
      (conjugatedMatrixJetTerm parameters grade reserve coefficients (rank + 1) index radius) radius := by
  have productSmooth := (radialPhaseRatio_smooth parameters ((twoFrequencyTranslation index.1).symm index.2).2 index.2.2).smul
    (smooth index.1 index.2)
  exact ((fourierMatrixPoint ((twoFrequencyTranslation index.1).symm index.2) index.2).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (((smoothCurve_iteratedDeriv_hasDerivAt _ productSmooth rank radius).const_smul
      (polynomialWeightRatio grade index.1 ((twoFrequencyTranslation index.1).symm index.2))).const_smul
        (frequencyReserveSymbol reserve index.2))

theorem conjugatedMatrixJetTerm_continuous {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (coefficients : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (smooth : ∀ shift input, ContDiff ℝ ∞ (fun radius => coefficients radius shift input))
    (rank : ℕ) (index : (ℤ × ℤ) × (ℤ × ℤ)) :
    Continuous (conjugatedMatrixJetTerm parameters grade reserve coefficients rank index) :=
  continuous_iff_continuousAt.mpr (fun radius =>
    (conjugatedMatrixJetTerm_hasDerivAt parameters grade reserve coefficients smooth rank index radius).continuousAt)

end Grad.AnnularWeightedSmoothness
