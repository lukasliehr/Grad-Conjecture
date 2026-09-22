import AKC14WeightedJetReserveBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.PhaseAlgebra Grad.AnnularRadialSmoothness

theorem bulkWeightRatio_phasePolynomial (parameters : PhaseParameters) (grade : ℕ)
    (radius : ℝ) (shift input : ℤ × ℤ) :
    bulkWeightRatio parameters grade radius shift ((twoFrequencyTranslation shift).symm input) =
      radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius *
        polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input) := by
  unfold bulkWeightRatio radialPhaseRatio polynomialWeightRatio
  simp only [Equiv.apply_symm_apply]
  ring

def conjugatedCoefficientJet {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (coefficients : ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (rank : ℕ) (shift input : ℤ × ℤ) (radius : ℝ) :
    ComplexEuclidean source →L[ℂ] ComplexEuclidean target :=
  frequencyReserveSymbol reserve input •
    (polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input) •
      iteratedDeriv rank (fun point =>
        radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 point •
          coefficients point shift input) radius)

def conjugatedJetConstant (parameters : PhaseParameters) (constants : ℕ → ℝ) (rank : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (rank + 1), (rank.choose index : ℝ) * phaseRatioJetConstant parameters index * constants (rank - index)

theorem conjugatedCoefficientJet_bound {source target : ℕ} (parameters : PhaseParameters)
    (grade order : ℕ)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (same : ∀ rank radius shift input, (kernels rank radius).entry shift input = coefficients rank radius.val shift input)
    (derivative : ∀ rank shift input radius, HasDerivAt (fun point => coefficients rank point shift input)
      (coefficients (rank + 1) radius shift input) radius)
    (constants : ℕ → ℝ) (nonnegative : ∀ rank, 0 ≤ constants rank)
    (bounded : ∀ rank radius, fullKernelMoment (radialKernelParameters parameters radius)
      (grade + (order + 4)) (kernels rank radius) ≤ constants rank)
    (rank : ℕ) (valid : rank ≤ order) (shift input : ℤ × ℤ) (radius : RadialPoint) :
    ‖conjugatedCoefficientJet parameters grade (order + 4) (coefficients 0) rank shift input radius.val‖ ≤
      conjugatedJetConstant parameters constants rank *
        ((annularFrequency shift.1 shift.2 ^ 4)⁻¹ * (annularFrequency input.1 input.2 ^ 4)⁻¹) := by
  have smooth := derivativeTower_smooth (fun rank point => coefficients rank point shift input)
    (fun rank point => derivative rank shift input point) 0
  have phaseSmooth := radialPhaseRatio_smooth parameters ((twoFrequencyTranslation shift).symm input).2 input.2
  have productBound := norm_iteratedDeriv_real_smul_le rank radius.val phaseSmooth smooth
  have jet (index : ℕ) : iteratedDeriv index (fun point => coefficients 0 point shift input) =
      fun point => coefficients index point shift input := by
    simpa only [Nat.zero_add] using derivativeTower_iteratedDeriv
      (fun rank point => coefficients rank point shift input) (fun rank point => derivative rank shift input point) index 0
  simp only [jet] at productBound
  unfold conjugatedCoefficientJet
  rw [norm_smul, frequencyReserveSymbol_norm, norm_smul,
    Real.norm_of_nonneg (polynomialWeightRatio_nonnegative grade shift ((twoFrequencyTranslation shift).symm input))]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left productBound
    (polynomialWeightRatio_nonnegative grade shift ((twoFrequencyTranslation shift).symm input)))
    (inv_nonneg.mpr (pow_nonneg (annularFrequency_pos input).le _))).trans
  rw [Finset.mul_sum, Finset.mul_sum]
  unfold conjugatedJetConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have indexRank : index ≤ rank := by have validIndex := Finset.mem_range.mp member; omega
  have matrixBound := weightedKernelEntry_decay parameters grade (order + 4) radius (kernels (rank - index) radius)
    (constants (rank - index)) (bounded (rank - index) radius) shift ((twoFrequencyTranslation shift).symm input)
  rw [bulkWeightRatio_phasePolynomial] at matrixBound
  simp only [Equiv.apply_symm_apply, same] at matrixBound
  have estimate := phaseProductJet_reserve_bound
    (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val)
    (polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input))
    (annularFrequency shift.1 shift.2) (annularFrequency input.1 input.2)
    ‖iteratedDeriv index (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2) radius.val‖
    ‖coefficients (rank - index) radius.val shift input‖
    (phaseRatioJetConstant parameters index) (constants (rank - index)) index order (indexRank.trans valid)
    (polynomialWeightRatio_nonnegative grade shift ((twoFrequencyTranslation shift).symm input))
    (annularFrequency_one_le shift) (annularFrequency_one_le input) (norm_nonneg _)
    (phaseRatioJetConstant_nonnegative parameters index) (nonnegative _)
    (radialPhaseRatio_iterated_bound parameters index shift input radius.val) matrixBound
  convert mul_le_mul_of_nonneg_left estimate (Nat.cast_nonneg (rank.choose index) : (0 : ℝ) ≤ _) using 1 <;> ring

end Grad.AnnularWeightedSmoothness
