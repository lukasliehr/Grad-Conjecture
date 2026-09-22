import GC14ReferenceJet

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

def referenceCurvatureMapping : ComplexEuclidean 3 →L[ℂ] OperatorValue 3 3 :=
  (columnEmbedding 3 3 2).comp physicalRotation

def referenceCurvatureCoefficient (parameters : PhaseParameters) (L ell : ℝ) (grade : ℕ) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
  familyCell L parameters.sigma0 parameters.gamma ell grade
    (fun _ => scaledOriginalJet ell referenceCurvatureMapping referenceStateJet) 0

def referenceCurvatureConstant (parameters : PhaseParameters) (grade : ℕ) : ℝ :=
  ‖referenceCurvatureMapping‖ * ∑ index : DerivativeIndex grade,
    ‖phaseOutsideClosedDerivative parameters 0 referenceStateJet (derivativeOrder index) (derivativeWord index)‖

theorem referenceCurvatureConstant_nonnegative (parameters : PhaseParameters) (grade : ℕ) :
    0 ≤ referenceCurvatureConstant parameters grade :=
  mul_nonneg (norm_nonneg referenceCurvatureMapping) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem referenceCurvatureCoefficient_norm_bound {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (grade : ℕ) :
    ‖referenceCurvatureCoefficient parameters L ell grade‖ ≤ referenceCurvatureConstant parameters grade := by
  refine (familyCell_norm_le L parameters.sigma0 parameters.gamma ell grade
    (fun _ => scaledOriginalJet ell referenceCurvatureMapping referenceStateJet) 0).trans ?_
  unfold referenceCurvatureConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _membership
  have bound := scaledOriginalJet_weightedDerivative_bound parameters admissible
    referenceCurvatureMapping referenceStateJet 0 index
  have frequencyZero : cellFrequency 0 = 1 := by norm_num [cellFrequency_formula]
  simpa only [frequencyZero, one_pow, one_mul] using bound

theorem referenceCurvatureCoefficient_derivative {L ell : ℝ} {grade : ℕ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (referenceCurvatureCoefficient parameters L ell grade) cell index point =
      (ell ^ derivativeOrder index : ℂ) • referenceCurvatureMapping
        (referenceStateMultiDerivative cell (derivativeMultiIndex index)
          (physicalScaledPoint ell admissible.2.2.2.1.le
            (admissible.2.2.2.2.trans (min_le_left _ _)) point)) := by
  change ((coefficientScale L parameters.sigma0 parameters.gamma ell grade cell index point : ℂ)⁻¹) •
    weightedSingle L parameters.sigma0 parameters.gamma ell grade 0
      (scaledOriginalJet ell referenceCurvatureMapping referenceStateJet) (cell, index) point = _
  rw [weightedSingle_apply]
  by_cases zeroCell : cell = 0
  · subst cell
    rw [if_pos rfl]
    change ((coefficientScale L parameters.sigma0 parameters.gamma ell grade 0 index point : ℂ)⁻¹) •
      ((coefficientScale L parameters.sigma0 parameters.gamma ell grade 0 index point : ℂ) •
        smoothOperatorDerivative (scaledOriginalJet ell referenceCurvatureMapping referenceStateJet)
          (derivativeMultiIndex index) point) = _
    rw [← mul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L parameters.sigma0 parameters.gamma ell grade 0 index point).ne'), one_smul]
    rw [scaledOriginalJet_derivative admissible.2.2.2.1.le
      (admissible.2.2.2.2.trans (min_le_left _ _)),
      radialPoint_eq_physicalScaledPoint ell admissible.2.2.2.1.le
        (admissible.2.2.2.2.trans (min_le_left _ _)), referenceStateJet_cartesianDerivative]
    rfl
  · rw [if_neg zeroCell]
    simp [referenceStateMultiDerivative, zeroCell]
    apply ContinuousLinearMap.ext
    intro vector
    apply PiLp.ext
    intro coordinate
    change (coefficientScale L parameters.sigma0 parameters.gamma ell grade cell index point : ℂ)⁻¹ * 0 =
      (ell ^ derivativeOrder index : ℂ) * 0
    ring

theorem coefficientDerivative_add_apply {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (first second : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (first + second) cell index point =
      coefficientDerivative first cell index point + coefficientDerivative second cell index point := by
  exact smul_add _ _ _

theorem coefficientDerivative_smul_apply {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ} (scalar : ℂ)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (scalar • coefficient) cell index point =
      scalar • coefficientDerivative coefficient cell index point := by
  exact smul_comm _ scalar _

end Grad.GaugeCoefficients.Physical.Frame
