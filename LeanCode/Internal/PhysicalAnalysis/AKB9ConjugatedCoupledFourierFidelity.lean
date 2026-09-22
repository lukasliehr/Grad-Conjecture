import AKB8ConjugatedCoupledContinuousFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

def conjugatedCoupledXiCoefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  if large : 3 ≤ |mode.1| then highPowerCurve lower highTiltExponent positive radius.val •
    (((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      conjugatedHighSection lower length positive bounded
        (bEnergyDecode lower length positive field.ofLp.1.ofLp.1) ⟨mode, large⟩ radius)
  else if small : |mode.1| = 1 ∨ |mode.1| = 2 then
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      conjugatedLowSection parameters lower length positive bounded field.ofLp.2 (0, ⟨mode, small⟩) radius
  else 0

def conjugatedCoupledXCoefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  if large : 3 ≤ |mode.1| then highPowerCurve lower highTiltExponent positive radius.val •
    (((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      annularFluxSection lower positive bounded
        (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2) ⟨mode, large⟩ radius)
  else if small : |mode.1| = 1 ∨ |mode.1| = 2 then
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      conjugatedLowSection parameters lower length positive bounded field.ofLp.2 (1, ⟨mode, small⟩) radius
  else 0

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include allGrades

theorem conjugatedCoupledXiSection_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    conjugatedCoupledXiSection parameters lower length positive bounded lengthPositive grade field radius mode =
      conjugatedCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius mode := by
  obtain ⟨weightedHigh, sameHigh⟩ := allGrades (grade + 4)
  obtain ⟨weightedLow, sameLow⟩ := allGrades (grade + 5)
  have high := conjugatedHighHilbertSection_coefficient lower length positive bounded grade
    (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)
    (bEnergyDecode lower length positive weightedHigh.ofLp.1.ofLp.1)
    (coupledBDecode_weighted lower length positive lengthPositive (grade + 4) field weightedHigh sameHigh) radius
  have low := conjugatedLowHilbertSection_coefficient parameters lower length positive bounded lengthPositive 0 grade
    field.ofLp.2 weightedLow.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weightedLow sameLow) radius
  unfold conjugatedCoupledXiSection
  rw [hilbertSectors_coefficient]
  simp only [high, low]
  rfl

theorem conjugatedCoupledXSection_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    conjugatedCoupledXSection parameters lower length positive bounded lengthPositive grade field radius mode =
      conjugatedCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius mode := by
  obtain ⟨weighted, same⟩ := allGrades (grade + 5)
  have high := conjugatedFluxHilbertSection_coefficient lower positive bounded grade
    (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2)
    (annularOmegaIntoNu lower length positive lengthPositive weighted.ofLp.1.ofLp.2)
    (coupledInsertedGrade_flux_value lower length positive lengthPositive (grade + 5) field weighted same)
    (coupledInsertedGrade_flux_derivative lower length positive lengthPositive (grade + 5) field weighted same) radius
  have low := conjugatedLowHilbertSection_coefficient parameters lower length positive bounded lengthPositive 1 grade
    field.ofLp.2 weighted.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weighted same) radius
  unfold conjugatedCoupledXSection
  rw [hilbertSectors_coefficient]
  simp only [high, low]
  rfl

end Grad.AnnularWeightedSmoothCore
