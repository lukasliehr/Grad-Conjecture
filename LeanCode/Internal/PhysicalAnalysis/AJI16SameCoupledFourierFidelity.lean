import AJI15SameCoupledContinuousFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem hilbertSectors_coefficient (high : lp (fun _ : HighAnnularMode => ComplexEuclidean 1) 2)
    (low : lp (fun _ : LowAnnularMode => ComplexEuclidean 1) 2) (scalar : ℝ) (mode : ℤ × ℤ) :
    (scalar • highHilbertIntoFull high + lowHilbertIntoFull low) mode =
      if large : 3 ≤ |mode.1| then scalar • high ⟨mode, large⟩
      else if small : |mode.1| = 1 ∨ |mode.1| = 2 then low ⟨mode, small⟩ else 0 := by
  have highValue : highHilbertIntoFull high mode =
      if large : 3 ≤ |mode.1| then high ⟨mode, large⟩ else 0 := rfl
  have lowValue : lowHilbertIntoFull low mode =
      if small : |mode.1| = 1 ∨ |mode.1| = 2 then low ⟨mode, small⟩ else 0 := rfl
  change scalar • highHilbertIntoFull high mode + lowHilbertIntoFull low mode = _
  rw [highValue, lowValue]
  by_cases large : 3 ≤ |mode.1|
  · have notSmall : ¬ (|mode.1| = 1 ∨ |mode.1| = 2) := by omega
    simp only [dif_pos large, dif_neg notSmall, add_zero]
  · simp only [dif_neg large, smul_zero, zero_add]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

def sameCoupledXiCoefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  if large : 3 ≤ |mode.1| then highPowerCurve lower highTiltExponent positive radius.val •
    (((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      annularPhysicalValueSection parameters lower length positive bounded ⟨mode, large⟩
        (bEnergyDecode lower length positive field.ofLp.1.ofLp.1) radius)
  else if small : |mode.1| = 1 ∨ |mode.1| = 2 then
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      lowPhysicalSection parameters lower length positive bounded field.ofLp.2 (0, ⟨mode, small⟩) radius
  else 0

def sameCoupledXCoefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  if large : 3 ≤ |mode.1| then highPowerCurve lower highTiltExponent positive radius.val •
    (((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      actualFluxPhysicalSection lower positive bounded parameters
        (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2) ⟨mode, large⟩ radius)
  else if small : |mode.1| = 1 ∨ |mode.1| = 2 then
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      lowPhysicalSection parameters lower length positive bounded field.ofLp.2 (1, ⟨mode, small⟩) radius
  else 0

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include allGrades

theorem sameCoupledPhysicalXiSection_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade field radius mode =
      sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius mode := by
  obtain ⟨weightedHigh, sameHigh⟩ := allGrades (grade + 4)
  obtain ⟨weightedLow, sameLow⟩ := allGrades (grade + 5)
  have high := actualHighHilbertSection_coefficient parameters lower length positive bounded grade
    (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)
    (bEnergyDecode lower length positive weightedHigh.ofLp.1.ofLp.1)
    (coupledBDecode_weighted lower length positive lengthPositive (grade + 4) field weightedHigh sameHigh) radius
  have low := actualLowHilbertSection_coefficient parameters lower length positive bounded lengthPositive 0 grade
    field.ofLp.2 weightedLow.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weightedLow sameLow) radius
  unfold sameCoupledPhysicalXiSection
  rw [hilbertSectors_coefficient]
  simp only [high, low]
  rfl

theorem sameCoupledPhysicalXSection_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade field radius mode =
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius mode := by
  obtain ⟨weighted, same⟩ := allGrades (grade + 5)
  have high := actualFluxHilbertSection_coefficient parameters lower positive bounded grade
    (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2)
    (annularOmegaIntoNu lower length positive lengthPositive weighted.ofLp.1.ofLp.2)
    (coupledInsertedGrade_flux_value lower length positive lengthPositive (grade + 5) field weighted same)
    (coupledInsertedGrade_flux_derivative lower length positive lengthPositive (grade + 5) field weighted same) radius
  have low := actualLowHilbertSection_coefficient parameters lower length positive bounded lengthPositive 1 grade
    field.ofLp.2 weighted.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weighted same) radius
  unfold sameCoupledPhysicalXSection
  rw [hilbertSectors_coefficient]
  simp only [high, low]
  rfl

end Grad.AnnularSmoothCore
