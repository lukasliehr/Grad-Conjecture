import AKB7ConjugatedLowHilbert

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)

/-- The SAME original high tilt is removed, retaining the original analytic phase.
The low summand removes only the original amplitude and mu balancing. -/
def conjugatedCoupledXiSection (grade : ℕ) (field : CoupledSpace lower length positive lengthPositive)
    (radius : Icc lower (1 : ℝ)) : CellL2 1 :=
  highPowerCurve lower highTiltExponent positive radius.val •
    highHilbertIntoFull (conjugatedHighHilbertSection lower length positive bounded grade
      (bEnergyDecode lower length positive field.ofLp.1.ofLp.1) radius) +
    lowHilbertIntoFull (conjugatedLowHilbertSection parameters lower length positive bounded 0 grade field.ofLp.2 radius)

/-- The second field is the original corrected flux x=Rp. -/
def conjugatedCoupledXSection (grade : ℕ) (field : CoupledSpace lower length positive lengthPositive)
    (radius : Icc lower (1 : ℝ)) : CellL2 1 :=
  highPowerCurve lower highTiltExponent positive radius.val •
    highHilbertIntoFull (conjugatedFluxHilbertSection lower positive bounded grade
      (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2) radius) +
    lowHilbertIntoFull (conjugatedLowHilbertSection parameters lower length positive bounded 1 grade field.ofLp.2 radius)

variable (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include allGrades

theorem conjugatedCoupledXiSection_continuous (grade : ℕ) :
    Continuous (conjugatedCoupledXiSection parameters lower length positive bounded lengthPositive grade field) := by
  obtain ⟨weightedHigh, sameHigh⟩ := allGrades (grade + 4)
  obtain ⟨weightedLow, sameLow⟩ := allGrades (grade + 5)
  have high := highHilbertIntoFull.continuous.comp
    (conjugatedHighHilbertSection_continuous lower length positive bounded grade
      (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)
      (bEnergyDecode lower length positive weightedHigh.ofLp.1.ofLp.1)
      (coupledBDecode_weighted lower length positive lengthPositive (grade + 4) field weightedHigh sameHigh))
  have low := lowHilbertIntoFull.continuous.comp
    (conjugatedLowHilbertSection_continuous parameters lower length positive bounded lengthPositive 0 grade
      field.ofLp.2 weightedLow.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weightedLow sameLow))
  exact (((highPowerCurve lower highTiltExponent positive).continuous.comp continuous_subtype_val).smul high).add low

theorem conjugatedCoupledXSection_continuous (grade : ℕ) :
    Continuous (conjugatedCoupledXSection parameters lower length positive bounded lengthPositive grade field) := by
  obtain ⟨weighted, same⟩ := allGrades (grade + 5)
  have high := highHilbertIntoFull.continuous.comp
    (conjugatedFluxHilbertSection_continuous lower positive bounded grade
      (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2)
      (annularOmegaIntoNu lower length positive lengthPositive weighted.ofLp.1.ofLp.2)
      (coupledInsertedGrade_flux_value lower length positive lengthPositive (grade + 5) field weighted same)
      (coupledInsertedGrade_flux_derivative lower length positive lengthPositive (grade + 5) field weighted same))
  have low := lowHilbertIntoFull.continuous.comp
    (conjugatedLowHilbertSection_continuous parameters lower length positive bounded lengthPositive 1 grade
      field.ofLp.2 weighted.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weighted same))
  exact (((highPowerCurve lower highTiltExponent positive).continuous.comp continuous_subtype_val).smul high).add low

end Grad.AnnularWeightedSmoothCore
