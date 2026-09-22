import AJI14HilbertFourierSector
import AJI6ActualFluxHilbertSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

def highHilbertIntoFull : lp (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 →ₗᵢ[ℂ] CellL2 1 :=
  hilbertSectorIntoFull (fun mode : ℤ × ℤ => 3 ≤ |mode.1|)

def lowHilbertIntoFull : lp (fun _ : LowAnnularMode => ComplexEuclidean 1) 2 →ₗᵢ[ℂ] CellL2 1 :=
  hilbertSectorIntoFull (fun mode : ℤ × ℤ => |mode.1| = 1 ∨ |mode.1| = 2)

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)

/-- The original high tilt is removed explicitly. The low summand is the
original exp(Phi)(a_m mu xi,x) inverse coordinate from ADY7. -/
def sameCoupledPhysicalXiSection (grade : ℕ) (field : CoupledSpace lower length positive lengthPositive)
    (radius : Icc lower (1 : ℝ)) : CellL2 1 :=
  highPowerCurve lower highTiltExponent positive radius.val •
    highHilbertIntoFull (actualHighHilbertSection parameters lower length positive bounded grade
      (bEnergyDecode lower length positive field.ofLp.1.ofLp.1) radius) +
    lowHilbertIntoFull (actualLowHilbertSection parameters lower length positive bounded 0 grade field.ofLp.2 radius)

/-- The second field is the original corrected flux x=Rp. -/
def sameCoupledPhysicalXSection (grade : ℕ) (field : CoupledSpace lower length positive lengthPositive)
    (radius : Icc lower (1 : ℝ)) : CellL2 1 :=
  highPowerCurve lower highTiltExponent positive radius.val •
    highHilbertIntoFull (actualFluxHilbertSection parameters lower positive bounded grade
      (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2) radius) +
    lowHilbertIntoFull (actualLowHilbertSection parameters lower length positive bounded 1 grade field.ofLp.2 radius)

omit parameters bounded in
theorem coupledBDecode_weighted (grade : ℕ) (field weighted : CoupledSpace lower length positive lengthPositive)
    (same : CoupledInsertedGrade lower length positive lengthPositive grade field weighted) (mode : HighAnnularMode) :
    (bEnergyDecode lower length positive weighted.ofLp.1.ofLp.1).val mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        (bEnergyDecode lower length positive field.ofLp.1.ofLp.1).val mode := by
  simp only [bEnergyDecode, annularEnergyDiagonal_apply]
  rw [same.1 mode]
  exact smul_comm _ _ _

variable (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include allGrades

theorem sameCoupledPhysicalXiSection_continuous (grade : ℕ) :
    Continuous (sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade field) := by
  obtain ⟨weightedHigh, sameHigh⟩ := allGrades (grade + 4)
  obtain ⟨weightedLow, sameLow⟩ := allGrades (grade + 5)
  have high := highHilbertIntoFull.continuous.comp
    (actualHighHilbertSection_continuous parameters lower length positive bounded grade
      (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)
      (bEnergyDecode lower length positive weightedHigh.ofLp.1.ofLp.1)
      (coupledBDecode_weighted lower length positive lengthPositive (grade + 4) field weightedHigh sameHigh))
  have low := lowHilbertIntoFull.continuous.comp
    (actualLowHilbertSection_continuous parameters lower length positive bounded lengthPositive 0 grade
      field.ofLp.2 weightedLow.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weightedLow sameLow))
  exact (((highPowerCurve lower highTiltExponent positive).continuous.comp continuous_subtype_val).smul high).add low

theorem sameCoupledPhysicalXSection_continuous (grade : ℕ) :
    Continuous (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade field) := by
  obtain ⟨weighted, same⟩ := allGrades (grade + 5)
  have high := highHilbertIntoFull.continuous.comp
    (actualFluxHilbertSection_continuous parameters lower positive bounded grade
      (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2)
      (annularOmegaIntoNu lower length positive lengthPositive weighted.ofLp.1.ofLp.2)
      (coupledInsertedGrade_flux_value lower length positive lengthPositive (grade + 5) field weighted same)
      (coupledInsertedGrade_flux_derivative lower length positive lengthPositive (grade + 5) field weighted same))
  have low := lowHilbertIntoFull.continuous.comp
    (actualLowHilbertSection_continuous parameters lower length positive bounded lengthPositive 1 grade
      field.ofLp.2 weighted.ofLp.2 (coupledInsertedGrade_low lower length positive lengthPositive (grade + 5) field weighted same))
  exact (((highPowerCurve lower highTiltExponent positive).continuous.comp continuous_subtype_val).smul high).add low

end Grad.AnnularSmoothCore
