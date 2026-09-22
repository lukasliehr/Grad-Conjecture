import AJF9SameCoupledInsertedGraphGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularFluxTrace Grad.AnnularCoupledInverse
open Grad.SourceCollarDivision Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit

/-- The actual omega/nu radial normalization commutes with an arbitrary
complex Fourier coefficient, independently in every original mode. -/
theorem annularOmegaToNu_weighted (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field weighted : AnnularBulk lower) (coefficient : HighAnnularMode → ℂ)
    (actual : ∀ mode, weighted mode = coefficient mode • field mode) (mode : HighAnnularMode) :
    annularOmegaToNu lower length positive lengthPositive weighted mode =
      coefficient mode • annularOmegaToNu lower length positive lengthPositive field mode := by
  change scalarRadialMap lower (annularOmegaOverNuCurve lower length positive mode)
    ((1 + length⁻¹) / lower) (annularOmegaOverNu_bound lower length positive lengthPositive mode) (weighted mode) =
      coefficient mode • scalarRadialMap lower (annularOmegaOverNuCurve lower length positive mode)
        ((1 + length⁻¹) / lower) (annularOmegaOverNu_bound lower length positive lengthPositive mode) (field mode)
  rw [actual, map_smul]

variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
  (grade : ℕ) (field weighted : CoupledSpace lower length positive lengthPositive)
  (actual : CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include actual

/-- Literal weighted energy coordinates consumed by the original radial
section reconstruction. No alternative high field is introduced. -/
theorem coupledInsertedGrade_energy (mode : HighAnnularMode) :
    weighted.ofLp.1.ofLp.1.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) • field.ofLp.1.ofLp.1.val mode :=
  actual.1 mode

/-- The value of the SAME original decoded weak flux graph. -/
theorem coupledInsertedGrade_flux_value (mode : HighAnnularMode) :
    (annularOmegaIntoNu lower length positive lengthPositive weighted.ofLp.1.ofLp.2).val.1 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2).val.1 mode :=
  actual.2.1 0 mode

/-- The derivative of that SAME original decoded weak flux graph; the
fixed omega/nu normalization commutes with the literal BF insertion. -/
theorem coupledInsertedGrade_flux_derivative (mode : HighAnnularMode) :
    (annularOmegaIntoNu lower length positive lengthPositive weighted.ofLp.1.ofLp.2).val.2 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2).val.2 mode :=
  annularOmegaToNu_weighted lower length positive lengthPositive
    (field.ofLp.1.ofLp.2.val 1) (weighted.ofLp.1.ofLp.2.val 1)
    (fun index => ((Grad.AnnularVariational.annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ)) (actual.2.1 1) mode

/-- Both rho-normalized low graph coordinates retain the same literal ν. -/
theorem coupledInsertedGrade_low (coordinate : Fin 2) (index : LowAnnularIndex) :
    weighted.ofLp.2.val coordinate index =
      ((Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 ^ grade : ℝ) : ℂ) • field.ofLp.2.val coordinate index :=
  actual.2.2 coordinate index

end Grad.AnnularHighGenerators
