import AJP3HighFluxStorageAlgebra
import AJI30ActualFullRadialRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularHighRadial Grad.AnnularCurrentLow Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.AnnularCoupledInverse Grad.AnnularCurrentEnergy Grad.AnnularVariational Grad.AnnularOmegaGraph
open Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.AnnularHighTilt
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

theorem sameCoupledXiCoefficient_high (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode.val =
      rawHighXiSection parameters lower length positive bounded field.ofLp.1.ofLp.1 mode radius := by
  rw [rawHighXiSection_same]
  simp only [sameCoupledXiCoefficient, dif_pos mode.property, pow_zero, Complex.ofReal_one, one_smul]

theorem sameCoupledXCoefficient_high (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode.val =
      rawHighXSection parameters lower length positive bounded lengthPositive field.ofLp.1.ofLp.2 mode radius := by
  rw [rawHighXSection_same]
  simp only [sameCoupledXCoefficient, dif_pos mode.property, pow_zero, Complex.ofReal_one, one_smul]

/-- The physical x entering the original RHS is the same genuine high flux representative. -/
theorem sameCoupledXCoefficient_high_stored (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowRhoPhysicalCoefficient parameters lower positive
        (highBulkIntoFull lower (field.ofLp.1.ofLp.2.val 0)) radius mode.val =
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
        (radialClamp lower bounded.le radius) mode.val := by
  filter_upwards [actualHighXSection_stored parameters lower positive bounded
      (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2) mode,
    ae_restrict_mem measurableSet_Icc] with radius stored inside
  unfold lowRhoPhysicalCoefficient
  rw [highBulkIntoFull_high]
  change (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ)⁻¹ •
    (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.1.ofLp.2).val.1 mode radius = _
  rw [← stored, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr
    (lowRhoPhysicalWeight_pos parameters lower positive radius mode.val).ne')]
  simp only [sameCoupledXCoefficient, dif_pos mode.property, pow_zero, Complex.ofReal_one, one_smul]
  rw [radialClamp_eq lower bounded.le radius inside]

end Grad.AnnularSmoothCore
