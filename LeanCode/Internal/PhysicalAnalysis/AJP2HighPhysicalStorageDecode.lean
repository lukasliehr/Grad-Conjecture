import AJP1FullPhysicalRowLinearity
import AJI22ActualHighSectionStorage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.CircularHighRegularity Grad.AnnularHighRadial Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The high raw phase and sqrt(r) decoding equal the original common physical storage inverse. -/
theorem rawHighPhase_ordinaryWeight (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    rawHighPhase parameters lower positive mode.2 radius * reciprocalRadialWeight lower (fun _ => 1) radius =
      (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ := by
  have scalar := originalHighSection_storageFactor parameters lower positive radius inside mode
  change lowRhoPhysicalWeight parameters lower positive radius mode *
    Grad.AnnularHighTilt.highPowerCurve lower Grad.AnnularHighTilt.highTiltExponent positive radius *
    Grad.AnnularReconstruction.annularInversePhase parameters mode.2 radius = Real.sqrt radius at scalar
  change (Grad.AnnularHighTilt.highPowerCurve lower Grad.AnnularHighTilt.highTiltExponent positive radius *
    Grad.AnnularReconstruction.annularInversePhase parameters mode.2 radius) *
    (1 / Real.sqrt (max lower radius)) = _
  rw [max_eq_right inside.1]
  field_simp [(lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne',
    (Real.sqrt_pos.2 (positive.trans_le inside.1)).ne']
  nlinarith only [scalar]

theorem rawHighPhase_radialOrdinary_ae (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (field : DivisionRow 1 lower) (mode : ℤ × ℤ) :
    collarScalar 1 lower (rawHighPhase parameters lower positive mode.2)
      (radialOrdinary 1 lower positive (field mode)) =ᵐ[volume.restrict (Icc lower 1)]
      fun radius => lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  filter_upwards [collarScalar_ae 1 lower (rawHighPhase parameters lower positive mode.2)
      (radialOrdinary 1 lower positive (field mode)),
    radialOrdinary_ae 1 lower positive (field mode), ae_restrict_mem measurableSet_Icc]
    with radius phase ordinary inside
  rw [phase, ordinary, smul_smul, rawHighPhase_ordinaryWeight parameters lower positive radius inside mode]
  unfold lowRhoPhysicalCoefficient
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact congrArg (fun scalar : ℂ => scalar • field mode radius)
    (Complex.ofReal_inv (lowRhoPhysicalWeight parameters lower positive radius mode))

end Grad.AnnularSmoothCore
