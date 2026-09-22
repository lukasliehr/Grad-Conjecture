import AKBR1SameFullOuterSevenBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularSmoothCore Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularUniformBoundary
open Grad.AnnularTiltedReference Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length)
    (candidate : CoupledSpace lower length positive lengthPositive)

/-- Genuine high x outer trace equals the SAME physical section at r=1. -/
theorem originalHighOuterX_physical (mode : HighAnnularMode) :
    negativeTraceCoefficient parameters 0 0
      (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).val mode.val=
      actualFluxPhysicalSection lower positive (lowerHalf.trans_lt (by norm_num)) parameters
        (annularOmegaIntoNu lower length positive lengthPositive candidate.ofLp.1.ofLp.2) mode
        ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩ := by
  rw [negativeTraceCoefficient,coupledHighFluxOuter_coefficient,annularFluxTrace_apply,negativeTraceWeight_base,
    ← Complex.ofReal_inv]
  change ((Real.exp (radialPhase parameters 1 mode.val.2)/Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹:ℝ) •
    ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
      annularFluxSection lower positive (lowerHalf.trans_lt (by norm_num))
        (annularOmegaIntoNu lower length positive lengthPositive candidate.ofLp.1.ofLp.2) mode
        ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩)=_
  rw [smul_smul]
  change _=Real.exp (-radialPhase parameters 1 mode.val.2) •
    annularFluxSection lower positive (lowerHalf.trans_lt (by norm_num))
      (annularOmegaIntoNu lower length positive lengthPositive candidate.ofLp.1.ofLp.2) mode
      ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩
  congr 1
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos _).ne',(Real.sqrt_pos.mpr (Grad.AnnularFluxTrace.annularFrequency_pos mode)).ne']

/-- Genuine high Xi outer trace equals the SAME physical section at r=1. -/
theorem originalHighOuterXi_physical (mode : HighAnnularMode) :
    positiveTraceCoefficient parameters 0 0
      (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1) mode.val=
      annularPhysicalValueSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) mode
        (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1)
        ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩ := by
  rw [positiveTraceCoefficient,actualCurrentHighOuterTrace_high,
    uniformOuterTrace_eq_annularEnergyTrace lower length positive lowerHalf (lowerHalf.trans_lt (by norm_num)) lengthPositive,
    annularEnergyTrace_eq_radial,positiveTraceWeight_base,← Complex.ofReal_inv]
  change ((Real.exp (radialPhase parameters 1 mode.val.2)*Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹:ℝ) •
    ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2):ℂ) •
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1)))=_
  rw [Complex.coe_smul,smul_smul]
  change _=Real.exp (-radialPhase parameters 1 mode.val.2) •
    weightedRadialSection 1 lower positive (lowerHalf.trans_lt (by norm_num))
      (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1))
      ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩
  have endpoint := weightedRadialSection_endpoint 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
    (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1))
  change weightedRadialSection 1 lower positive (lowerHalf.trans_lt (by norm_num))
    (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1))
    ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩=_ at endpoint
  rw [endpoint]
  congr 1
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos _).ne',(Real.sqrt_pos.mpr (Grad.AnnularFluxTrace.annularFrequency_pos mode)).ne']

end Grad.OriginalKernelOuterUniqueness
