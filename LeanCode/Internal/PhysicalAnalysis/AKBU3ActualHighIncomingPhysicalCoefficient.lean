import AKBU2SameOriginalPhysicalGraphRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularRestriction Grad.AnnularSourceGraph
open Grad.AnnularLowEnergy Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.GaugeCoefficients.Physical.WeightedTrace Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower) (bounded : lower<1)
    (lengthPositive : 0<length) (field : CoupledSpace lower length positive lengthPositive)

/-- Exact original high incoming datum of the SAME field. The r^-9/4,
full phase, b decoder and positive-half frequency are all retained. -/
theorem originalHighIncoming_physical (mode : HighAnnularMode) :
    annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1) mode=
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)*lower^(-(9/4:ℝ))*
        Real.exp (radialPhase parameters lower mode.val.2)) •
      sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨lower,le_rfl,bounded.le⟩ mode.val := by
  rw [annularEnergyTrace_eq_radial,sameCoupledXiCoefficient,dif_pos mode.property]
  simp only [pow_zero,Complex.ofReal_one,one_smul]
  rw [highPowerCurve_physical lower highTiltExponent positive lower ⟨le_rfl,bounded.le⟩]
  have endpoint := weightedRadialSection_endpoint 1 lower positive bounded 0
    (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field.ofLp.1.ofLp.1))
  change weightedRadialSection 1 lower positive bounded
    (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field.ofLp.1.ofLp.1))
    ⟨lower,le_rfl,bounded.le⟩=_ at endpoint
  change (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • _=
    (_ : ℝ) • (lower^(9/4:ℝ) • (Real.exp (-radialPhase parameters lower mode.val.2) •
      weightedRadialSection 1 lower positive bounded
        (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field.ofLp.1.ofLp.1))
        ⟨lower,le_rfl,bounded.le⟩))
  rw [endpoint,Complex.coe_smul,smul_smul,smul_smul]
  congr 1
  rw [Real.exp_neg,Real.rpow_neg positive.le]
  field_simp [(Real.exp_pos _).ne',(Real.rpow_pos_of_pos positive (9/4:ℝ)).ne']

end Grad.OriginalPhysicalKernelUniqueness
