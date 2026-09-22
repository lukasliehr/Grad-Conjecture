import AKAK6ActualXiRadialEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness

private theorem cancelThirdRadius (radius : ℝ) (frequency phase : ℂ)
    (value coefficient : ComplexEuclidean 1) (nonzero : radius ≠ 0)
    (same : value = frequency • (phase • (radius • coefficient))) :
    (radius : ℂ)⁻¹ • value = frequency • (phase • coefficient) := by
  rw [same]
  change (radius : ℂ)⁻¹ • (frequency • (phase • ((radius : ℂ) • coefficient))) = _
  rw [smul_comm ((radius : ℂ)⁻¹) frequency,smul_comm ((radius : ℂ)⁻¹) phase,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr nonzero)]

/-- Undo the known factor r in the actual third-source curve on the
original positive collar. The same prescribed g and analytic phase remain. -/
def actualThirdSourceCurves (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data) :
    SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2 where
  curve grade radius := (radius : ℂ)⁻¹ • curves.third grade radius
  smooth grade := (reciprocalRadius_smooth lower positive).smul (curves.thirdSmooth grade)
  same grade := by
    filter_upwards [curves.thirdSame grade,ae_restrict_mem measurableSet_Icc] with radius actual inside
    intro mode
    change (radius : ℂ)⁻¹ • curves.third grade radius mode = _
    exact cancelThirdRadius radius ((annularFrequency mode.1 mode.2 : ℂ)^grade)
      (Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) : ℂ)
      (curves.third grade radius mode)
      (lowRhoPhysicalCoefficient parameters lower positive
        (strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2 radius mode)
      (positive.trans_le inside.1).ne' (actual mode)

end Grad.ActualPolarEquations
