import AJB8SameLowInverseOrbit
import AJB10ActualLowSmoothGenerator
import AJA15GenericInverseSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularInverseCalculus

private theorem complexLinear_contDiff_comp {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (mapping : E →L[ℂ] F) (function : P → E) (smooth : ContDiff ℝ ∞ function) :
    ContDiff ℝ ∞ (fun point => mapping (function point)) :=
  (mapping.restrictScalars ℝ).contDiff.comp smooth

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

/-- Smoothness of the actual differential equation plus genuine fixed trace,
in operator norm on the original complete graph and independent data space. -/
theorem actualLowDataOperatorOrbit_contDiff :
    ContDiff ℝ ∞ (actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state) := by
  have generatorSmooth : ContDiff ℝ ∞ (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state) :=
    contDiff_infty.mpr (actualLowGeneratorOrbit_contDiff parameters length compact lower lengthPositive positive bounded.le state)
  have composed := complexLinear_contDiff_comp (P := OrbitParameter)
    (E := LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower)
    (F := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower)
    (lowDataGeneratorAssembly lower length positive)
    (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state) generatorSmooth
  have formula : actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state =
      fun sigma => lowDataDiagonal lower length positive bounded -
        lowDataGeneratorAssembly lower length positive
          (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state sigma) := by
    funext sigma
    exact actualLowDataOperatorOrbit_assembly parameters length compact lower lengthPositive positive bounded state sigma
  rw [formula]
  exact ContDiff.sub (𝕜 := ℝ) (E := OrbitParameter)
    (F := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower) contDiff_const composed

/-- Every order of the SAME original inverse exists in complete operator norm;
only the accepted primitive B8 smallness is used. Fourier-generator membership
is a separate conclusion obtained by applying this orbit to genuine data. -/
theorem actualLowInverseOrbit_contDiff
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact) :
    ContDiff ℝ ∞ (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state) := by
  apply sameInverse_contDiff (𝕜 := ℂ) (P := OrbitParameter)
    (E := lowEnergyGraph lower length positive) (F := LowEnergyData lower)
    (actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state)
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
  · intro tau
    apply ContinuousLinearMap.ext
    intro data
    exact actualLowInverseOrbit_right parameters length compact lower lengthPositive positive bounded state small tau data
  · intro tau
    apply ContinuousLinearMap.ext
    intro field
    exact actualLowInverseOrbit_left parameters length compact lower lengthPositive positive bounded state small tau field
  · exact actualLowDataOperatorOrbit_contDiff parameters length compact lower lengthPositive positive bounded state

end Grad.AnnularLowOrbit
