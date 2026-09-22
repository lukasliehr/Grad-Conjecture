import AJD38ActualBoundaryCrossCoordinateBounds
import AJD39ActualBulkCrossCoordinateBounds
import AJD41UniformFiniteOperatorAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularCrossMaps

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule crossHighRealNormed crossHighRealModule
  lowToHighOperatorRealNormed highToLowOperatorRealNormed

local instance lowToHighOperatorNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (lowEnergyGraph lower L positive →L[ℂ] CrossHighData parameters lower) := inferInstance

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem lowToHighCrossOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        lowToHighCrossOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state) := by
  have bulk := UniformCoordinateBound.threeComplex
    (fun (row : Fin 3) (context : CoupledCoordinateContext parameters L compact) =>
      lowToHighBulkOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state row)
    (fun row => lowToHighBulkOrbit_uniformCoordinateBound parameters L compact row)
    (fun row context => lowToHighBulkOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state row)
    (fun context => context.budget_nonnegative)
  have combined := bulk.pairComplex (lowToHighBoundaryOrbit_uniformCoordinateBound parameters L compact)
    (fun context => piLpOperator_contDiff _ (fun row => lowToHighBulkOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state row))
    (fun context => lowToHighBoundaryOrbit_contDiff parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state)
  with_unfolding_all exact combined

theorem highToLowCrossOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        highToLowCrossOrbit parameters L compact context.lower context.lengthPositive context.positive context.lowerHalf context.state) := by
  have incoming := UniformCoordinateBound.const (budget := CoupledCoordinateContext.budget)
    (fun context : CoupledCoordinateContext parameters L compact => context.budget_nonnegative)
    (fun context => (0 : CrossHighSpace context.lower L context.positive context.lengthPositive →L[ℂ] LowEnergyBoundary))
    0 le_rfl (fun _ => by simp only [norm_zero, le_refl])
  have combined := (highToLowBulkOrbit_uniformCoordinateBound parameters L compact).pairComplex incoming
    (fun context => highToLowBulkOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state)
    (fun _ => contDiff_const)
  with_unfolding_all exact combined
end Grad.AnnularCrossOrbit
