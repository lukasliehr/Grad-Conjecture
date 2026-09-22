import AKAF8SameOriginalForceCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.AnnularGeneralSourceRegularity
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem physicalCurve_add {other : DivisionRow dimension lower}
    (target : SmoothLowPhysicalRow parameters lower positive other) (grade : ℕ) (radius : ℝ) :
    (curves.add target).physicalCurve grade radius = curves.physicalCurve grade radius + target.physicalCurve grade radius := by
  exact map_add (inversePhaseDiagonal parameters dimension 4 radius) _ _

theorem physicalCurve_sub {other : DivisionRow dimension lower}
    (target : SmoothLowPhysicalRow parameters lower positive other) (grade : ℕ) (radius : ℝ) :
    (curves.sub target).physicalCurve grade radius = curves.physicalCurve grade radius - target.physicalCurve grade radius := by
  exact map_sub (inversePhaseDiagonal parameters dimension 4 radius) _ _

theorem physicalCurve_smul (scalar : ℂ) (grade : ℕ) (radius : ℝ) :
    (curves.smul scalar).physicalCurve grade radius = scalar • curves.physicalCurve grade radius := by
  exact map_smul (inversePhaseDiagonal parameters dimension 4 radius) scalar _

theorem physicalCurve_bulkUnit {target : ℕ} (output : Fin target) (input : Fin dimension)
    (bounded : lower < 1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (curves.bulkUnit output input).physicalCurve 0 radius mode = matrixUnit output input (curves.physicalCurve 0 radius mode) := by
  rw [(curves.bulkUnit output input).physicalCurve_coefficient bounded 0 radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode,map_smul]
  rfl

def physicalForceCurves (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : AnnularReconstructionState parameters length compact) (kind : Fin 2)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive
      (fullPhysicalForceAction parameters length compact lower positive bounded.le state kind row) :=
  curves.action parameters lower positive bounded
    (fun radius => radialForceKernel parameters length compact state.val radius kind 0)
    (radialForceKernel_regular parameters length compact state.val kind 0)
    (radialForceKernel_conjugated_smooth parameters length compact state.val lower positive bounded kind 0)

end Grad.ActualPolarEquations
