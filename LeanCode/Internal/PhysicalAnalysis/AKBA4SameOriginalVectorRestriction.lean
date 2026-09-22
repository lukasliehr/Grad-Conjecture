import AKBA2ExactOriginalPhysicalRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.Constraints Grad.NonlinearQuotientBounds Grad.AnnularKernelL2 Grad.BoundaryLift Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.AnnularOriginalSmoothCore Grad.NonlinearRange Grad.NonlinearProduct
open Grad.GaugeCoefficients.Physical.Ledger Grad.OriginalKernelRetainedDecay

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : ACore parameters 3)

def originalVectorComponent (component : Fin 3) : ACore parameters 1 :=
  Grad.NonlinearQuotientBounds.valueMapCore parameters (matrixUnit (input := 3) (output := 1) 0 component) field

def originalVectorLowRow : DivisionRow 3 lower :=
  bulkMatrixUnit lower 0 0 (originalCoreLowRow parameters lower positive bounded (originalVectorComponent parameters field 0))+
    bulkMatrixUnit lower 1 0 (originalCoreLowRow parameters lower positive bounded (originalVectorComponent parameters field 1))+
    bulkMatrixUnit lower 2 0 (originalCoreLowRow parameters lower positive bounded (originalVectorComponent parameters field 2))

def originalVectorLowCurves : SmoothLowPhysicalRow parameters lower positive
    (originalVectorLowRow parameters lower positive bounded field) :=
  (((originalCoreLowCurves parameters lower positive bounded (originalVectorComponent parameters field 0)).bulkUnit (0 : Fin 3) 0).add
    ((originalCoreLowCurves parameters lower positive bounded (originalVectorComponent parameters field 1)).bulkUnit (1 : Fin 3) 0)).add
    ((originalCoreLowCurves parameters lower positive bounded (originalVectorComponent parameters field 2)).bulkUnit (2 : Fin 3) 0)

theorem originalVectorLowCurves_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalVectorLowCurves parameters lower positive bounded field).fullField bounded (radius,angles) =
      originalCoreCircle parameters field ⟨radius,positive.le.trans inside.1,inside.2⟩ angles := by
  unfold originalVectorLowCurves originalVectorLowRow
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles]
  simp_rw [SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    originalCoreLowCurves_fullField parameters lower positive bounded _ radius inside angles]
  unfold originalVectorComponent originalCoreCircle
  simp_rw [coreValue_valueMap]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [matrixUnit_apply,operatorBasis]

end Grad.OriginalKernelGraphRestriction
