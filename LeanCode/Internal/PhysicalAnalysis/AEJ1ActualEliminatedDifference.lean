import AHW20CompletedEliminatedBulkAction
import AHX9ExactRetainedL2Consumer
import AEG11ExactEnergyPacketConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ)

/-- The completed action of the literal circular eliminated eight-input kernel. -/
def circularEliminatedBulkAction : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (fun r => circularEliminatedBulkKernel (radialKernelParameters parameters r) L)
    (fixedRadialKernel_regular parameters _ (fun _ _ => sameCircularEliminatedBulkKernel _ _ L))

theorem eliminatedBulkAction_eq_regular :
    eliminatedBulkAction parameters L compact lower positive bounded state power =
      regularRadialBulkAction parameters power lower positive bounded
        (radialEliminatedBulkKernel parameters L compact state)
        (radialEliminatedBulkKernel_regular parameters L compact state) := by
  symm
  exact regularRadialBulkAction_eq_completed parameters power lower positive bounded _ _ _ _ _

theorem eliminatedBulkErrorAction_eq_regular :
    eliminatedBulkErrorAction parameters L compact lower positive bounded state power =
      regularRadialBulkAction parameters power lower positive bounded
        (fun r => fullKernelSub (radialEliminatedBulkKernel parameters L compact state r)
          (circularEliminatedBulkKernel (radialKernelParameters parameters r) L))
        (radialEliminatedBulkError_regular parameters L compact state) := by
  symm
  exact regularRadialBulkAction_eq_completed parameters power lower positive bounded _ _ _ _ _

/-- The bounded error action is the actual difference of the two completed
physical operators, with the same Fourier weights and radial storage. -/
theorem eliminatedBulkErrorAction_eq_sub :
    eliminatedBulkErrorAction parameters L compact lower positive bounded state power =
      eliminatedBulkAction parameters L compact lower positive bounded state power -
        circularEliminatedBulkAction parameters L lower positive bounded power := by
  rw [eliminatedBulkErrorAction_eq_regular, eliminatedBulkAction_eq_regular]
  exact regularRadialBulkAction_sub parameters power lower positive bounded _ _ _ _

end Grad.AnnularKernelL2
