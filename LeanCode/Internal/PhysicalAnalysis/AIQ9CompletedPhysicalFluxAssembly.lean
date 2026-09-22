import AIQ8RegularCompletedAddition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularKernelContinuity
open Grad.AnnularCurrentEnergy Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact) (power : ℕ)

def knownSevenBulkAction : DivisionRow 8 lower →L[ℂ] DivisionRow 7 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (fun radius => knownEightToSevenKernel (radialKernelParameters parameters radius))
    (constantMatrixRadialKernel_regular parameters 8 7 knownEightToSevenMap)

/-- Independent physical x and the six known normalized slots, in the original seven-slot order. -/
def assembledSevenBulk (x : DivisionRow 1 lower) (input : DivisionRow 8 lower) : DivisionRow 7 lower :=
  bulkMatrixUnit lower 0 0 x + knownSevenBulkAction parameters lower positive bounded power input

def eliminatedSevenBulkAction : DivisionRow 8 lower →L[ℂ] DivisionRow 7 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (radialEliminatedSevenKernel parameters L compact state)
    (radialEliminatedSevenKernel_regular parameters L compact state)

theorem eliminatedSevenBulkAction_assembled (input : DivisionRow 8 lower) :
    eliminatedSevenBulkAction parameters L compact lower positive bounded state power input =
      assembledSevenBulk parameters lower positive bounded power
        (eliminatedXAction parameters L compact lower positive bounded state power input) input := by
  let injection := constantMatrixRadialKernel_regular parameters 1 7 (matrixUnit 0 0)
  let solved := radialEliminatedXKernel_regular parameters L compact state
  let known := constantMatrixRadialKernel_regular parameters 8 7 knownEightToSevenMap
  have split : eliminatedSevenBulkAction parameters L compact lower positive bounded state power =
      regularRadialBulkAction parameters power lower positive bounded
        (fun radius => fullKernelComposition (constantMatrixKernel (radialKernelParameters parameters radius) 1 7 (matrixUnit 0 0))
          (radialEliminatedXKernel parameters L compact state radius)) (injection.comp solved) +
        knownSevenBulkAction parameters lower positive bounded power :=
    regularRadialBulkAction_add parameters power lower positive bounded _ _ (injection.comp solved) known
  rw [split, add_apply,
    regularRadialBulkAction_comp parameters power lower positive bounded _ _ injection solved, ContinuousLinearMap.comp_apply]
  simp only [regularMatrixUnit_eq_bulk]
  rw [← eliminatedXAction_eq_regular]
  rfl

def normalizedCBulkAction : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (radialNormalizedCKernel parameters L compact state) (radialNormalizedCKernel_regular parameters L compact state)

def normalizedRVBulkAction : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (radialNormalizedRVKernel parameters L compact state) (radialNormalizedRVKernel_regular parameters L compact state)

/-- Actual completed c and rV are computed from the SAME independent x and original seven inputs. -/
def assembledPhysicalBulk (x : DivisionRow 1 lower) (input : DivisionRow 8 lower) : DivisionRow 3 lower :=
  bulkMatrixUnit lower 0 0 x +
    bulkMatrixUnit lower 1 0 (normalizedCBulkAction parameters L compact lower positive bounded state power
      (assembledSevenBulk parameters lower positive bounded power x input)) +
    bulkMatrixUnit lower 2 0 (normalizedRVBulkAction parameters L compact lower positive bounded state power
      (assembledSevenBulk parameters lower positive bounded power x input))

theorem eliminatedBulkAction_assembled (input : DivisionRow 8 lower) :
    eliminatedBulkAction parameters L compact lower positive bounded state power input =
      assembledPhysicalBulk parameters L compact lower positive bounded state power
        (eliminatedXAction parameters L compact lower positive bounded state power input) input := by
  let i0 := constantMatrixRadialKernel_regular parameters 1 3 (matrixUnit 0 0)
  let i1 := constantMatrixRadialKernel_regular parameters 1 3 (matrixUnit 1 0)
  let i2 := constantMatrixRadialKernel_regular parameters 1 3 (matrixUnit 2 0)
  let xr := radialEliminatedXKernel_regular parameters L compact state
  let cr := radialEliminatedCKernel_regular parameters L compact state
  let vr := radialEliminatedRVKernel_regular parameters L compact state
  let seven := radialEliminatedSevenKernel_regular parameters L compact state
  let c := radialNormalizedCKernel_regular parameters L compact state
  let v := radialNormalizedRVKernel_regular parameters L compact state
  let xAction := regularRadialBulkAction parameters power lower positive bounded
    (fun radius => fullKernelComposition (constantMatrixKernel (radialKernelParameters parameters radius) 1 3 (matrixUnit 0 0))
      (radialEliminatedXKernel parameters L compact state radius)) (i0.comp xr)
  let cAction := regularRadialBulkAction parameters power lower positive bounded
    (fun radius => fullKernelComposition (constantMatrixKernel (radialKernelParameters parameters radius) 1 3 (matrixUnit 1 0))
      (radialEliminatedCKernel parameters L compact state radius)) (i1.comp cr)
  let vAction := regularRadialBulkAction parameters power lower positive bounded
    (fun radius => fullKernelComposition (constantMatrixKernel (radialKernelParameters parameters radius) 1 3 (matrixUnit 2 0))
      (radialEliminatedRVKernel parameters L compact state radius)) (i2.comp vr)
  have split : eliminatedBulkAction parameters L compact lower positive bounded state power = xAction + cAction + vAction := by
    rw [eliminatedBulkAction_eq_regular]
    exact (regularRadialBulkAction_add parameters power lower positive bounded _ _ ((i0.comp xr).add (i1.comp cr)) (i2.comp vr)).trans
      (congrArg (fun action : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower => action + vAction)
        (regularRadialBulkAction_add parameters power lower positive bounded _ _ (i0.comp xr) (i1.comp cr)))
  rw [split, add_apply, add_apply]
  dsimp only [xAction, cAction, vAction]
  rw [regularRadialBulkAction_comp parameters power lower positive bounded _ _ i0 xr,
    regularRadialBulkAction_comp parameters power lower positive bounded _ _ i1 cr,
    regularRadialBulkAction_comp parameters power lower positive bounded _ _ i2 vr]
  simp only [ContinuousLinearMap.comp_apply, regularMatrixUnit_eq_bulk]
  have cLaw : regularRadialBulkAction parameters power lower positive bounded
      (radialEliminatedCKernel parameters L compact state) cr =
      (normalizedCBulkAction parameters L compact lower positive bounded state power).comp
        (eliminatedSevenBulkAction parameters L compact lower positive bounded state power) :=
    regularRadialBulkAction_comp parameters power lower positive bounded _ _ c seven
  have vLaw : regularRadialBulkAction parameters power lower positive bounded
      (radialEliminatedRVKernel parameters L compact state) vr =
      (normalizedRVBulkAction parameters L compact lower positive bounded state power).comp
        (eliminatedSevenBulkAction parameters L compact lower positive bounded state power) :=
    regularRadialBulkAction_comp parameters power lower positive bounded _ _ v seven
  rw [cLaw, vLaw]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← eliminatedXAction_eq_regular]
  change bulkMatrixUnit lower (0 : Fin 3) (0 : Fin 1)
      (eliminatedXAction parameters L compact lower positive bounded state power input) +
      bulkMatrixUnit lower (1 : Fin 3) (0 : Fin 1)
        (normalizedCBulkAction parameters L compact lower positive bounded state power
          (eliminatedSevenBulkAction parameters L compact lower positive bounded state power input)) +
      bulkMatrixUnit lower (2 : Fin 3) (0 : Fin 1)
        (normalizedRVBulkAction parameters L compact lower positive bounded state power
          (eliminatedSevenBulkAction parameters L compact lower positive bounded state power input)) = _
  rw [eliminatedSevenBulkAction_assembled]
  rfl

end Grad.AnnularPhysicalSolution
