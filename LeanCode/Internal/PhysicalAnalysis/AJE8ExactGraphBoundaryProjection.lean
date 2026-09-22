import AJE6SharedWeightedAmbientUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

variable (parameters : PhaseParameters) (angular cell : ℕ)

private def sourceTupleSlot (slot : Fin 3) : SourceBoundaryTuple →L[ℂ] SourceBoundary 1 :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => SourceBoundary 1) slot

/-- The actual last three source slots, with the first four independent
solution slots set to zero. -/
def sourceSevenTraceMap : SourceBoundaryTuple →L[ℂ] SevenSlotTrace parameters angular cell :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 7 => NegativeTrace parameters angular cell 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![0,0,0,0,
      (sourceBoundaryToNegative parameters angular cell).comp (sourceTupleSlot 0),
      (sourceBoundaryToNegative parameters angular cell).comp (sourceTupleSlot 1),
      (sourceBoundaryToNegative parameters angular cell).comp (sourceTupleSlot 2)])

theorem sourceSevenTraceMap_apply (source : SourceBoundaryTuple) :
    sourceSevenTraceMap parameters angular cell source = sevenSlotTrace parameters angular cell 0 0 source := by
  apply PiLp.ext
  intro slot
  fin_cases slot
  · rfl
  · change 0 = positiveRotationToNegative parameters angular cell 0
    exact (map_zero _).symm
  · change 0 = positiveCellToNegative parameters angular cell 0
    exact (map_zero _).symm
  · change 0 = positiveToNegative parameters angular cell 0
    exact (map_zero _).symm
  · rfl
  · rfl
  · rfl

/-- Bounded complex linear realization of the existing graph-native
three-source boundary vector; its value is unchanged. -/
def graphSourceBoundaryVectorMap : SourceBoundaryTuple →L[ℂ] NegativeTrace parameters angular cell 3 :=
  (fullNegativeKernelAction parameters angular cell (sourceTupleProjectionKernel parameters)).comp
    ((sevenSlotFlatten parameters angular cell).comp (sourceSevenTraceMap parameters angular cell))

theorem graphSourceBoundaryVectorMap_apply (source : SourceBoundaryTuple) :
    graphSourceBoundaryVectorMap parameters angular cell source =
      graphSourceBoundaryVector parameters angular cell source := by
  change fullNegativeKernelAction parameters angular cell (sourceTupleProjectionKernel parameters)
    (sevenSlotFlatten parameters angular cell (sourceSevenTraceMap parameters angular cell source)) = _
  rw [sourceSevenTraceMap_apply]
  rfl

theorem sourceBoundaryToNegative_translation {dimension : ℕ} (tau : OrbitParameter)
    (source : SourceBoundary dimension) :
    sourceBoundaryToNegative parameters angular cell (orbitLpAction (ComplexEuclidean dimension) tau source) =
      orbitLpAction (ComplexEuclidean dimension) tau (sourceBoundaryToNegative parameters angular cell source) := by
  apply lp.ext
  funext mode
  change (sourceToNegativeRatio parameters angular cell mode : ℂ) • (orbitCharacter tau mode • source mode) =
    orbitCharacter tau mode • ((sourceToNegativeRatio parameters angular cell mode : ℂ) • source mode)
  exact smul_comm _ _ _

/-- The graph boundary triple transforms by its genuine common Fourier
character, including the original negative-half trace normalization. -/
theorem graphSourceBoundaryVector_translation (tau : OrbitParameter) (source : SourceBoundaryTuple) :
    graphSourceBoundaryVector parameters angular cell (sourceTupleTranslation tau source) =
      orbitLpAction (ComplexEuclidean 3) tau (graphSourceBoundaryVector parameters angular cell source) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [graphSourceBoundaryVector_coefficient,sourceNegativeCoefficient_translation,graphSourceBoundaryVector_coefficient]
  apply PiLp.ext
  intro slot
  fin_cases slot
  · change negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell (orbitLpAction (ComplexEuclidean 1) tau (source 0))) mode 0 =
      (orbitCharacter tau mode • negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell (source 0)) mode) 0
    rw [sourceBoundaryToNegative_translation,sourceNegativeCoefficient_translation]
  · change negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell (orbitLpAction (ComplexEuclidean 1) tau (source 1))) mode 0 =
      (orbitCharacter tau mode • negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell (source 1)) mode) 0
    rw [sourceBoundaryToNegative_translation,sourceNegativeCoefficient_translation]
  · change negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell (orbitLpAction (ComplexEuclidean 1) tau (source 2))) mode 0 =
      (orbitCharacter tau mode • negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell (source 2)) mode) 0
    rw [sourceBoundaryToNegative_translation,sourceNegativeCoefficient_translation]

end Grad.AnnularStrongOrbit
