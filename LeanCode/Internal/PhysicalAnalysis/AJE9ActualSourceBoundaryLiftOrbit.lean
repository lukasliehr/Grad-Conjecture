import AJE8ExactGraphBoundaryProjection
import AJA13RealOrbitColumns

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularHighInverseOrbit

private def sourcePrecomposeOperator {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (mapping : X →L[ℂ] E) : (E →L[ℂ] F) →L[ℝ] (X →L[ℂ] F) :=
  ((ContinuousLinearMap.compL ℂ X E F).flip mapping).restrictScalars ℝ

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryInverseState parameters L compact) (traceAngular traceCell : ℕ)

/-- Actual source boundary lift kernel jet acting on the genuine shared
three-source trace. The original negative-half grade is unchanged. -/
def graphSourceLiftOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    SourceBoundaryTuple →L[ℂ] NegativeTrace parameters traceAngular traceCell 1 :=
  (boundaryOrbitJetAction parameters traceAngular traceCell
    (actualSourceBoundaryLiftKernel state) tau angular cell).comp
      (graphSourceBoundaryVectorMap parameters traceAngular traceCell)

theorem graphSourceLiftOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell angular cell)
      (orbitColumns (graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell (angular + 1) cell tau)
        (graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell angular (cell + 1) tau)) tau := by
  let restriction : (NegativeTrace parameters traceAngular traceCell 3 →L[ℂ]
      NegativeTrace parameters traceAngular traceCell 1) →L[ℝ]
      (SourceBoundaryTuple →L[ℂ] NegativeTrace parameters traceAngular traceCell 1) :=
    sourcePrecomposeOperator (graphSourceBoundaryVectorMap parameters traceAngular traceCell)
  have derivative := HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter)
    (F := NegativeTrace parameters traceAngular traceCell 3 →L[ℂ] NegativeTrace parameters traceAngular traceCell 1)
    (G := SourceBoundaryTuple →L[ℂ] NegativeTrace parameters traceAngular traceCell 1) tau
    (ContinuousLinearMap.hasFDerivAt
      (E := NegativeTrace parameters traceAngular traceCell 3 →L[ℂ] NegativeTrace parameters traceAngular traceCell 1)
      (F := SourceBoundaryTuple →L[ℂ] NegativeTrace parameters traceAngular traceCell 1) restriction)
    (boundaryOrbitJetAction_hasFDerivAt parameters traceAngular traceCell (actualSourceBoundaryLiftKernel state) tau angular cell)
  apply derivative.congr_fderiv
  exact orbitDifferential_comp restriction _ _

theorem graphSourceLiftOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell angular cell) :=
  orbitTower_contDiff _ (graphSourceLiftOrbitJet_hasFDerivAt parameters L compact state traceAngular traceCell) angular cell

/-- Exact conjugation of the previously checked source boundary lift;
there is no translated physical state or source trace premise. -/
theorem graphSourceLiftOrbit_apply (tau : OrbitParameter) (source : SourceBoundaryTuple) :
    graphSourceLiftOrbitJet parameters L compact state traceAngular traceCell 0 0 tau source =
      orbitLpAction (ComplexEuclidean 1) tau
        (graphSourceBoundaryLiftOnHigh state traceAngular traceCell
          (sourceTupleTranslation (-tau) source)).val := by
  unfold graphSourceLiftOrbitJet boundaryOrbitJetAction
  rw [kernelOrbitJet_zero,fullNegativeKernelAction_orbit]
  change orbitLpAction (ComplexEuclidean 1) tau
      (fullNegativeKernelAction parameters traceAngular traceCell (actualSourceBoundaryLiftKernel state)
        (orbitLpAction (ComplexEuclidean 3) (-tau)
          (graphSourceBoundaryVectorMap parameters traceAngular traceCell source))) = _
  rw [graphSourceBoundaryVectorMap_apply,← graphSourceBoundaryVector_translation]
  congr 1
  exact (actualSourceBoundaryTerm_kernel state traceAngular traceCell _).symm

end Grad.AnnularStrongOrbit
