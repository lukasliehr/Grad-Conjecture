import AJE10SourceLiftJetOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse Grad.AnnularStrongData

private def sourceGraphPairFirst (parameters : PhaseParameters) (lower : ℝ) :
    HighKnownGraphHilbert parameters lower →L[ℝ] HighF0SourceGraph parameters lower :=
  (ContinuousLinearMap.fst ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap
private def sourceGraphPairSecond (parameters : PhaseParameters) (lower : ℝ) :
    HighKnownGraphHilbert parameters lower →L[ℝ] HighF2SourceGraph parameters lower :=
  (ContinuousLinearMap.snd ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)

/-- The actual three endpoint values of the two shared radial graphs as
one bounded real linear map. RF0 is traced from the same F0 graph. -/
def highGraphOuterTupleMap : HighKnownGraphHilbert parameters lower →L[ℝ] SourceBoundaryTuple :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => SourceBoundary 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (annularEndpointInclusion parameters 1 (radialEndpointRadius lower 1) 0 0 1 0 (by omega) (by omega)).comp
        ((totalSourceTrace parameters 1 lower positive bounded 1 0 grade 1).comp (sourceGraphPairFirst parameters lower)),
      (sourceRotationTrace parameters 1 lower positive bounded 0 grade 1).comp (sourceGraphPairFirst parameters lower),
      (totalSourceTrace parameters 1 lower positive bounded 0 0 grade 1).comp (sourceGraphPairSecond parameters lower)])

theorem highGraphOuterTupleMap_apply (graphs : HighKnownGraphHilbert parameters lower) :
    highGraphOuterTupleMap parameters lower positive bounded grade graphs =
      highGraphOuterTuple parameters lower positive bounded grade graphs.ofLp := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> rfl

theorem highGraphOuterTupleMap_translation (tau : OrbitParameter) (graphs : HighKnownGraphHilbert parameters lower) :
    highGraphOuterTupleMap parameters lower positive bounded grade
      (realHilbertProductEquivalence (sourceGraphTranslationEquivalence 1 lower tau)
        (sourceGraphTranslationEquivalence 1 lower tau) graphs) =
      sourceTupleTranslation tau (highGraphOuterTupleMap parameters lower positive bounded grade graphs) := by
  rw [highGraphOuterTupleMap_apply,highGraphOuterTupleMap_apply]
  exact highGraphOuterTuple_translation parameters lower positive bounded grade tau graphs.ofLp

private theorem graphPairTriple_bound {E F D : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup D] (graphs : WithLp 2 (E × F)) (output : D)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ‖output‖ ≤ constant * (2 * ‖graphs.ofLp.1‖ + ‖graphs.ofLp.2‖)) :
    ‖output‖ ≤ (3 * constant) * ‖graphs‖ := by
  have first := hilbert_first_bound graphs
  have second := hilbert_second_bound graphs
  have sum : 2 * ‖graphs.ofLp.1‖ + ‖graphs.ofLp.2‖ ≤ 3 * ‖graphs‖ := by linarith only [first,second]
  exact bound.trans ((mul_le_mul_of_nonneg_left sum nonnegative).trans_eq (by ring))

theorem highGraphOuterTupleMap_uniform_bound (lowerHalf : lower ≤ 1 / 2)
    (graphs : HighKnownGraphHilbert parameters lower) :
    ‖highGraphOuterTupleMap parameters lower positive bounded grade graphs‖ ≤
      (3 * uniformSourceOuterConstant) * ‖graphs‖ := by
  rw [highGraphOuterTupleMap_apply]
  exact graphPairTriple_bound (E := HighF0SourceGraph parameters lower) (F := HighF2SourceGraph parameters lower)
    (D := SourceBoundaryTuple) graphs
    (highGraphOuterTuple parameters lower positive bounded grade graphs.ofLp)
    uniformSourceOuterConstant uniformSourceOuterConstant_nonnegative
    (highGraphOuterTuple_uniform_bound parameters lower positive lowerHalf grade graphs.ofLp)

end Grad.AnnularStrongOrbit
