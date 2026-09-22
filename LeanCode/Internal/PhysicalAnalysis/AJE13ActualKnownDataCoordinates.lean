import AJE12RealKnownOperatorCalculus
import AJE7CompleteSharedDataUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowOrbit
open Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (lower : ℝ) (angular cell : ℕ)

/-- Simultaneous character of the complete high known ambient, retaining
all genuine shared graphs and incoming/outer datum. -/
def highKnownAmbientTranslation (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower angular cell ≃ₗᵢ[ℝ]
      ActualHighKnownAmbient parameters lower angular cell :=
  realHilbertProductEquivalence
    (realHilbertProductEquivalence
      (finiteRealHilbertEquivalence 4 (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau)))
      (finiteRealHilbertEquivalence 3 (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau))))
    (realHilbertProductEquivalence
      (realHilbertProductEquivalence (sourceGraphTranslationEquivalence 1 lower tau)
        (sourceGraphTranslationEquivalence 1 lower tau))
      (realHilbertProductEquivalence (realCharacterEquivalence (outerDatumTranslationEquivalence parameters angular cell tau))
        (realCharacterEquivalence (highIncomingTranslationEquivalence tau))))

def knownAmbientGraphs : ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
    HighKnownGraphHilbert parameters lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((highKnownF0GraphProjection parameters lower angular cell).prod
      (highKnownF2GraphProjection parameters lower angular cell))

def knownAmbientEight : ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 8 lower :=
  ((highKnownEightPacket lower).restrictScalars ℝ).comp (highKnownWeightedProjection parameters lower angular cell)

def knownAmbientDirect (positive : 0 < lower) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 3 lower :=
  ((directKnownThreePacket lower positive).restrictScalars ℝ).comp (highKnownAuxiliaryProjection parameters lower angular cell)

def knownAmbientSourceTuple (positive : 0 < lower) (bounded : lower < 1) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] SourceBoundaryTuple :=
  (highGraphOuterTupleMap parameters lower positive bounded (angular + cell)).comp
    (knownAmbientGraphs parameters lower angular cell)

theorem knownAmbientGraphs_apply (data : ActualHighKnownAmbient parameters lower angular cell) :
    knownAmbientGraphs parameters lower angular cell data = data.ofLp.2.ofLp.1 := rfl

theorem knownAmbientEight_apply (data : ActualHighKnownAmbient parameters lower angular cell) :
    knownAmbientEight parameters lower angular cell data = highKnownEightPacket lower data.ofLp.1.ofLp.1 := rfl

theorem knownAmbientDirect_apply (positive : 0 < lower) (data : ActualHighKnownAmbient parameters lower angular cell) :
    knownAmbientDirect parameters lower angular cell positive data = directKnownThreePacket lower positive data.ofLp.1.ofLp.2 := rfl

theorem knownAmbientSourceTuple_apply (positive : 0 < lower) (bounded : lower < 1)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    knownAmbientSourceTuple parameters lower angular cell positive bounded data =
      highGraphOuterTuple parameters lower positive bounded (angular + cell) data.ofLp.2.ofLp.1.ofLp :=
  highGraphOuterTupleMap_apply parameters lower positive bounded (angular + cell) data.ofLp.2.ofLp.1

theorem knownAmbientSourceTuple_translation (positive : 0 < lower) (bounded : lower < 1)
    (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower angular cell) :
    knownAmbientSourceTuple parameters lower angular cell positive bounded
      (highKnownAmbientTranslation parameters lower angular cell tau data) =
      sourceTupleTranslation tau (knownAmbientSourceTuple parameters lower angular cell positive bounded data) := by
  rw [knownAmbientSourceTuple_apply,knownAmbientSourceTuple_apply]
  exact highGraphOuterTuple_translation parameters lower positive bounded (angular + cell) tau data.ofLp.2.ofLp.1.ofLp

end Grad.AnnularStrongOrbit
