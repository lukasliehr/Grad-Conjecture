import AJX1OriginalFiveBlockAmbient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace Grad.AnnularFullGraph
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)

/-- Discard only the independent boundary coordinates from the full datum.
Both original source graphs and both complete residuals are retained. -/
def originalFullSourceProjection (data : OriginalStrongCarrier parameters lower 0 0) :
    OriginalFullSourceBlocks parameters lower := data.val.ofLp.1

/-- Observation of the simultaneous original source/solution space into
exactly the five AK31 blocks, independently of any equation or inverse. -/
def originalFiveBlockObservation
    (pair : OriginalStrongCarrier parameters lower 0 0 × OriginalCoupledSpace lower length positive) :
    OriginalFiveBlockAmbient parameters lower length positive :=
  WithLp.toLp 2 (pair.2,originalFullSourceProjection parameters lower pair.1)

theorem originalFullSourceProjection_continuous :
    Continuous (originalFullSourceProjection parameters lower) :=
  continuous_fst.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp continuous_subtype_val)

theorem originalFiveBlockObservation_continuous :
    Continuous (originalFiveBlockObservation parameters lower length positive) :=
  (WithLp.prod_continuous_toLp 2 _ _).comp
    (continuous_snd.prodMk ((originalFullSourceProjection_continuous parameters lower).comp continuous_fst))

theorem originalFiveBlockObservation_retained
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive) :
    (originalFiveBlockObservation parameters lower length positive (data,candidate)).ofLp.1 = candidate := rfl

theorem originalFiveBlockObservation_sources
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive) :
    (originalFiveBlockObservation parameters lower length positive (data,candidate)).ofLp.2 = data.val.ofLp.1 := rfl

end Grad.AnnularFullGraph
