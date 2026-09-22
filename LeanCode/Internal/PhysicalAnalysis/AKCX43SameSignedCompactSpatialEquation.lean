import AKCX42CompactDifferentiatedER

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.SpatialDilation

variable (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)

def startupSame_cutoff_spatialEquation {order : ℕ}
    (field zeroth : GraphGrade 3 order 0 openUnitDisk)
    (tensor : Fin 2 → Fin 2 → GraphGrade 3 order 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 order 0 openUnitDisk)
    (equation : StartupWeakDivDivEquation (base 3 order openUnitDisk (fun _ => 0) field)
      (base 3 order openUnitDisk (fun _ => 0) zeroth)
      (fun outer inner => base 3 order openUnitDisk (fun _ => 0) (tensor outer inner))
      (fun direction => base 3 order openUnitDisk (fun _ => 0) (flux direction))) :
    StartupCompactSpatialEquation order (tsupport cutoff) := by
  have supported := startupCutoffEquation_supported cutoff smooth compact
    (base 3 order openUnitDisk (fun _ => 0) field) (base 3 order openUnitDisk (fun _ => 0) zeroth)
    (fun outer inner => base 3 order openUnitDisk (fun _ => 0) (tensor outer inner))
    (fun direction => base 3 order openUnitDisk (fun _ => 0) (flux direction))
  refine {
    field := startupCutoffSpatialGraph cutoff smooth compact order 0 field
    zeroth := startupCutoffEquationZerothGraph cutoff smooth compact field zeroth tensor flux
    tensor := fun outer inner => startupCutoffSpatialGraph cutoff smooth compact order 0 (tensor outer inner)
    flux := startupCutoffEquationFluxGraph cutoff smooth compact field tensor flux
    fieldSupported := ?_
    zeroSupported := ?_
    tensorSupported := ?_
    fluxSupported := ?_
    equation := ?_ }
  · rw [startupCutoffSpatialGraph_base]
    exact supported.1
  · rw [startupCutoffEquationZerothGraph_base]
    exact supported.2.1
  · intro outer inner
    rw [startupCutoffSpatialGraph_base]
    exact supported.2.2.1 outer inner
  · intro direction
    rw [startupCutoffEquationFluxGraph_base]
    exact supported.2.2.2 direction
  · simp only [startupCutoffSpatialGraph_base,startupCutoffEquationZerothGraph_base,startupCutoffEquationFluxGraph_base]
    exact startupSame_cutoff_divDiv cutoff smooth compact _ _ _ _ equation

/-- Actual signed native equation → exact original phase → actual compact
spatial equation. Every phase and cutoff graph is constructed from the completed induction grade. -/
theorem startupSame_signedCompactSpatialEquation (parameters : PhaseParameters) {L : ℝ}
    (lengthNonzero : L ≠ 0) (scale : Scale) (order : ℕ)
    (field : StartupSignedFamily 3 L scale.val) (tensor : Fin 2 → Fin 2 → StartupSignedFamily 3 L scale.val)
    (flux : Fin 2 → StartupSignedFamily 3 L scale.val)
    (fieldRegular : field.HasSpatialGrade order)
    (tensorRegular : ∀ outer inner, (tensor outer inner).HasSpatialGrade order)
    (fluxRegular : ∀ direction, (flux direction).HasSpatialGrade order)
    (equation : StartupWeakDivDivEquation (field.unweight parameters scale).field 0
      (fun outer inner => ((tensor outer inner).unweight parameters scale).field)
      (fun direction => ((flux direction).unweight parameters scale).field)) (power : ℕ) :
    ∃ data : StartupCompactSpatialEquation order (tsupport cutoff),
      base 3 order openUnitDisk (fun _ => 0) data.field = startupCutoffL2 cutoff smooth compact (field.moment power) ∧
      ∀ outer inner, base 3 order openUnitDisk (fun _ => 0) (data.tensor outer inner) =
        startupCutoffL2 cutoff smooth compact ((tensor outer inner).moment power) := by
  obtain ⟨zeroRegular,lowerRegular⟩ := startupSame_signedPhase_graphs parameters lengthNonzero scale field tensor flux power order
    fieldRegular tensorRegular fluxRegular
  let fieldGraph := (fieldRegular power 0).choose
  let tensorGraph (outer inner : Fin 2) := (tensorRegular outer inner power 0).choose
  let fluxGraph (direction : Fin 2) := (lowerRegular direction).choose
  have fieldSame : base 3 order openUnitDisk (fun _ => 0) fieldGraph = field.moment power := (fieldRegular power 0).choose_spec
  have tensorSame (outer inner : Fin 2) : base 3 order openUnitDisk (fun _ => 0) (tensorGraph outer inner) =
      (tensor outer inner).moment power := (tensorRegular outer inner power 0).choose_spec
  have fluxSame (direction : Fin 2) : base 3 order openUnitDisk (fun _ => 0) (fluxGraph direction) =
      startupSignedPhaseFlux parameters lengthNonzero scale field tensor flux power direction := (lowerRegular direction).choose_spec
  have weighted : StartupWeakDivDivEquation (base 3 order openUnitDisk (fun _ => 0) fieldGraph)
      (base 3 order openUnitDisk (fun _ => 0) zeroRegular.choose)
      (fun outer inner => base 3 order openUnitDisk (fun _ => 0) (tensorGraph outer inner))
      (fun direction => base 3 order openUnitDisk (fun _ => 0) (fluxGraph direction)) := by
    simp only [fieldSame,tensorSame,fluxSame,zeroRegular.choose_spec]
    exact startupSame_signedPhase_equation parameters lengthNonzero scale field tensor flux power equation
  refine ⟨startupSame_cutoff_spatialEquation cutoff smooth compact fieldGraph zeroRegular.choose tensorGraph fluxGraph weighted,?_,?_⟩
  · change base 3 order openUnitDisk (fun _ => 0) (startupCutoffSpatialGraph cutoff smooth compact order 0 fieldGraph) = _
    rw [startupCutoffSpatialGraph_base,fieldSame]
  · intro outer inner
    change base 3 order openUnitDisk (fun _ => 0) (startupCutoffSpatialGraph cutoff smooth compact order 0 (tensorGraph outer inner)) = _
    rw [startupCutoffSpatialGraph_base,tensorSame]

end Grad.CartesianStartup
