import AKCX43SameSignedCompactSpatialEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.SpatialDilation

variable (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)

/-- The constructed compact equation retains all four literal base formulas. -/
theorem startupSame_signedCompactSpatialEquation_explicit (parameters : PhaseParameters) {L : ℝ}
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
      (∀ outer inner, base 3 order openUnitDisk (fun _ => 0) (data.tensor outer inner) =
        startupCutoffL2 cutoff smooth compact ((tensor outer inner).moment power)) ∧
      base 3 order openUnitDisk (fun _ => 0) data.zeroth =
        startupCutoffEquationZeroth cutoff smooth compact (field.moment power)
          (startupSignedPhaseZeroth parameters lengthNonzero scale field tensor flux power)
          (fun outer inner => (tensor outer inner).moment power)
          (startupSignedPhaseFlux parameters lengthNonzero scale field tensor flux power) ∧
      ∀ direction,base 3 order openUnitDisk (fun _ => 0) (data.flux direction)=
        startupCutoffEquationFlux cutoff smooth compact (field.moment power)
          (fun outer inner => (tensor outer inner).moment power)
          (startupSignedPhaseFlux parameters lengthNonzero scale field tensor flux power) direction := by
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
  refine ⟨startupSame_cutoff_spatialEquation cutoff smooth compact fieldGraph zeroRegular.choose tensorGraph fluxGraph weighted,?_,?_,?_,?_⟩
  · change base 3 order openUnitDisk (fun _ => 0) (startupCutoffSpatialGraph cutoff smooth compact order 0 fieldGraph) = _
    rw [startupCutoffSpatialGraph_base,fieldSame]
  · intro outer inner
    change base 3 order openUnitDisk (fun _ => 0) (startupCutoffSpatialGraph cutoff smooth compact order 0 (tensorGraph outer inner)) = _
    rw [startupCutoffSpatialGraph_base,tensorSame]

  · change base 3 order openUnitDisk (fun _ => 0)
      (startupCutoffEquationZerothGraph cutoff smooth compact fieldGraph zeroRegular.choose tensorGraph fluxGraph)=_
    rw [startupCutoffEquationZerothGraph_base,fieldSame,zeroRegular.choose_spec]
    simp only [tensorSame,fluxSame]
  · intro direction
    change base 3 order openUnitDisk (fun _ => 0)
      (startupCutoffEquationFluxGraph cutoff smooth compact fieldGraph tensorGraph fluxGraph direction)=_
    rw [startupCutoffEquationFluxGraph_base,fieldSame]
    simp only [tensorSame,fluxSame]

end Grad.CartesianStartup
