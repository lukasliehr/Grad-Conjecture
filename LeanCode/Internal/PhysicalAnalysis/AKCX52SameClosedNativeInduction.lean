import AKCX50SameActualRankStep
import AKCX51SameAnnularAllSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered Grad.TensorBootstrap Grad.SpatialDilation
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupL2_zeroGraph (field : StartupL2 3) : ∃ graph : GraphGrade 3 0 0 openUnitDisk,
    base 3 0 openUnitDisk (fun _ => 0) graph = field := by
  have weak (index : JetIndex 0) : Grad.WeakTesting.Commutation.HasWeakOrderedDerivative 3 openUnitDisk
      (degree index) (derivativeWord index) field field := by
    rcases index with ⟨⟨one,two⟩,bound⟩
    have zeros : one = 0 ∧ two = 0 := by omega
    rcases zeros with ⟨rfl,rfl⟩
    exact (Grad.WeakTesting.Commutation.zero 3 openUnitDisk openUnitDisk_isOpen _ _ _).mpr rfl
  exact ⟨startupGraphFromWeak field (fun _ => field) rfl weak,
    startupGraphFromWeak_base field (fun _ => field) rfl weak⟩

theorem StartupSignedFamily.spatialGrade_zero {L ell : ℝ} (field : StartupSignedFamily 3 L ell)
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) : field.HasSpatialGrade 0 :=
  field.hasSpatialGrade_of_zero lengthNonzero scaleNonzero (fun power => startupL2_zeroGraph (field.moment power))

/-- Closed spatial/cell induction on the actual composed ER equation.
The same fixed rank resolvent is used at rank zero and every higher rank;
all signed powers and all cell reserves are proved together. -/
theorem startupSame_native_allSpatialGrades (parameters : PhaseParameters) {L : ℝ}
    (lengthNonzero : L ≠ 0) (scale : Scale)
    (admissible : Admissible L parameters.sigma0 parameters.gamma scale.val)
    (ledger : LedgerData L parameters.sigma0 parameters.gamma scale.val) (coherent : LedgerCoherent ledger)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.gaugeDeviation))
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (plateau : ∀ point ∈ tsupport inside, outer point = 1)
    (localizer : TestLocalizer openUnitDisk (tsupport outer))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second)
    (resolves : ∀ rank, StartupActualRankResolvable admissible ledger coherent inverseCoherent outer outerSmooth outerCompact rank)
    (field : StartupSignedFamily 3 L scale.val)
    (known : Fin 2 → Fin 2 → StartupSignedFirstFamily 3 L scale.val)
    (knownRegular : ∀ one two order, (known one two).toStartupSignedFamily.HasSpatialGrade order)
    (flux : Fin 2 → StartupSignedFamily 3 L scale.val)
    (fluxRegular : ∀ order, field.HasSpatialGrade order → ∀ direction, (flux direction).HasSpatialGrade order)
    (equation : StartupWeakDivDivEquation (field.unweight parameters scale).field 0
      (fun one two => ((startupSignedFullTensor admissible ledger coherent inverseCoherent field known one two).unweight parameters scale).field)
      (fun direction => ((flux direction).unweight parameters scale).field))
    (outside : ∀ order power : ℕ, ∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph = field.moment power-
        startupCutoffL2 inside insideSmooth insideCompact (field.moment power)) :
    ∀ order, field.HasSpatialGrade order := by
  intro order
  induction order with
  | zero => exact field.spatialGrade_zero lengthNonzero scale.property.1.ne'
  | succ order completed =>
    apply field.hasSpatialGrade_of_zero lengthNonzero scale.property.1.ne'
    intro power
    induction power using Nat.strong_induction_on with
    | h power lower =>
      obtain ⟨interior,interiorSame⟩ := startupSame_actualRank_step parameters lengthNonzero scale admissible ledger coherent inverseCoherent
        outer inside outerSmooth insideSmooth outerCompact insideCompact plateau localizer radial order (resolves order)
        field completed known knownRegular flux (fluxRegular order completed) equation power lower
      obtain ⟨annular,annularSame⟩ := outside (order+1) power
      refine ⟨interior+annular,?_⟩
      rw [map_add,interiorSame,annularSame]
      abel

end Grad.CartesianStartup
