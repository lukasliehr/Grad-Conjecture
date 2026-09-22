import AKCO15ActualSignedPowerResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.SpatialDilation
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger

/-- The inner native induction genuinely closes every signed power from
its same compact weak ER equation and punctured complement graphs. It
never assumes spatial regularity of the top power or its coefficient outputs. -/
theorem startupSame_allSignedPowers_first (parameters : PhaseParameters) (L : ℝ) (lengthNonzero : L ≠ 0)
    (scale : Scale) (admissible : Admissible L parameters.sigma0 parameters.gamma scale.val)
    (data : LedgerData L parameters.sigma0 parameters.gamma scale.val) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (insideDisk : tsupport inside ⊆ openUnitDisk)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second)
    (regular : FieldH1 →L[ℂ] FieldH1)
    (compatible : ∀ input, valueInclusion (regular input) =
      startupGenuinePrincipalL2 outer outerSmooth outerCompact admissible data coherent inverseCoherent (valueInclusion input))
    (coarseSmall : ‖startupGenuinePrincipalL2 outer outerSmooth outerCompact admissible data coherent inverseCoherent‖ < 1)
    (fineSmall : ‖regular‖ < 1)
    (field : StartupSignedFamily 3 L scale.val)
    (known : Fin 2 → Fin 2 → StartupSignedFirstFamily 3 L scale.val)
    (flux : Fin 2 → StartupSignedFamily 3 L scale.val)
    (equation : StartupWeakDivDivEquation (field.unweight parameters scale).field 0
      (fun outer inner => ((startupSignedFullTensor admissible data coherent inverseCoherent field known outer inner).unweight parameters scale).field)
      (fun direction => ((flux direction).unweight parameters scale).field))
    (outside : ∀ power : ℕ, ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph =
        field.moment power - startupCutoffL2 inside insideSmooth insideCompact (field.moment power)) :
    ∀ power : ℕ, ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph = field.moment power := by
  intro power
  induction power using Nat.strong_induction_on with
  | h power lower =>
    obtain ⟨improved,same⟩ := startupSame_signedPower_h1 parameters L lengthNonzero scale admissible data coherent inverseCoherent
      outer inside outerSmooth insideSmooth outerCompact insideCompact insideDisk plateau radial regular compatible coarseSmall fineSmall
      field known flux equation power lower
    obtain ⟨disk,diskSame,_⟩ := startupH1_diskGraph_exists improved
    rw [same,startupPlaneRestriction_extension] at diskSame
    obtain ⟨annular,annularSame⟩ := outside power
    refine ⟨disk+annular,?_⟩
    rw [map_add,diskSame,annularSame]
    abel

end Grad.CartesianStartup
