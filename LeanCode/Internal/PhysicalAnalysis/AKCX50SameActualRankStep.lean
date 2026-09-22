import AKCX48ActualNestedRankDistribution
import AKCX49RankFirstGraphAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered Grad.TensorBootstrap Grad.SpatialDilation
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The exact final clause of the accepted B10 rank resolvent, on one fixed
actual ledger and one fixed outer cutoff. -/
def StartupActualRankResolvable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ledger : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent ledger) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.gaugeDeviation))
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer) (rank : ℕ) : Prop :=
  ∀ (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank),
    (∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2
          (distributionEmbedding ((StartupRankOperator.principalTensor admissible rank ledger coherent inverseCoherent index.1 index.2).localizedCoarse
            outer smooth compact original word))))+
          distributionEmbedding (zeroth word)+
          ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) →
      ∃ improved : StartupOrderedH1 rank, startupOrderedValue rank improved = original

/-- The actual rank resolvent closes the next graph of a top signed power
using only the completed spatial grade and strictly lower signed powers. -/
theorem startupSame_actualRank_step (parameters : PhaseParameters) {L : ℝ}
    (lengthNonzero : L ≠ 0) (scale : Scale)
    (admissible : Admissible L parameters.sigma0 parameters.gamma scale.val)
    (ledger : LedgerData L parameters.sigma0 parameters.gamma scale.val) (coherent : LedgerCoherent ledger)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.gaugeDeviation))
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (plateau : ∀ point ∈ tsupport inside, outer point = 1)
    (localizer : TestLocalizer openUnitDisk (tsupport outer))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second)
    (rank : ℕ) (resolves : StartupActualRankResolvable admissible ledger coherent inverseCoherent outer outerSmooth outerCompact rank)
    (field : StartupSignedFamily 3 L scale.val) (regular : field.HasSpatialGrade rank)
    (known : Fin 2 → Fin 2 → StartupSignedFirstFamily 3 L scale.val)
    (knownRegular : ∀ one two order, (known one two).toStartupSignedFamily.HasSpatialGrade order)
    (flux : Fin 2 → StartupSignedFamily 3 L scale.val) (fluxRegular : ∀ direction, (flux direction).HasSpatialGrade rank)
    (equation : StartupWeakDivDivEquation (field.unweight parameters scale).field 0
      (fun one two => ((startupSignedFullTensor admissible ledger coherent inverseCoherent field known one two).unweight parameters scale).field)
      (fun direction => ((flux direction).unweight parameters scale).field))
    (power : ℕ) (lower : ∀ q < power, ∃ graph : GraphGrade 3 (rank+1) 0 openUnitDisk,
      base 3 (rank+1) openUnitDisk (fun _ => 0) graph = field.moment q) :
    ∃ next : GraphGrade 3 (rank+1) 0 openUnitDisk,
      base 3 (rank+1) openUnitDisk (fun _ => 0) next = startupCutoffL2 inside insideSmooth insideCompact (field.moment power) := by
  have tensors (one two : Fin 2) : (startupSignedFullTensor admissible ledger coherent inverseCoherent field known one two).HasSpatialGrade rank :=
    (StartupSignedAction.actualPrincipal_allWeightSpatial admissible rank ledger coherent inverseCoherent lengthNonzero scale.property.1.ne' field regular one two).add
      (knownRegular one two rank)
  obtain ⟨data,fieldSame,tensorSame⟩ := startupSame_signedCompactSpatialEquation inside insideSmooth insideCompact
    parameters lengthNonzero scale rank field (startupSignedFullTensor admissible ledger coherent inverseCoherent field known) flux
    regular tensors fluxRegular equation power
  have lowerFirst : ∀ q < power, ∃ first : StartupFirst (startupTensorDimension 3 rank),
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) first =
        (field.spatialCutoff inside insideSmooth insideCompact).rankDerivative (regular.spatialCutoff inside insideSmooth insideCompact) q := by
    intro q bound
    obtain ⟨higher,same⟩ := lower q bound
    apply StartupSignedFamily.rankDerivative_firstOfHigher
    refine ⟨startupCutoffSpatialGraph inside insideSmooth insideCompact (rank+1) 0 higher,?_⟩
    rw [startupCutoffSpatialGraph_base,same]
    rfl
  have leading := startupSame_localizedPrincipal_rankLeading admissible ledger coherent inverseCoherent lengthNonzero scale.property.1.ne'
    inside insideSmooth insideCompact radial rank field regular known knownRegular power lowerFirst data fieldSame tensorSame
  obtain ⟨zeroth,lowerFlux,distribution⟩ := startupSame_nestedRank_distribution data (isClosed_tsupport inside)
    outer outerSmooth outerCompact plateau localizer (StartupRankOperator.principalTensor admissible rank ledger coherent inverseCoherent) leading
  obtain ⟨improved,same⟩ := resolves _ zeroth lowerFlux distribution
  have first (word : Fin rank → Fin 2) : ∃ graph : StartupFirst 3, base 3 1 openUnitDisk (fun _ => 0) graph =
      orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field word := by
    obtain ⟨graph,graphSame,_⟩ := startupH1_diskGraph_exists (improved word)
    have coordinate := congrArg (fun tuple : StartupOrderedL2 rank => tuple word) same
    change valueInclusion (improved word) = startupPlaneExtension
      (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field word) at coordinate
    rw [coordinate,startupPlaneRestriction_extension] at graphSame
    exact ⟨graph,graphSame⟩
  obtain ⟨next,nextSame⟩ := startupRankFirst_nextGraph data.field first
  exact ⟨next,nextSame.trans fieldSame⟩

end Grad.CartesianStartup
