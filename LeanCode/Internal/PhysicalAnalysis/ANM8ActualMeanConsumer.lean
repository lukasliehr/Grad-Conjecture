import ANM7MeanUniqueness

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
variable {L sigma gamma ell : ℝ}

/-- The explicit mean inverse is one complex-linear map on the actual smooth
source carrier; all original-width and all-grade realizations use this same map. -/
def meanInverseLinear (L sigma gamma ell : ℝ) :
    SmoothCapSource L sigma gamma ell →ₗ[ℂ] CompensatedData L sigma gamma ell :=
  (0 : SmoothCapSource L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1).prod
    ((apSmoothValueMap L sigma gamma ell planarInclusionMap).comp
      (((1 / 2 : ℂ) • apSmoothQuarter L sigma gamma ell).comp (LinearMap.fst ℂ _ _)))

theorem meanInverseLinear_apply (source : SmoothCapSource L sigma gamma ell) :
    meanInverseLinear L sigma gamma ell source = meanState source := rfl

/-- AN7/AN26 on the literal smooth circular carriers. Raw zero is stated before
compatibility; the actual source constraints force G=Hc=0 and the first force jet
vanishes. The same explicit state has both original gauges, both axis first jets,
the exact force/divergence/third rows, high boundary row zero and the original AN8
same-grade bound, and is unique in the raw-zero original circular domain. -/
theorem actualMeanReferenceInverse (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) :
    source.2.1 = 0 ∧ source.2.2 = 0 ∧
    APSmoothAxisFirstJetZero admissible source.1 ∧
    meanInverseLinear L sigma gamma ell source ∈ circularCompensatedCore admissible ∧
    IsRawMeanState admissible (meanInverseLinear L sigma gamma ell source) ∧
    (meanInverseLinear L sigma gamma ell source).1 = 0 ∧
    apSmoothPlanar L sigma gamma ell (meanInverseLinear L sigma gamma ell source).2 =
      (1 / 2 : ℂ) • apSmoothQuarter L sigma gamma ell source.1 ∧
    apSmoothScalar L sigma gamma ell (meanInverseLinear L sigma gamma ell source).2 = 0 ∧
    APSmoothAxisFirstJetZero admissible (meanInverseLinear L sigma gamma ell source).1 ∧
    APSmoothAxisFirstJetZero admissible
      (compensatedReconstruct admissible (meanInverseLinear L sigma gamma ell source)) ∧
    apSmoothComplement L sigma gamma ell
      (compensatedReconstruct admissible (meanInverseLinear L sigma gamma ell source)) = 0 ∧
    circularRows admissible (meanInverseLinear L sigma gamma ell source) = source ∧
    (∀ grade, 1 ≤ grade → circularCoreTrace admissible grade
      (meanInverseLinear L sigma gamma ell source) = 0) ∧
    (∀ grade, compensatedNorm admissible grade (meanInverseLinear L sigma gamma ell source) ≤
      ‖capSourceGrade grade source‖) ∧
    ∀ state : circularCompensatedCore admissible, IsRawMeanState admissible state.val →
      circularRows admissible state.val = source →
      state.val = meanInverseLinear L sigma gamma ell source := by
  have scalar := meanSource_scalars_zero admissible source compatible raw
  have member := meanState_circularCore admissible source compatible raw
  have flat := (mem_compensatedFlatCore admissible (meanState source)).mp member.1
  refine ⟨scalar.1, scalar.2, meanSource_firstJet_zero admissible source compatible raw,
    member, meanState_raw admissible source raw, rfl,
    apPlanar_inclusion admissible (meanVector source.1), apScalar_inclusion admissible (meanVector source.1),
    flat.1.2, flat.2, meanState_complement_zero admissible source compatible,
    meanState_rows admissible source compatible raw, meanState_highBoundary admissible source compatible raw,
    meanState_source_norm_bound admissible source compatible raw, ?_⟩
  intro state stateRaw equations
  exact meanState_unique admissible source state stateRaw (congrArg Prod.fst equations)

/-- Immediate actual-domain consumer: no smooth inverse, recurrence, or final
right-inverse law is assumed to obtain this unique state. -/
theorem actualMeanReferenceInverse_existsUnique (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) :
    ∃! state : circularCompensatedCore admissible,
      IsRawMeanState admissible state.val ∧ circularRows admissible state.val = source := by
  let chosen : circularCompensatedCore admissible :=
    ⟨meanState source, meanState_circularCore admissible source compatible raw⟩
  refine ⟨chosen, ⟨meanState_raw admissible source raw, meanState_rows admissible source compatible raw⟩, ?_⟩
  intro other satisfies
  apply Subtype.ext
  exact meanState_unique admissible source other satisfies.1 (congrArg Prod.fst satisfies.2)

end Grad.ActualMeanInverse
