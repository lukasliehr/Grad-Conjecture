import ANM1FirstTaylorJet

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.NonlinearDivision

variable {L sigma gamma ell : ℝ}

/-- Literal raw angular sector zero on the actual smooth source carrier:
vector equivariance and scalar angular mode zero, cell by cell. -/
def IsRawMeanSource (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) : Prop :=
  (∀ cell, equivariantAverageJet (apSmoothJet admissible 2 cell source.1) = apSmoothJet admissible 2 cell source.1) ∧
  (∀ cell, angularClosedJet 0 (apSmoothJet admissible 1 cell source.2.1) = apSmoothJet admissible 1 cell source.2.1) ∧
  (∀ cell, angularClosedJet 0 (apSmoothJet admissible 1 cell source.2.2) = apSmoothJet admissible 1 cell source.2.2)

theorem actualSource_conditions (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible) :
    (apSmoothQrad L sigma gamma ell source.1 = source.1 ∧ APSmoothAxisValueZero admissible source.1 ∧
      APSmoothAxisValueZero admissible (apSmoothCurl admissible source.1)) ∧
    APSmoothMeanZero admissible source.2.1 ∧
      APSmoothMeanZero admissible source.2.2 ∧ APSmoothAxisFirstJetZero admissible source.2.2 := by
  simpa only [smoothCapSourceCore, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, mem_apSmoothAxisValues, mem_apSmoothMeanFree,
    mem_apSmoothAxisFirsts, and_assoc] using compatible

theorem meanSource_scalars_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : source.2.1 = 0 ∧ source.2.2 = 0 := by
  have conditions := actualSource_conditions admissible source compatible
  constructor
  · apply apSmoothJet_ext admissible
    intro cell
    exact ((raw.2.1 cell).symm.trans (conditions.2.1 cell)).trans (map_zero (apSmoothJet admissible 1 cell)).symm
  · apply apSmoothJet_ext admissible
    intro cell
    exact ((raw.2.2 cell).symm.trans (conditions.2.2.1 cell)).trans (map_zero (apSmoothJet admissible 1 cell)).symm

theorem tangential_of_mean_Qrad (field : ClosedJet 2)
    (mean : equivariantAverageJet field = field)
    (radial : field - (1 / 2 : ℂ) • (equivariantAverageJet field +
      reflectedVectorJet (equivariantAverageJet field)) = field) : tangentialJet field = field := by
  rw [mean] at radial
  have removed : (1 / 2 : ℂ) • (field + reflectedVectorJet field) = 0 := sub_eq_self.mp radial
  have sumZero : field + reflectedVectorJet field = 0 :=
    (smul_eq_zero.mp removed).resolve_left (by norm_num)
  have reflected : reflectedVectorJet field = -field := eq_neg_of_add_eq_zero_right sumZero
  rw [tangentialJet_eq, mean, reflected, sub_neg_eq_add, ← two_smul ℂ field, smul_smul]
  norm_num

theorem meanSource_tangential (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) :
    apSmoothTangential L sigma gamma ell source.1 = source.1 := by
  have radial := (actualSource_conditions admissible source compatible).1.1
  apply apSmoothJet_ext admissible
  intro cell
  rw [apSmoothTangential_jet]
  apply tangential_of_mean_Qrad _ (raw.1 cell)
  exact (apSmoothQrad_jet admissible source.1 cell).symm.trans
    (congrArg (apSmoothJet admissible 2 cell) radial)

theorem meanSource_firstJet_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : APSmoothAxisFirstJetZero admissible source.1 := by
  have tangent := meanSource_tangential admissible source compatible raw
  have curl := (actualSource_conditions admissible source compatible).1.2.2
  have cellFlat (cell : ℤ) : ClosedFirstJetZero (apSmoothJet admissible 2 cell source.1) := by
    have tangentCell := (apSmoothTangential_jet admissible source.1 cell).symm.trans
      (congrArg (apSmoothJet admissible 2 cell) tangent)
    rw [← tangentCell]
    apply tangentialJet_firstJet_zero
    have curlCell := congrArg (fun value : ComplexEuclidean 1 => value 0) (curl cell)
    rw [apSmoothCurl_jet] at curlCell
    exact curlCell
  constructor
  · intro cell
    exact (cellFlat cell).1
  · intro direction cell
    rw [apSmoothPartial_jet]
    exact (cellFlat cell).2 direction

end Grad.ActualMeanInverse
