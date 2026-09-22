import AAZ4PhysicalLeibnizCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev AnnularRawState (lower : ℝ) := AnnularRawFamily lower × AnnularRawFamily lower
abbrev AnnularRawSource (lower : ℝ) := AnnularRawFamily lower × (AnnularRawFamily lower × AnnularRawFamily lower)

def annularAngularISymbol (mode : HighAnnularMode) : ℂ := Complex.I * ((mode.val.1 : ℝ) : ℂ)
def annularLongitudinalISymbol (length : ℝ) (mode : HighAnnularMode) : ℂ :=
  Complex.I * (((mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2) : ℝ) : ℂ)
def annularLongitudinalSourceSymbol (length : ℝ) (mode : HighAnnularMode) : ℂ :=
  (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ)

/-- Canonical modewise physical jets. Only smaller solution orders are used;
no weighted membership or unspecified higher derivative is an input. The
formulas are precisely the differentiated original two physical rows. -/
def annularPhysicalStateJet (lower : ℝ) (positive : 0 < lower) (length : ℝ)
    (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower) (index : ℕ) : AnnularRawState lower :=
  Nat.strongRecOn index (fun index previous =>
    match index with
    | 0 => initial
    | order + 1 =>
      let pRadial := ∑ index ∈ Finset.range (order + 1), order.choose index •
        annularReciprocalJet lower positive 1 index ((previous (order - index) (Nat.lt_succ_of_le (Nat.sub_le _ _))).1)
      let xiRadial := ∑ index ∈ Finset.range (order + 1), order.choose index •
        annularReciprocalJet lower positive 1 index ((previous (order - index) (Nat.lt_succ_of_le (Nat.sub_le _ _))).2)
      let xiSquare := ∑ index ∈ Finset.range (order + 1), order.choose index •
        annularReciprocalJet lower positive 2 index ((previous (order - index) (Nat.lt_succ_of_le (Nat.sub_le _ _))).2)
      (pRadial + annularRawSymbol lower annularAngularISymbol xiSquare +
        annularRawSymbol lower (annularLongitudinalISymbol length) (previous order (Nat.lt_succ_self order)).2 +
        (source order).2.1 + annularRawSymbol lower (annularLongitudinalSourceSymbol length) (source order).2.2,
       (-2 : ℝ) • xiRadial + annularRawSymbol lower (fun mode => -annularDSymbol mode)
          (previous order (Nat.lt_succ_self order)).1 + (source order).1))

theorem annularPhysicalStateJet_zero (lower : ℝ) (positive : 0 < lower) (length : ℝ)
    (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower) :
    annularPhysicalStateJet lower positive length initial source 0 = initial := by
  unfold annularPhysicalStateJet
  rw [Nat.strongRecOn_eq]

/-- Readable exact Leibniz recurrence for the same canonical jets. -/
theorem annularPhysicalStateJet_succ (lower : ℝ) (positive : 0 < lower) (length : ℝ)
    (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower) (order : ℕ) :
    annularPhysicalStateJet lower positive length initial source (order + 1) =
      (annularLeibniz lower positive 1 order (fun index => (annularPhysicalStateJet lower positive length initial source index).1) +
        annularRawSymbol lower annularAngularISymbol
          (annularLeibniz lower positive 2 order (fun index => (annularPhysicalStateJet lower positive length initial source index).2)) +
        annularRawSymbol lower (annularLongitudinalISymbol length) (annularPhysicalStateJet lower positive length initial source order).2 +
        (source order).2.1 + annularRawSymbol lower (annularLongitudinalSourceSymbol length) (source order).2.2,
       (-2 : ℝ) • annularLeibniz lower positive 1 order (fun index => (annularPhysicalStateJet lower positive length initial source index).2) +
         annularRawSymbol lower (fun mode => -annularDSymbol mode) (annularPhysicalStateJet lower positive length initial source order).1 +
         (source order).1) := by
  unfold annularPhysicalStateJet
  rw [Nat.strongRecOn_eq]
  rfl

theorem annularLeibniz_zero (lower : ℝ) (positive : 0 < lower) (base : ℕ)
    (jet : ℕ → AnnularRawFamily lower) :
    annularLeibniz lower positive base 0 jet = annularRawRadiusPower lower positive base (jet 0) := by
  simp only [annularLeibniz, zero_add, Finset.sum_range_one, Nat.choose_zero_right, zero_tsub,
    annularReciprocalJet, annularReciprocalCoefficient_zero, Nat.add_zero, one_smul]

end Grad.AnnularRadialJets
