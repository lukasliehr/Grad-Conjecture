import AKDP3SameLocalizedOriginalCore
import AKCG6ActualMatrixWeakLeadingSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.WeightedJets.Ordered Grad.NonlinearProduct
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.OriginalCartesianTameEstimate Grad.RepresentedKernel.SpatialProduct

/-- The actual nonempty spatial Leibniz remainder, with every restored
input identified with the SAME original core. Its constant precedes the
coefficient state and the unknown; only one high coefficient times M0
remains. -/
theorem startupMatrixOrderedRemainder_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset rank : ℕ) (word : Word rank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (input output order weight : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input) (jet : GraphGrade input order weight openUnitDisk)
      (_same : base input order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
      (bound : rank≤order) (reserve : rank-1≤weight),
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖startupMatrixOrderedRemainder admissible family estimate.actualCoherent word bound reserve jet‖ ≤
        epsilon*originalGradeNorm rank core+
          constant*((1+physicalBudget parameters baseField rho curvature (offset+rank))*originalGradeNorm 0 core) := by
  classical
  let selectedSets := (Finset.univ : Finset (Finset (Fin rank))).erase ∅
  let delta := epsilon/((selectedSets.card : ℝ)+1)
  have deltaPositive : 0<delta := div_pos epsilonPositive (by positivity)
  have each (selected : Finset (Fin rank)) (member : selected ∈ selectedSets) :=
    actualFullDerivative_oneHigh parameters admissible offset
      (degree (startupComplementIndex word le_rfl selected)) (startupSelectedCoefficientIndex word selected)
      (by rw [startupSelectedCoefficientIndex_order]; exact Finset.card_pos.mpr ((startupMatrixRemainder_lowerRank selected member).1))
      (derivativeWord (startupComplementIndex word le_rfl selected)) profile fixedNonnegative deviationNonnegative delta deltaPositive
  choose constants nonnegative estimates using each
  refine ⟨∑ selected ∈ selectedSets.attach,constants selected.val selected.property,
    Finset.sum_nonneg (fun selected _ => nonnegative selected.val selected.property),?_⟩
  intro input output order weight baseField rho curvature family reference estimate core jet same bound reserve low
  have indexDegree (selected : Finset (Fin rank)) :
      derivativeOrder (startupSelectedCoefficientIndex word selected)+degree (startupComplementIndex word le_rfl selected)=rank := by
    rw [startupSelectedCoefficientIndex_order,startupComplementIndex,wordIndex_degree]
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl selected
  have eachBound (selected : ↥selectedSets) :
      ‖startupDerivativeKernel admissible family estimate.actualCoherent (startupSelectedCoefficientIndex word selected.val)
        (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected.val reserve)
          (startupComplementIndex word bound selected.val) jet)‖ ≤
      delta*originalGradeNorm rank core+constants selected.val selected.property*
        ((1+physicalBudget parameters baseField rho curvature (offset+rank))*originalGradeNorm 0 core) := by
    rw [startupReservedDerivative_originalCarrier parameters admissible core jet same]
    have result := estimates selected.val selected.property input output baseField rho curvature family reference estimate core low
    rw [indexDegree] at result
    exact result
  have leading : (selectedSets.card : ℝ)*delta≤epsilon := by
    have ratio : (selectedSets.card : ℝ)/((selectedSets.card : ℝ)+1)≤1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = epsilon*((selectedSets.card : ℝ)/((selectedSets.card : ℝ)+1)) := by dsimp only [delta]; ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  have represented := Finset.sum_attach selectedSets (fun selected =>
    startupDerivativeKernel admissible family estimate.actualCoherent (startupSelectedCoefficientIndex word selected)
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
        (startupComplementIndex word bound selected) jet))
  change (∑ selected ∈ selectedSets.attach,_) = startupMatrixOrderedRemainder admissible family estimate.actualCoherent word bound reserve jet at represented
  rw [← represented]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun selected _ => eachBound selected)).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_attach,nsmul_eq_mul,← Finset.sum_mul]
  exact add_le_add (by nlinarith only [mul_le_mul_of_nonneg_right leading (originalGradeNorm_nonnegative rank core)]) le_rfl

end Grad.CartesianStartup
