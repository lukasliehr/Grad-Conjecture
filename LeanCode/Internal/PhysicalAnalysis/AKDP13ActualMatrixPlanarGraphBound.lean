import AKDP12ActualMatrixBaseAndInputBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.CartesianCoreRecovery Grad.CellWeights
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- No-loss planar graph estimate for the genuine full original matrix.
Each nonempty spatial allocation is paid by BZ30 on the SAME input core.
The high coefficient multiplies only that input's independent base norm. -/
theorem startupEstimatedMatrix_planarGraph (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset grade : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input) (jet : GraphGrade input grade grade openUnitDisk)
      (image : GraphGrade output grade 0 openUnitDisk),
      base input grade openUnitDisk (fun _ => grade) jet = (originalSourceMoments parameters core).field →
      base output grade openUnitDisk (fun _ => 0) image =
        originalMatrixKernel admissible family estimate.actualCoherent (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖image‖ ≤ constant*(originalGradeNorm grade core+
        (1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
  classical
  let baseBound := startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma profile
  have baseNonnegative : 0≤baseBound := startupMatrixProfileBaseBound_nonnegative admissible profile fixedNonnegative deviationNonnegative
  have each (index : JetIndex grade) := startupMatrixOrderedRemainder_oneHigh parameters admissible offset
    (degree index) (derivativeWord index) profile fixedNonnegative deviationNonnegative 1 zero_lt_one
  choose constants nonnegative estimates using each
  let leading := (Fintype.card (JetIndex grade) : ℝ)*(baseBound+1)
  let remainder := ∑ index,constants index
  have leadingNonnegative : 0≤leading := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have remainderNonnegative : 0≤remainder := Finset.sum_nonneg (fun index _ => nonnegative index)
  refine ⟨leading+remainder,add_nonneg leadingNonnegative remainderNonnegative,?_⟩
  intro input output baseField rho curvature family reference estimate core jet image same imageSame low
  have bound (index : JetIndex grade) :
      ‖image.val index‖ ≤ (baseBound+1)*originalGradeNorm grade core+
        constants index*((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
    have indexBound := degree_le index
    have weak := startupActualMatrix_weakLeadingSplit admissible family estimate.actualCoherent
      (derivativeWord index) (degree_le index) (by omega : degree index-1≤grade) jet
    rw [same] at weak
    have imageWeak := recoveredDerivative_hasWeak output grade openUnitDisk (fun _ => 0) index image
    rw [imageSame] at imageWeak
    have equation := weakEquality output openUnitDisk openUnitDisk_isOpen (degree index) (derivativeWord index)
      (derivativeWord index) (fun _ => rfl) _ _ _ imageWeak weak
    rw [Realization.recoveredDerivative_apply,inverseFieldCLM_zero,ContinuousLinearMap.id_apply] at equation
    rw [equation]
    apply (norm_add_le _ _).trans
    have inputBound : ‖orderedDerivative input grade (degree index) openUnitDisk (fun _ => grade) (degree_le index) jet (derivativeWord index)‖ ≤
        originalGradeNorm grade core := by
      rw [startupOrdered_originalCore parameters core jet same]
      exact (startupOriginalOrdered_norm parameters admissible core (degree index) (derivativeWord index)).trans
        (originalGradeNorm_mono (degree_le index) core)
    have main := ((originalMatrixKernel admissible family estimate.actualCoherent).le_opNorm _).trans
      (mul_le_mul (startupEstimatedMatrix_lowNorm parameters admissible estimate low) inputBound (norm_nonneg _) baseNonnegative)
    have lower := estimates index input output grade grade baseField rho curvature family reference estimate core jet same
      (degree_le index) (by omega : degree index-1≤grade) low
    have coreBound := originalGradeNorm_mono (degree_le index) core
    have coefficientBound := physicalBudget_monotone parameters baseField rho curvature (by omega : offset+degree index≤offset+grade)
    have tailBound := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (add_le_add_right coefficientBound 1) (originalGradeNorm_nonnegative 0 core)) (nonnegative index)
    have paid := add_le_add main (lower.trans (add_le_add (by simpa only [one_mul] using coreBound) tailBound))
    exact paid.trans_eq (by ring)
  have finite := startupFiniteHilbert_norm_le_sum (fun index : JetIndex grade => image.val index)
  change ‖image‖ ≤ _ at finite
  apply (finite.trans (Finset.sum_le_sum (fun index _ => bound index))).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.sum_mul]
  change (Fintype.card (JetIndex grade) : ℝ)*((baseBound+1)*originalGradeNorm grade core)+
    remainder*((1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) ≤ _
  have highNonnegative := mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative parameters baseField rho curvature (offset+grade)))
    (originalGradeNorm_nonnegative 0 core)
  have first := mul_nonneg remainderNonnegative (originalGradeNorm_nonnegative grade core)
  have second := mul_nonneg leadingNonnegative highNonnegative
  dsimp only [leading] at *
  nlinarith only [first,second]

end Grad.CartesianStartup
