import AKBZ24SameFullCellRestoredOperator

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

theorem sharpOrthogonalKernel_identity {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) :
    sharpOrthogonalKernel admissible family coherent rank displacement positive word index (LinearIsometryEquiv.refl ℝ _)=
      sharpAllocatedKernel admissible family coherent rank displacement positive word index := rfl

/-- CT9 paid on the SAME accepted original normalized full-cell operator,
with its actual input reserve restored. No pointwise coefficient or raw
operator equality is assumed: BZ22--24 prove the exact identification. -/
theorem restoredOriginalKernel_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset phaseRank inputRank : ℕ) (phasePositive : 0<phaseRank)
    (phaseWord : Fin phaseRank → Fin 2) (index : CartesianMultiIndex)
    (inputWord : CartesianWord inputRank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (inputDimension outputDimension : ℕ) (base : ACore parameters 3) (rho curvature : ℝ)
        (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension)
        (_estimate : FamilyEstimate parameters base rho curvature offset profile family reference)
        (field : ACore parameters inputDimension),
      physicalBudget parameters base rho curvature offset≤1 →
      ‖startupAllocatedKernel admissible (family (cartesianOrder index+phaseRank)) phaseRank phaseWord
        (sharpCoefficientIndex index phaseRank) (sharpCoefficientIndex_allocation phaseRank index)
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-1) inputWord)‖≤
      epsilon*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (offset+(phaseRank+cartesianOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  obtain ⟨remainder,nonnegative,payment⟩ := sharpFullPhaseBlock_oneHigh parameters admissible offset phaseRank inputRank
    phasePositive phaseWord index (LinearIsometryEquiv.refl ℝ _) inputWord profile fixedNonnegative deviationNonnegative epsilon epsilonPositive
  refine ⟨remainder,nonnegative,?_⟩
  intro inputDimension outputDimension base rho curvature family reference estimate field low
  have bound := payment inputDimension outputDimension base rho curvature family reference estimate field low
  simp_rw [sharpOrthogonalKernel_identity] at bound
  rw [originalRestoredOperator_eq_sharpSum admissible family estimate.actualCoherent phaseRank inputRank phasePositive phaseWord index parameters field inputWord]
  exact bound

end Grad.OriginalCartesianTameEstimate
