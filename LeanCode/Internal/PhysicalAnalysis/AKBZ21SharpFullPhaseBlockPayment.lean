import AKBZ20ActualFullFrameOneHigh

noncomputable section
set_option maxHeartbeats 1300000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

/-- Full positive-phase block of the exact displacement decomposition,
including every d=1,...,a. This is the actual L2 sum, not a sum of unrelated
high-order majorants. The same low input norm pays every coefficient term. -/
theorem sharpFullPhaseBlock_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset phaseRank inputRank : ℕ) (phasePositive : 0<phaseRank)
    (phaseWord : Fin phaseRank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (inputWord : CartesianWord inputRank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (inputDimension outputDimension : ℕ) (base : ACore parameters 3) (rho curvature : ℝ)
        (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension)
        (estimate : FamilyEstimate parameters base rho curvature offset profile family reference)
        (field : ACore parameters inputDimension),
      physicalBudget parameters base rho curvature offset≤1 →
      ‖∑ displacement : Fin phaseRank,
        sharpOrthogonalKernel admissible family estimate.actualCoherent phaseRank (displacement.val+1)
          phasePositive phaseWord index orthogonal
          (originalMixedDerivativeCarrier parameters admissible field inputRank
            (phaseRank-(displacement.val+1)) inputWord)‖≤
      epsilon*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (offset+(phaseRank+cartesianOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  classical
  have deltaPositive : 0<epsilon/(phaseRank:ℝ) := div_pos epsilonPositive (by exact_mod_cast phasePositive)
  have perTerm (displacement : Fin phaseRank) := sharpKernel_oneHigh parameters admissible offset phaseRank
    (displacement.val+1) inputRank phasePositive (Nat.succ_pos _) (Nat.succ_le_iff.mpr displacement.isLt)
    phaseWord index orthogonal inputWord profile fixedNonnegative deviationNonnegative (epsilon/phaseRank) deltaPositive
  choose constants nonnegative estimates using perTerm
  refine ⟨∑ displacement,constants displacement,Finset.sum_nonneg (fun displacement _ => nonnegative displacement),?_⟩
  intro inputDimension outputDimension base rho curvature family reference estimate field low
  have factor : (phaseRank:ℝ)*((epsilon/phaseRank)*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field)=
      epsilon*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field := by field_simp
  calc
    _≤∑ displacement : Fin phaseRank,
      ‖sharpOrthogonalKernel admissible family estimate.actualCoherent phaseRank (displacement.val+1)
        phasePositive phaseWord index orthogonal
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-(displacement.val+1)) inputWord)‖ := norm_sum_le _ _
    _≤∑ displacement : Fin phaseRank,
        ((epsilon/phaseRank)*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field+
          constants displacement*((1+physicalBudget parameters base rho curvature
            (offset+(phaseRank+cartesianOrder index+inputRank)))*originalGradeNorm 0 field)) :=
      Finset.sum_le_sum (fun displacement _ =>
        estimates displacement inputDimension outputDimension base rho curvature family reference estimate field low)
    _=(phaseRank:ℝ)*((epsilon/phaseRank)*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field)+
        (∑ displacement,constants displacement)*((1+physicalBudget parameters base rho curvature
          (offset+(phaseRank+cartesianOrder index+inputRank)))*originalGradeNorm 0 field) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.sum_mul]
    _=_ := by rw [factor]

end Grad.OriginalCartesianTameEstimate
