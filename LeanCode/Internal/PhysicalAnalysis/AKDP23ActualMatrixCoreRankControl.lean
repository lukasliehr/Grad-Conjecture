import AKDP22OriginalCoreRankComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The checked matrix bounds supply a numerical rank profile before the
state, dimension or input core is selected. Its core and rank actions are
the SAME actual original matrix. -/
theorem startupOriginalMatrix_rankControl (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (offset rank : ℕ) (estimateProfile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤estimateProfile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤estimateProfile.deviation grade) :
    ∃ profile : StartupCoreRankProfile,
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset estimateProfile family reference),
      physicalBudget parameters baseField rho curvature offset≤1 →
      Nonempty (StartupCoreRankControl parameters (1+physicalBudget parameters baseField rho curvature (offset+rank)) profile
        (originalMatrixKernel admissible family estimate.actualCoherent)
        (StartupRankOperator.matrix admissible rank family estimate.actualCoherent).coarse) := by
  classical
  obtain ⟨high,highNonnegative,highBound⟩ := startupOriginalMatrix_core_oneHigh parameters admissible lengthNonzero scaleNonzero
    offset rank estimateProfile fixedNonnegative deviationNonnegative
  obtain ⟨base,baseNonnegative,baseBound⟩ := startupOriginalMatrix_core_oneHigh parameters admissible lengthNonzero scaleNonzero
    offset 0 estimateProfile fixedNonnegative deviationNonnegative
  let rem := fun epsilon : ℝ => if positive : 0<epsilon then
    (startupOriginalMatrix_rankRemainder_oneHigh parameters admissible lengthNonzero scaleNonzero offset rank
      estimateProfile fixedNonnegative deviationNonnegative epsilon positive).choose else 0
  have remNonnegative (epsilon : ℝ) (positive : 0<epsilon) : 0≤rem epsilon := by
    dsimp [rem]
    rw [dif_pos positive]
    exact (startupOriginalMatrix_rankRemainder_oneHigh parameters admissible lengthNonzero scaleNonzero offset rank
      estimateProfile fixedNonnegative deviationNonnegative epsilon positive).choose_spec.1
  let profile : StartupCoreRankProfile := ⟨3*base,high,rem,mul_nonneg (by norm_num) baseNonnegative,highNonnegative,remNonnegative⟩
  refine ⟨profile,?_⟩
  intro input output baseField rho curvature family reference estimate low
  let image := fun core : ACore parameters input =>
    (startupOriginalMatrix_core_exists parameters admissible lengthNonzero scaleNonzero family estimate.actualCoherent core).choose
  have same (core : ACore parameters input) :=
    (startupOriginalMatrix_core_exists parameters admissible lengthNonzero scaleNonzero family estimate.actualCoherent core).choose_spec
  refine ⟨{
    action := image
    same := same
    baseBound := ?_
    highBound := ?_
    remainderBound := ?_ }⟩
  · intro core
    have actual := baseBound input output baseField rho curvature family reference estimate core (image core) (same core) low
    simp only [Nat.add_zero] at actual
    change originalGradeNorm 0 (image core)≤3*base*originalGradeNorm 0 core
    apply actual.trans
    have paid := mul_le_mul_of_nonneg_right low (originalGradeNorm_nonnegative 0 core)
    have paidBase := mul_le_mul_of_nonneg_left paid baseNonnegative
    nlinarith only [paidBase]
  · intro core
    exact highBound input output baseField rho curvature family reference estimate core (image core) (same core) low
  · intro epsilon positive core
    have actual := (startupOriginalMatrix_rankRemainder_oneHigh parameters admissible lengthNonzero scaleNonzero offset rank
      estimateProfile fixedNonnegative deviationNonnegative epsilon positive).choose_spec.2
      input output baseField rho curvature family reference estimate core (image core) (same core) low
    change _≤epsilon*originalGradeNorm rank core+rem epsilon*_
    dsimp [rem]
    rw [dif_pos positive]
    exact actual

end Grad.CartesianStartup
