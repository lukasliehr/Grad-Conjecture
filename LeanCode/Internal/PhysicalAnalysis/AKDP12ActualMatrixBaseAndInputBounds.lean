import AKDP10SameOriginalPlanarGraphNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.CartesianCoreRecovery Grad.CellWeights
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Original reserve zero is exactly the SAME unscaled ordered derivative. -/
theorem startupOriginalOrdered_eq_zeroReserve {dimension : ℕ}
    (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (core : ACore parameters dimension) (rank : ℕ) (word : CartesianWord rank) :
    originalSourceOrderedJoint parameters core rank word =
      originalMixedDerivativeCarrier parameters admissible core rank 0 word := by
  apply Grad.CellWeights.fields_ext dimension openUnitDisk
  intro cell
  rw [originalSourceOrderedJoint_coordinate,originalMixedDerivativeCarrier_coordinate]
  simp only [originalSourceOrderedCoordinate,originalMixedDerivativeCoordinate,pow_zero,one_smul]

theorem startupOriginalOrdered_norm {dimension : ℕ} (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (core : ACore parameters dimension) (rank : ℕ) (word : CartesianWord rank) :
    ‖originalSourceOrderedJoint parameters core rank word‖ ≤ originalGradeNorm rank core := by
  rw [startupOriginalOrdered_eq_zeroReserve parameters admissible]
  simpa only [Nat.add_zero] using originalMixedDerivativeCarrier_norm parameters admissible core rank 0 word

theorem startupOrdered_originalCore {dimension order rank weight : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (jet : GraphGrade dimension order weight openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
    (bound : rank≤order) (word : CartesianWord rank) :
    orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound jet word =
      originalSourceOrderedJoint parameters core rank word := by
  have actual := orderedDerivative_hasWeak dimension order rank openUnitDisk (fun _ => weight) bound jet word
  rw [same] at actual
  exact weakEquality dimension openUnitDisk openUnitDisk_isOpen rank word word (fun _ => rfl) _ _ _ actual
    (originalSourceOrderedJoint_weak parameters core rank word)

/-- A numerical low-order matrix bound, fixed before the coefficient state. -/
def startupMatrixProfileBaseBound (L sigma gamma : ℝ) (profile : EstimateProfile) : ℝ :=
  2*startupDerivativeConstant L sigma gamma zeroDerivativeIndex*(profile.fixed 0+profile.deviation 0)

theorem startupMatrixProfileBaseBound_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade) (deviationNonnegative : ∀ grade,0≤profile.deviation grade) :
    0≤startupMatrixProfileBaseBound L sigma gamma profile :=
  mul_nonneg (mul_nonneg (by norm_num) (startupDerivativeConstant_nonnegative admissible zeroDerivativeIndex))
    (add_nonneg (fixedNonnegative 0) (deviationNonnegative 0))

theorem startupEstimatedMatrix_lowNorm (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    {offset input output : ℕ} {profile : EstimateProfile} {baseField : ACore parameters 3} {rho curvature : ℝ}
    {family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
    (low : physicalBudget parameters baseField rho curvature offset≤1) :
    ‖originalMatrixKernel admissible family estimate.actualCoherent‖ ≤
      startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma profile := by
  have coefficient := estimatedFamily_norm_le estimate 0
  simp only [Nat.add_zero] at coefficient
  have paid := mul_le_mul_of_nonneg_left (add_le_add_right low 1)
    (add_nonneg (estimate.fixedNonnegative 0) (estimate.deviationNonnegative 0))
  have total := mul_le_mul_of_nonneg_left (coefficient.trans paid)
    (startupDerivativeConstant_nonnegative admissible zeroDerivativeIndex)
  apply (originalMatrixKernel_bound admissible family estimate.actualCoherent).trans
  exact total.trans_eq (by unfold startupMatrixProfileBaseBound; ring)

end Grad.CartesianStartup
