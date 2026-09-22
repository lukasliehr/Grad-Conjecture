import AKDP17ActualOriginalRankMatrixRemainder
import GC18ExtensionEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Fixed, nonnegative all-grade profiles for the SAME full gauge and
complement extension occurring in the actual current operator. Only the
already retained B6 determinant neighborhood is required to construct them. -/
theorem startupCurrent_actualProfiles (parameters : PhaseParameters) {L ell rho curvature : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (baseField : ACore parameters 3)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (constants : ℕ → ℝ) (nonnegative : ∀ grade,0≤constants grade)
    (low : physicalBudget parameters baseField rho curvature 6≤1)
    (bounds : ∀ grade,‖gauge grade‖≤constants grade*physicalBudget parameters baseField rho curvature (grade+4))
    (small : physicalBudget parameters baseField rho curvature 6≤determinantLowRadius constants) :
    FamilyEstimate parameters baseField rho curvature 12 (unitProfile constants)
      (fullGaugeFamily gauge) (identityFamily L parameters.sigma0 parameters.gamma ell 3) ∧
    FamilyEstimate parameters baseField rho curvature 12 (unitProfile (complementExtensionConstant constants))
      (complementExtensionFamily admissible gauge) (identityFamily L parameters.sigma0 parameters.gamma ell 3) := by
  constructor
  · change FamilyEstimate parameters baseField rho curvature 12 (unitProfile constants)
      (fun grade => identityFamily L parameters.sigma0 parameters.gamma ell 3 grade+gauge grade)
      (identityFamily L parameters.sigma0 parameters.gamma ell 3)
    apply unitPerturbation_estimate parameters baseField rho curvature 12 3 gauge coherent constants nonnegative
    intro grade
    exact (bounds grade).trans (mul_le_mul_of_nonneg_left
      (physicalBudget_monotone parameters baseField rho curvature (by omega : grade+4≤grade+12)) (nonnegative grade))
  · refine {
      actualCoherent := complementExtensionFamily_coherent admissible gauge coherent inverseCoherent
      referenceCoherent := identityFamily_coherent L parameters.sigma0 parameters.gamma ell 3
      fixedNonnegative := fun _ => Nat.cast_nonneg _
      deviationNonnegative := fun _ => abs_nonneg _
      referenceBound := identityFamily_norm_le L parameters.sigma0 parameters.gamma ell 3
      deviationBound := ?_ }
    intro grade
    change ‖complementExtensionFamily admissible gauge grade-identityFamily L parameters.sigma0 parameters.gamma ell 3 grade‖ ≤
      complementExtensionConstant constants grade*physicalBudget parameters baseField rho curvature (12+grade)
    exact (complementExtension_deviation_bound parameters admissible baseField rho curvature gauge coherent constants nonnegative low bounds small grade).trans
      (mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters baseField rho curvature (by omega : grade+6≤12+grade)) (abs_nonneg _))

end Grad.CartesianStartup
