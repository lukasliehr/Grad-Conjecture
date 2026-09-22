import AKDS2ActualInverseTransposeCoreTame
import ACP2ForceMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianStartup Grad.NonlinearProduct Grad.ActualOriginalSourceMoments
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualCurrentPrimitives

/-- The literal original force matrix has zero reference; only its fixed
numerical envelope is enlarged to a nonnegative one. -/
def originalForceAbsoluteProfile (parameters : PhaseParameters) (length : ℝ) : EstimateProfile :=
  ⟨fun _ => 0,fun grade => |(forceMatrixProfile parameters length).deviation grade|⟩

theorem forceMatrixFamily_absoluteEstimate (parameters : PhaseParameters)
    (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters field rho epsilon 5 (originalForceAbsoluteProfile parameters length)
      (forceMatrixFamily parameters length epsilon field)
      (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 3) := by
  refine ⟨forceMatrixFamily_coherent parameters length rho epsilon field small,
    zeroFamily_coherent _ _ _ _ _ _,fun _ => le_rfl,fun _ => abs_nonneg _,?_,?_⟩
  · intro grade
    simp only [zeroFamily,norm_zero,originalForceAbsoluteProfile,le_refl]
  · intro grade
    change ‖forceMatrixFamily parameters length epsilon field grade - 0‖ ≤ _
    rw [sub_zero]
    exact (forceMatrixFamily_bound parameters length rho epsilon field small grade).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _)
        (physicalBudget_nonnegative parameters field rho epsilon (5+grade)))

/-- A single original core for the SAME literal force matrix action, all
grades at once, with one high coefficient payment times the input base. -/
theorem actualOriginalForce_core_tame (parameters : PhaseParameters) (length : ℝ) :
    ∃ constants : ℕ → ℝ,(∀ grade,0≤constants grade) ∧
    ∀ (baseField : ACore parameters 3) (rho epsilon : ℝ)
      (small : physicalBudget parameters baseField rho epsilon 6≤originalCoefficientLowRadius parameters length)
      (covariant : ACore parameters 3),
      ∃ force : ACore parameters 3,
        (originalSourceMoments parameters force).field =
          originalMatrixKernel (unitDiskAdmissible parameters)
            (forceMatrixFamily parameters length epsilon baseField)
            (forceMatrixFamily_coherent parameters length rho epsilon baseField small)
            (originalSourceMoments parameters covariant).field ∧
        ∀ grade,originalGradeNorm grade force ≤ constants grade *
          (originalGradeNorm grade covariant +
            (1+physicalBudget parameters baseField rho epsilon (5+grade))*originalGradeNorm 0 covariant) := by
  obtain ⟨constants,nonnegative,bounds⟩ := startupOriginalMatrix_core_tame parameters
    (unitDiskAdmissible parameters) one_ne_zero one_ne_zero 5
    (originalForceAbsoluteProfile parameters length) (fun _ => le_rfl) (fun _ => abs_nonneg _)
  refine ⟨constants,nonnegative,?_⟩
  intro baseField rho epsilon small covariant
  have lowFive : physicalBudget parameters baseField rho epsilon 5≤1 :=
    (physicalBudget_monotone parameters baseField rho epsilon (by norm_num : 5≤6)).trans
      (small.trans (min_le_left _ _))
  exact bounds 3 3 baseField rho epsilon (forceMatrixFamily parameters length epsilon baseField)
    (zeroFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (forceMatrixFamily_absoluteEstimate parameters length rho epsilon baseField small) covariant lowFive

end Grad.ActualPhysicalField
