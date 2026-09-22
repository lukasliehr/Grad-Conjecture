import GC18APInverseAll
import GC18BoundsConsumer

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- CT_GC19: the actual completed original AP2 multiplier, every grade and
all Fourier cells, with its literal field realization and no width loss. -/
theorem completeWeightedMultiplier {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output grade : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (field : apGrade L sigma gamma ell input grade) :
    0 ≤ apMultiplierConstant L sigma gamma grade ∧
      ‖apCompletedBilinear admissible input output grade coefficient field‖ ≤
        apMultiplierConstant L sigma gamma grade * ‖coefficient‖ * ‖field‖ ∧
      ∀ angle : ℝ, apL2PhysicalValue admissible angle
        (apCompletedBilinear admissible input output grade coefficient field) =
        closedOperatorL2 (cMapCoefficient admissible grade input output angle coefficient)
          (apL2PhysicalValue admissible angle field) :=
  ⟨apMultiplierConstant_nonnegative admissible grade, apMultiplier_bound admissible coefficient field,
    fun angle => apMultiplier_L2 admissible angle coefficient field⟩

/-- Full CT_GC18 on the actual GC17 physical ledger. One fixed low
neighborhood works for every grade. Etilde is asserted to invert C0*C only
on the literal complete AP2 subspace V=ran C0, never on the ambient space. -/
def ActualRadialGaugeInverseGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
    ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          physicalBudget parameters base rho epsilon 12 ≤ 1 →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ‖determinantInverseInput admissible ledger.val.gaugeDeviation 0‖ ≤ 1 / 2 ∧
            (∀ grade, radialLedgerSize admissible ledger.val.gaugeDeviation grade ≤
              constants grade * physicalBudget parameters base rho epsilon (grade + 6)) ∧
            (∀ grade angle point,
              familyMatrix (determinantFamily admissible ledger.val.gaugeDeviation) grade angle point *
                familyMatrix (determinantInverseFamily admissible ledger.val.gaugeDeviation) grade angle point = 1 ∧
              familyMatrix (determinantInverseFamily admissible ledger.val.gaugeDeviation) grade angle point *
                familyMatrix (determinantFamily admissible ledger.val.gaugeDeviation) grade angle point = 1) ∧
            ∀ grade (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade),
              field ∈ apComplementRange L parameters.sigma0 parameters.gamma ell grade →
              apExtensionMap admissible ledger.val.gaugeDeviation grade field ∈
                apComplementRange L parameters.sigma0 parameters.gamma ell grade ∧
              apExtensionMap admissible ledger.val.gaugeDeviation grade
                (apGaugeMap admissible ledger.val.gaugeDeviation grade field) = field ∧
              apGaugeMap admissible ledger.val.gaugeDeviation grade
                (apExtensionMap admissible ledger.val.gaugeDeviation grade field) = field

theorem actualRadialGaugeInverse (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualRadialGaugeInverseGoal parameters L radius threshold := by
  obtain ⟨ledgerRadius, ledgerRadiusPositive, ledgerRadiusOne, gaugeConstants, higherConstants,
    gaugeConstantsNonnegative, _, supplied⟩ := actualLedger parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨min ledgerRadius (determinantLowRadius gaugeConstants),
    lt_min ledgerRadiusPositive (determinantLowRadius_positive gaugeConstants),
    (min_le_left _ _).trans ledgerRadiusOne, fullLedgerConstant gaugeConstants,
    fullLedgerConstant_nonnegative gaugeConstantsNonnegative, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low _bounded
  have lowSix := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)).trans low.le
  have ledgerSmall := lowSix.trans (min_le_left _ _)
  have determinantSmall := lowSix.trans (min_le_right _ _)
  have unitSmall := ledgerSmall.trans ledgerRadiusOne
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg rho]
  obtain ⟨ledger, primitiveMargin, ledgerBounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base ledgerSmall
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      gaugeConstants grade * physicalBudget parameters base rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (ledgerBounds grade).1
  have gaugeCoherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  refine ⟨ledger, primitiveMargin,
    determinant_base_margin parameters admissible base rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall,
    fun grade => radialLedgerSize_bound parameters admissible base rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall grade,
    fun grade angle point => determinantInverse_two_sided parameters admissible base rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative
      unitSmall gaugeBound determinantSmall grade angle point, ?_⟩
  intro grade field member
  exact ⟨apExtensionMap_mem parameters admissible base rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative
    unitSmall gaugeBound determinantSmall grade field member,
    apGaugeMap_two_sided_inverse parameters admissible base rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative
      unitSmall gaugeBound determinantSmall grade field member⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
