import AKY12OriginalWidthCovariantInverse
import GQC68ActualLedgerIsomorphism

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- The literal smooth-field ER3–5 contract on an actual physical ledger.
The two original physical gauges determine Qa; all cells satisfy the exact
zero-order and second-order identities already derived from actualRows. -/
def ActualLedgerReduction {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) : Prop :=
  ∀ (state : CompensatedData L parameters.sigma0 parameters.gamma ell),
    APSmoothMeanZero admissible state.1 →
    ActualPhysicalGaugeMeans ledger (by omega : 2 ≤ 2) (compensatedReconstruct admissible state) →
    apSmoothCurrent admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent
      (actualErQuotient admissible state) = compensatedReconstruct admissible state ∧
    ∀ cell, (actualErCell admissible ledger.val ledger.property.1 state cell).ZeroOrder ∧
      (actualErCell admissible ledger.val ledger.property.1 state cell).SecondOrder

theorem actualLedgerReduction_of_projection {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (laws : ∀ grade, ActualProjectionLaws admissible ledger.val.gaugeDeviation grade) :
    ActualLedgerReduction ledger inverseCoherent := by
  intro state mean gauges
  have current := (actualSmoothGauge_zero_iff_physical ledger (by omega : 2 ≤ 2)
    (compensatedReconstruct admissible state)).mpr gauges
  exact ⟨actualErRows_use_current_projection admissible ledger.val ledger.property.1 inverseCoherent laws state current,
    fun cell => actualErCell_reduction admissible ledger.val ledger.property.1 state mean cell⟩

/-- The coefficient actions in the reduction are exactly the original frame,
rotated-frame and full signed flux matrices. -/
theorem actualLedgerReduction_coefficients {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base) :
    flux_formulaLaw parameters admissible rho alpha delta parameter epsilon base ledger.val ∧
      rotatedPlanar_formulaLaw parameters admissible rho alpha delta parameter epsilon base ledger.val ∧
        rotatedThird_formulaLaw parameters admissible rho alpha delta parameter epsilon base ledger.val :=
  ⟨ledger.property.2.2.2.2.2.1, ledger.property.2.2.2.2.2.2.2.2.1,
    ledger.property.2.2.2.2.2.2.2.2.2⟩

end Grad.CartesianUncompressed
