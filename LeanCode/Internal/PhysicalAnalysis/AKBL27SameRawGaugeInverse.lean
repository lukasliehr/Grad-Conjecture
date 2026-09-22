import AKBL26SameWeightedOperatorFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- Exact E C0 G C0=C0 on the SAME physical circle realization. This is the
retained actual determinant inverse, not a newly assumed rough inverse. -/
theorem startupRawGauge_leftInverse {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade+4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)
    (raw : ℝ × Spatial → PhysicalValue 3) (regular : StartupOrbitContinuous raw)
    (angle : ℝ) (point : ClosedDisk) (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    startupRawMatrix (complementExtensionFamily admissible gauge)
      (startupRawComplement (startupRawMatrix (fullGaugeFamily gauge) (startupRawComplement raw))) (angle,point.val) =
      startupRawComplement raw (angle,point.val) := by
  simp only [startupRawMatrix_value,startupRawComplement_value]
  change coefficientPhysicalValue (complementExtensionFamily admissible gauge 0) angle point
    (cartesianComplementValue (fullGaugeValueAction gauge 0 angle
      (cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)))) point) = _
  obtain ⟨localized,_continuousLocal,same⟩ := regular point.val positive inside
  have complementSame (other : ClosedDisk) (normSame : ‖other.val‖ = ‖point.val‖) :
      cartesianComplementValue (fun query : ClosedDisk => raw (angle,query.val)) other = cartesianComplementValue (localized angle) other :=
    startupComplement_norm_locality _ _ other (fun query sameQuery => (same angle query (sameQuery.trans normSame)).symm)
  have gaugeSame : cartesianComplementValue (fullGaugeValueAction gauge 0 angle
      (cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)))) point =
      cartesianComplementValue (fullGaugeValueAction gauge 0 angle (cartesianComplementValue (localized angle))) point := by
    apply startupComplement_norm_locality
    intro other normSame
    exact congrArg (coefficientPhysicalValue (fullGaugeFamily gauge 0) angle other) (complementSame other normSame)
  rw [gaugeSame,complementSame point rfl]
  have block := cartesianGauge_on_range admissible gauge coherent 0 angle
    (cartesianComplementMap (localized angle)) ⟨localized angle,rfl⟩ point
  change cartesianComplementValue (fullGaugeValueAction gauge 0 angle (cartesianComplementValue (localized angle))) point = _ at block
  rw [block]
  exact (actualExtension_block_inverse parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small 0 angle point (cartesianComplementValue (localized angle) point)
    (cartesianRange_tangential (cartesianComplementMap (localized angle)) ⟨localized angle,rfl⟩ point)).1

end Grad.CartesianStartup
