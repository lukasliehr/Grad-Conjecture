import AKBL17PuncturedComplementLocality
import GC18CMapComplement
import GC18CMapAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- The retained actual determinant inverse is a left inverse on the literal
fixed complement of a merely punctured continuous field. This transports
only the needed circle, and retains the original coefficient family. -/
 theorem startupPunctured_gauge_leftInverse {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade+4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) (angle : ℝ) (raw : Spatial → PhysicalValue 3)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (point : ClosedDisk) (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    coefficientPhysicalValue (complementExtensionFamily admissible gauge grade) angle point
      (cartesianComplementValue (fullGaugeValueAction gauge grade angle
        (cartesianComplementValue (fun other : ClosedDisk => raw other.val))) point) =
      cartesianComplementValue (fun other : ClosedDisk => raw other.val) point := by
  obtain ⟨localized,same⟩ := startupCircle_continuousLocalization raw continuousRaw point.val positive inside
  have complementSame (other : ClosedDisk) (normSame : ‖other.val‖ = ‖point.val‖) :
      cartesianComplementValue (fun query : ClosedDisk => raw query.val) other = cartesianComplementValue localized other :=
    startupComplement_norm_locality _ _ other (fun query sameQuery => (same query (sameQuery.trans normSame)).symm)
  have gaugeSame : cartesianComplementValue (fullGaugeValueAction gauge grade angle
      (cartesianComplementValue (fun other : ClosedDisk => raw other.val))) point =
      cartesianComplementValue (fullGaugeValueAction gauge grade angle (cartesianComplementValue localized)) point := by
    apply startupComplement_norm_locality
    intro other normSame
    exact congrArg (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle other) (complementSame other normSame)
  rw [gaugeSame,complementSame point rfl]
  have block := cartesianGauge_on_range admissible gauge coherent grade angle
    (cartesianComplementMap localized) ⟨localized,rfl⟩ point
  change cartesianComplementValue (fullGaugeValueAction gauge grade angle (cartesianComplementValue localized)) point = _ at block
  rw [block]
  exact (actualExtension_block_inverse parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bound small grade angle point (cartesianComplementValue localized point)
    (cartesianRange_tangential (cartesianComplementMap localized) ⟨localized,rfl⟩ point)).1

/-- Algebraic recovery used after the actual gauge and left-inverse laws
have been identified on the SAME field. The operators need not commute. -/
 theorem startupCurrent_circle_recovery_algebra {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (projection gauge extension : Value →L[ℂ] Value) (field : Value)
    (gauged : projection (gauge field) = 0)
    (inverse : extension (projection (gauge (projection field))) = projection field) :
    (field-projection field)-extension (projection (gauge (field-projection field))) = field := by
  rw [map_sub,map_sub,gauged,zero_sub,map_neg,inverse]
  abel

end Grad.CartesianStartup
