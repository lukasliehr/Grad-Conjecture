import AKBL27SameRawGaugeInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade+4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)
    (field : StartupL2 3) (raw : ℝ × Spatial → PhysicalValue 3)
    (same : StartupWeightedRep parameters.sigma0 parameters.gamma ell field raw)
    (regular : StartupOrbitContinuous raw)

include same regular low bound small nonnegative in
/-- The actual determinant inverse identity holds on the SAME weighted L2
field before H1 startup, by exact full-cell matrix/C0 realization. -/
theorem startupSameRough_gauge_leftInverse :
    originalMatrixKernel admissible (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent)
      (originalComplementKernel (originalMatrixKernel admissible (fullGaugeFamily gauge)
        (fullGaugeFamily_coherent gauge coherent) (originalComplementKernel field))) = originalComplementKernel field := by
  have complementRep := same.complement regular
  have gaugeRep := StartupWeightedRep.matrix admissible (fullGaugeFamily gauge)
    (fullGaugeFamily_coherent gauge coherent) complementRep regular.complement
  have gaugeRegular := regular.complement.matrix admissible (fullGaugeFamily gauge)
  have projectedRep := gaugeRep.complement gaugeRegular
  have extensionRep := StartupWeightedRep.matrix admissible (complementExtensionFamily admissible gauge)
    (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent) projectedRep gaugeRegular.complement
  have rawSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ angle,
      startupRawMatrix (complementExtensionFamily admissible gauge)
        (startupRawComplement (startupRawMatrix (fullGaugeFamily gauge) (startupRawComplement raw))) (angle,point) =
        startupRawComplement raw (angle,point) := by
    filter_upwards [startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point nonzero inside
    intro angle
    exact startupRawGauge_leftInverse parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small
      raw regular angle ⟨point,openDiskMembershipClosed point inside⟩ (norm_pos_iff.mpr nonzero) inside
  exact (extensionRep.congr_raw rawSame).ext complementRep

include same regular low bound small nonnegative in
/-- Qa(Q0 a_C)=a_C on the SAME rough full-cell field, once its two actual
native gauges have been identified as C0(G a_C)=0. No H1 premise is used. -/
theorem startupSameRough_current_recovers
    (gauged : originalComplementKernel (originalMatrixKernel admissible (fullGaugeFamily gauge)
      (fullGaugeFamily_coherent gauge coherent) field) = 0) :
    originalCurrentKernel admissible gauge coherent inverseCoherent (originalCircleKernel field) = field := by
  have inverse := startupSameRough_gauge_leftInverse parameters admissible base rho epsilon gauge coherent inverseCoherent
    constants nonnegative low bound small field raw same regular
  exact startupCurrent_circle_recovery_algebra originalComplementKernel
    (originalMatrixKernel admissible (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent))
    (originalMatrixKernel admissible (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent)) field gauged inverse

end Grad.CartesianStartup
