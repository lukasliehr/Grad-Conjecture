import AKBL24SameOrbitContinuousFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.SourceCollarAngular Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Radial

 theorem startupPhysicalCoefficient_joint {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output) :
    Continuous (fun pair : ℝ × ClosedDisk => coefficientPhysicalValue coefficient pair.1 pair.2) := by
  apply continuous_tsum
    (fun cell : ℤ => ((cellExponential_smooth cell).continuous.comp continuous_fst).smul
      ((coefficientDerivative coefficient cell zeroDerivativeIndex).continuous.comp continuous_snd))
    (coordinate_norm_summable coefficient.val zeroDerivativeIndex)
  intro cell pair
  change ‖cellExponential cell pair.1 • coefficientDerivative coefficient cell zeroDerivativeIndex pair.2‖ ≤ _
  rw [norm_smul,cellExponential_norm,one_mul]
  exact coefficientDerivative_point_norm_le admissible coefficient cell zeroDerivativeIndex pair.2

 def startupPhysicalCoefficient_cmap {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output) (angle : ℝ) :
    C(ClosedDisk,OperatorValue input output) :=
  ⟨coefficientPhysicalValue coefficient angle,cMapCoefficient_continuous admissible coefficient angle⟩

 theorem startupPhysicalCoefficient_cmap_continuous {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output) :
    Continuous (startupPhysicalCoefficient_cmap admissible coefficient) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact startupPhysicalCoefficient_joint admissible coefficient

 def startupRawMatrix {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (raw : ℝ × Spatial → PhysicalValue input) (pair : ℝ × Spatial) : PhysicalValue output :=
  closedDiskLift (coefficientPhysicalValue (family 0) pair.1) pair.2 (raw pair)

 theorem startupRawMatrix_value {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (raw : ℝ × Spatial → PhysicalValue input) (angle : ℝ) (point : ClosedDisk) :
    startupRawMatrix family raw (angle,point.val) = coefficientPhysicalValue (family 0) angle point (raw (angle,point.val)) := by
  simp only [startupRawMatrix,closedDiskLift,dif_pos point.property]

/-- Full original matrix multiplication preserves the SAME continuous
circle realization, including its entire axial family and every input cell. -/
 theorem StartupOrbitContinuous.matrix {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    {raw : ℝ × Spatial → PhysicalValue input} (regular : StartupOrbitContinuous raw) :
    StartupOrbitContinuous (startupRawMatrix family raw) := by
  intro point positive inside
  obtain ⟨localized,continuousLocal,same⟩ := regular point positive inside
  let outputLocal := fun angle => cMapAction (startupPhysicalCoefficient_cmap admissible (family 0) angle) (localized angle)
  have continuousOutput : Continuous outputLocal :=
    ((cMapActionBilinear input output).continuous.comp
      (startupPhysicalCoefficient_cmap_continuous admissible (family 0))).clm_apply continuousLocal
  refine ⟨outputLocal,continuousOutput,?_⟩
  intro angle other normSame
  rw [startupRawMatrix_value]
  change coefficientPhysicalValue (family 0) angle other (localized angle other) = _
  rw [same angle other normSame]

end Grad.CartesianStartup
