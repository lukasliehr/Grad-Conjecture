import AKDP12ActualMatrixBaseAndInputBounds
import AKCX30SameOriginalSourceAllOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.CartesianCoreRecovery Grad.CellWeights
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

/-- Signed moments of an original core before any spatial dilation. -/
def startupOriginalSignedFamily {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (L ell : ℝ) : StartupSignedFamily dimension L ell where
  field := (originalSourceMoments parameters core).field
  moment power := (originalSourceMoments parameters (originalSignedAxialCore parameters core L ell power)).field
  same power := by
    filter_upwards [originalSourceMoments_same parameters (originalSignedAxialCore parameters core L ell power),
      originalSourceMoments_same parameters core,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
      with point moment field inside
    intro cell
    rw [moment cell,field cell,originalSignedAxialCore_cell parameters core L ell power cell
      ⟨point,openDiskMembershipClosed point inside⟩]
    exact smul_comm _ _ _

/-- Every original core has all spatial graphs with all natural reserves,
constructed from its genuine signed time derivatives. -/
theorem startupOriginalSignedFamily_allSpatial {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) {L ell : ℝ} (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (grade : ℕ) : (startupOriginalSignedFamily parameters core L ell).HasSpatialGrade grade := by
  apply StartupSignedFamily.hasSpatialGrade_of_zero _ lengthNonzero scaleNonzero
  intro power
  exact ⟨originalSourceSpatialGraph parameters (originalSignedAxialCore parameters core L ell power) grade,
    originalSourceSpatialGraph_base parameters (originalSignedAxialCore parameters core L ell power) grade⟩

theorem startupOriginal_reservedGraph {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) {L ell : ℝ} (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (grade weight : ℕ) :
    ∃ graph : GraphGrade dimension grade weight openUnitDisk,
      base dimension grade openUnitDisk (fun _ => weight) graph = (originalSourceMoments parameters core).field := by
  obtain ⟨graph,same⟩ := startupOriginalSignedFamily_allSpatial parameters core lengthNonzero scaleNonzero grade 0 weight
  rw [StartupSignedFamily.zero] at same
  exact ⟨graph,same⟩

/-- Actual original matrix action constructs its own image core, with the
same weighted field on the original disk and original analytic width. -/
theorem startupOriginalMatrix_core_exists {input output : ℕ} (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (coefficients : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (coherent : FamilyCoherent coefficients) (core : ACore parameters input) :
    ∃ image : ACore parameters output,
      (originalSourceMoments parameters image).field = originalMatrixKernel admissible coefficients coherent
        (originalSourceMoments parameters core).field := by
  let source := startupOriginalSignedFamily parameters core L ell
  let mapped := source.matrix admissible coefficients coherent
  have regular (grade : ℕ) : mapped.HasSpatialGrade grade :=
    (startupOriginalSignedFamily_allSpatial parameters core lengthNonzero scaleNonzero grade).matrix
      admissible coefficients coherent lengthNonzero scaleNonzero
  let graphs := fun grade => (regular grade 0 grade).choose
  have same (grade : ℕ) : base output grade openUnitDisk (fun _ => grade) (graphs grade) = mapped.field := by
    have result := (regular grade 0 grade).choose_spec
    exact result.trans (StartupSignedFamily.zero mapped)
  obtain ⟨image,identified,_⟩ := allDiagonalGraphs_sameOriginalCore parameters mapped.field graphs same
  exact ⟨image,identified⟩

end Grad.CartesianStartup
