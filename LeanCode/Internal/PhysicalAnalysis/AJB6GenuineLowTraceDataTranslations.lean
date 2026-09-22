import AJB5SameLowGeneratorConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference
open Grad.CircularHighRegularity Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Character translation on the original independently prescribed incoming datum. -/
def lowBoundaryTranslation (tau : OrbitParameter) : LowEnergyBoundary →L[ℂ] LowEnergyBoundary :=
  complexLpTwoMap (fun index : LowAnnularIndex =>
    orbitCharacter tau index.2.val • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) 1 (by norm_num)
    (fun index field => by
      change ‖orbitCharacter tau index.2.val • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, orbitCharacter_norm])

theorem lowBoundaryTranslation_apply (tau : OrbitParameter) (field : LowEnergyBoundary) (index : LowAnnularIndex) :
    lowBoundaryTranslation tau field index = orbitCharacter tau index.2.val • field index := rfl

theorem lowBulkTranslation_norm (lower : ℝ) (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    ‖lowBulkTranslation lower tau field‖ = ‖field‖ := by
  have point (index : LowAnnularIndex) : ‖lowBulkTranslation lower tau field index‖ = ‖field index‖ := by
    rw [lowBulkTranslation_apply, norm_smul, orbitCharacter_norm, one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun index => (point index).le))
    (lp.norm_mono (by norm_num) (fun index => (point index).ge))

def lowBulkTranslationEquivalence (lower : ℝ) (tau : OrbitParameter) : LowEnergyBulk lower ≃ₗᵢ[ℂ] LowEnergyBulk lower where
  toLinearEquiv :=
    { (lowBulkTranslation lower tau).toLinearMap with
      invFun := lowBulkTranslation lower (-tau)
      left_inv := by
        intro field
        change lowBulkTranslation lower (-tau) (lowBulkTranslation lower tau field) = field
        simpa only [neg_neg] using lowBulkTranslation_inverse lower (-tau) field
      right_inv := lowBulkTranslation_inverse lower tau }
  norm_map' := lowBulkTranslation_norm lower tau

theorem lowBoundaryTranslation_inverse (tau : OrbitParameter) (field : LowEnergyBoundary) :
    lowBoundaryTranslation tau (lowBoundaryTranslation (-tau) field) = field := by
  apply lp.ext
  funext index
  rw [lowBoundaryTranslation_apply, lowBoundaryTranslation_apply, smul_smul, orbitCharacter_inverse, one_smul]

theorem lowBoundaryTranslation_norm (tau : OrbitParameter) (field : LowEnergyBoundary) :
    ‖lowBoundaryTranslation tau field‖ = ‖field‖ := by
  have point (index : LowAnnularIndex) : ‖lowBoundaryTranslation tau field index‖ = ‖field index‖ := by
    rw [lowBoundaryTranslation_apply, norm_smul, orbitCharacter_norm, one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun index => (point index).le))
    (lp.norm_mono (by norm_num) (fun index => (point index).ge))

def lowBoundaryTranslationEquivalence (tau : OrbitParameter) : LowEnergyBoundary ≃ₗᵢ[ℂ] LowEnergyBoundary where
  toLinearEquiv :=
    { (lowBoundaryTranslation tau).toLinearMap with
      invFun := lowBoundaryTranslation (-tau)
      left_inv := by
        intro field
        change lowBoundaryTranslation (-tau) (lowBoundaryTranslation tau field) = field
        simpa only [neg_neg] using lowBoundaryTranslation_inverse (-tau) field
      right_inv := lowBoundaryTranslation_inverse tau }
  norm_map' := lowBoundaryTranslation_norm tau

/-- The exact BE18 Hilbert datum, with its bulk/incoming normalization unchanged. -/
def lowDataTranslationEquivalence (lower : ℝ) (tau : OrbitParameter) : LowEnergyData lower ≃ₗᵢ[ℂ] LowEnergyData lower :=
  hilbertProductEquivalence (lowBulkTranslationEquivalence lower tau) (lowBoundaryTranslationEquivalence tau)

theorem lowDataTranslation_apply (lower : ℝ) (tau : OrbitParameter) (data : LowEnergyData lower) :
    lowDataTranslationEquivalence lower tau data =
      WithLp.toLp 2 (lowBulkTranslation lower tau data.ofLp.1, lowBoundaryTranslation tau data.ofLp.2) := rfl

theorem lowDataTranslation_symm (lower : ℝ) (tau : OrbitParameter) (data : LowEnergyData lower) :
    (lowDataTranslationEquivalence lower tau).symm data = lowDataTranslationEquivalence lower (-tau) data := rfl

/-- Translation of the genuine continuous radial representative is forced by
its L2 bulk; no endpoint is introduced as a free graph coordinate. -/
theorem lowEnergySection_translation (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowEnergySection lower length positive bounded (lowTranslation lower length positive tau field) index =
      orbitCharacter tau index.2.val • lowEnergySection lower length positive bounded field index := by
  apply radialSectionL2_injective lower positive bounded
  rw [radialSectionL2_complex_smul, lowEnergySection_bulk, lowEnergySection_bulk]
  change collarScalar 1 lower (lowStorageInverse lower positive)
    (orbitCharacter tau index.2.val • field.val 0 index) =
      orbitCharacter tau index.2.val • collarScalar 1 lower (lowStorageInverse lower positive) (field.val 0 index)
  exact map_smul _ _ _

theorem lowEnergyEndpoint_translation (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowEnergyEndpoint lower length positive bounded endpoint (lowTranslation lower length positive tau field) index =
      orbitCharacter tau index.2.val • lowEnergyEndpoint lower length positive bounded endpoint field index := by
  unfold lowEnergyEndpoint
  rw [lowEnergySection_translation]
  rfl

/-- Actual ADY incoming trace covariance, with its original r^-7/4 mu^-1/2 factor. -/
theorem lowIncomingTrace_translation (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) :
    lowIncomingTrace lower length positive bounded (lowTranslation lower length positive tau field) =
      lowBoundaryTranslation tau (lowIncomingTrace lower length positive bounded field) := by
  apply lp.ext
  funext index
  rw [lowIncomingTrace_apply, lowBoundaryTranslation_apply, lowIncomingTrace_apply, lowEnergyEndpoint_translation]
  exact smul_comm _ _ _

end Grad.AnnularLowOrbit
