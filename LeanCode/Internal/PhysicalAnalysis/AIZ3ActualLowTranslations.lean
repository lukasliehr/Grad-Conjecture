import AIZ2ActualFluxTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCoupledOrbit
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularKernelOrbit
open Grad.AnnularLowEnergy Grad.CircularHighRegularity Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower length : ℝ) (positive : 0 < lower)

def lowBulkTranslation (tau : OrbitParameter) : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  complexLpTwoMap (fun index : LowAnnularIndex =>
    orbitCharacter tau index.2.val • ContinuousLinearMap.id ℂ (CollarL2 (ComplexEuclidean 1) lower))
    1 (by norm_num) (by
      intro index field
      change ‖orbitCharacter tau index.2.val • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, orbitCharacter_norm])

theorem lowBulkTranslation_apply (tau : OrbitParameter) (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    lowBulkTranslation lower tau field index = orbitCharacter tau index.2.val • field index := rfl

def lowTranslationAmbient (tau : OrbitParameter) (field : LowEnergyAmbient lower) : LowEnergyAmbient lower :=
  WithLp.toLp 2 (fun coordinate => lowBulkTranslation lower tau (field coordinate))

theorem lowTranslation_mem (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) :
    lowTranslationAmbient lower tau field.val ∈ lowEnergyGraph lower length positive := by
  intro index
  change CollarWeakDerivative lower
    (collarScalar 1 lower (lowStorageInverse lower positive) (orbitCharacter tau index.2.val • field.val 0 index))
    (collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
      (collarScalar 1 lower (lowStorageInverse lower positive) (orbitCharacter tau index.2.val • field.val 1 index)))
  rw [map_smul, map_smul, map_smul]
  exact collarWeakDerivative_complex_smul lower (orbitCharacter tau index.2.val) _ _ (field.property index)

/-- The actual original rho-weighted Y graph is preserved, with both stored
coordinates translated by the same radius-independent Fourier character. -/
def lowTranslationLinear (tau : OrbitParameter) :
    lowEnergyGraph lower length positive →ₗ[ℂ] lowEnergyGraph lower length positive where
  toFun field := ⟨lowTranslationAmbient lower tau field.val, lowTranslation_mem lower length positive tau field⟩
  map_add' first second := by
    apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    exact map_add (lowBulkTranslation lower tau) (first.val coordinate) (second.val coordinate)
  map_smul' scalar field := by
    apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    exact map_smul (lowBulkTranslation lower tau) scalar (field.val coordinate)

theorem lowTranslationLinear_apply (tau : OrbitParameter) (field : lowEnergyGraph lower length positive)
    (coordinate : Fin 2) (index : LowAnnularIndex) :
    (lowTranslationLinear lower length positive tau field).val coordinate index =
      orbitCharacter tau index.2.val • field.val coordinate index := rfl

theorem lowTranslationLinear_norm (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) :
    ‖lowTranslationLinear lower length positive tau field‖ = ‖field‖ := by
  have rowNorm (coordinate : Fin 2) :
      ‖(lowTranslationLinear lower length positive tau field).val coordinate‖ = ‖field.val coordinate‖ := by
    have point (index : LowAnnularIndex) :
        ‖(lowTranslationLinear lower length positive tau field).val coordinate index‖ = ‖field.val coordinate index‖ := by
      rw [lowTranslationLinear_apply, norm_smul, orbitCharacter_norm, one_mul]
    exact le_antisymm (lp.norm_mono (by norm_num) (fun index => (point index).le))
      (lp.norm_mono (by norm_num) (fun index => (point index).ge))
  have first := lowEnergyGraph_norm_sq lower length positive (lowTranslationLinear lower length positive tau field)
  have second := lowEnergyGraph_norm_sq lower length positive field
  rw [rowNorm 0, rowNorm 1] at first
  nlinarith [norm_nonneg field, norm_nonneg (lowTranslationLinear lower length positive tau field)]

def lowTranslation (tau : OrbitParameter) :
    lowEnergyGraph lower length positive →L[ℂ] lowEnergyGraph lower length positive :=
  (lowTranslationLinear lower length positive tau).mkContinuous 1
    (fun field => by rw [lowTranslationLinear_norm, one_mul])

theorem lowTranslation_apply (tau : OrbitParameter) (field : lowEnergyGraph lower length positive)
    (coordinate : Fin 2) (index : LowAnnularIndex) :
    (lowTranslation lower length positive tau field).val coordinate index =
      orbitCharacter tau index.2.val • field.val coordinate index := rfl

theorem lowTranslation_add (tau sigma : OrbitParameter) (field : lowEnergyGraph lower length positive) :
    lowTranslation lower length positive (tau + sigma) field =
      lowTranslation lower length positive tau (lowTranslation lower length positive sigma field) := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  apply lp.ext
  funext index
  rw [lowTranslation_apply, lowTranslation_apply, lowTranslation_apply, smul_smul, orbitCharacter_add]

theorem lowTranslation_inverse (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) :
    lowTranslation lower length positive tau (lowTranslation lower length positive (-tau) field) = field := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  apply lp.ext
  funext index
  rw [lowTranslation_apply, lowTranslation_apply, smul_smul, orbitCharacter_inverse, one_smul]

def lowTranslationEquivalence (tau : OrbitParameter) :
    lowEnergyGraph lower length positive ≃ₗᵢ[ℂ] lowEnergyGraph lower length positive where
  toLinearEquiv :=
    { (lowTranslation lower length positive tau).toLinearMap with
      invFun := lowTranslation lower length positive (-tau)
      left_inv := by
        intro field
        change lowTranslation lower length positive (-tau) (lowTranslation lower length positive tau field) = field
        simpa only [neg_neg] using lowTranslation_inverse lower length positive (-tau) field
      right_inv := lowTranslation_inverse lower length positive tau }
  norm_map' := lowTranslationLinear_norm lower length positive tau

end Grad.AnnularCoupledOrbit
