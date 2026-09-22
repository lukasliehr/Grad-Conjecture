import AED4ExactReferenceFormTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped Topology BigOperators
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularHighTilt Grad.AnnularSourceGraph

section Trace
variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)

/-- The physical trace changes by the actual endpoint radial power. -/
theorem highEnergyUnweight_trace (endpoint : Fin 2) (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive endpoint
      (highEnergyUnweight lower length positive bounded.le field) =
    (highPowerCurve lower highTiltExponent positive (radialEndpointRadius lower endpoint) : ℂ) •
      annularEnergyTrace lower length positive bounded lengthPositive endpoint field := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    (isClosed_eq
      ((annularEnergyTrace lower length positive bounded lengthPositive endpoint).continuous.comp
        (highEnergyUnweight lower length positive bounded.le).continuous)
      ((continuous_const (y := (highPowerCurve lower highTiltExponent positive (radialEndpointRadius lower endpoint) : ℂ))).smul
        (annularEnergyTrace lower length positive bounded lengthPositive endpoint).continuous)) _ field
  intro core
  change annularEnergyTrace lower length positive bounded lengthPositive endpoint
    (highEnergyUnweight lower length positive bounded.le (annularEnergyCoreInto lower length positive core)) =
    (highPowerCurve lower highTiltExponent positive (radialEndpointRadius lower endpoint) : ℂ) •
      annularEnergyTrace lower length positive bounded lengthPositive endpoint
        (annularEnergyCoreInto lower length positive core)
  rw [highEnergyUnweight_coreInto, annularEnergyTrace_core, annularEnergyTrace_core]
  apply lp.ext
  funext mode
  rw [lp.coeFn_smul, Pi.smul_apply, finiteAnnularTraceCore_apply, finiteAnnularTraceCore_apply,
    highPowerFiniteCore_apply, highPowerComplexCore_value]
  exact smul_comm _ _ _

theorem highEnergyUnweight_outerTrace (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive 1
      (highEnergyUnweight lower length positive bounded.le field) =
    annularEnergyTrace lower length positive bounded lengthPositive 1 field := by
  rw [highEnergyUnweight_trace]
  change (highPowerCurve lower highTiltExponent positive 1 : ℂ) • _ = _
  rw [highPower_outer lower highTiltExponent positive bounded.le, Complex.ofReal_one, one_smul]

theorem highEnergyUnweight_innerTrace (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive 0
      (highEnergyUnweight lower length positive bounded.le field) =
    ((lower ^ highTiltExponent : ℝ) : ℂ) • annularEnergyTrace lower length positive bounded lengthPositive 0 field := by
  rw [highEnergyUnweight_trace]
  change (highPowerCurve lower highTiltExponent positive lower : ℂ) • _ = _
  rw [highPowerCurve_physical lower highTiltExponent positive lower ⟨le_rfl, bounded.le⟩]

theorem highEnergyUnweight_innerZero
    (field : annularInnerZero lower length positive bounded lengthPositive) :
    highEnergyUnweight lower length positive bounded.le field.val ∈
      annularInnerZero lower length positive bounded lengthPositive := by
  change annularEnergyTrace lower length positive bounded lengthPositive 0
    (highEnergyUnweight lower length positive bounded.le field.val) = 0
  rw [highEnergyUnweight_trace]
  have zero : annularEnergyTrace lower length positive bounded lengthPositive 0 field.val = 0 := field.property
  rw [zero, smul_zero]

/-- The physical trace changes by the actual endpoint radial power. -/
theorem highEnergyWeight_trace (endpoint : Fin 2) (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive endpoint
      (highEnergyWeight lower length positive bounded.le field) =
    (highPowerCurve lower (-highTiltExponent) positive (radialEndpointRadius lower endpoint) : ℂ) •
      annularEnergyTrace lower length positive bounded lengthPositive endpoint field := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    (isClosed_eq
      ((annularEnergyTrace lower length positive bounded lengthPositive endpoint).continuous.comp
        (highEnergyWeight lower length positive bounded.le).continuous)
      ((continuous_const (y := (highPowerCurve lower (-highTiltExponent) positive (radialEndpointRadius lower endpoint) : ℂ))).smul
        (annularEnergyTrace lower length positive bounded lengthPositive endpoint).continuous)) _ field
  intro core
  change annularEnergyTrace lower length positive bounded lengthPositive endpoint
    (highEnergyWeight lower length positive bounded.le (annularEnergyCoreInto lower length positive core)) =
    (highPowerCurve lower (-highTiltExponent) positive (radialEndpointRadius lower endpoint) : ℂ) •
      annularEnergyTrace lower length positive bounded lengthPositive endpoint
        (annularEnergyCoreInto lower length positive core)
  rw [highEnergyWeight_coreInto, annularEnergyTrace_core, annularEnergyTrace_core]
  apply lp.ext
  funext mode
  rw [lp.coeFn_smul, Pi.smul_apply, finiteAnnularTraceCore_apply, finiteAnnularTraceCore_apply,
    highPowerFiniteCore_apply, highPowerComplexCore_value]
  exact smul_comm _ _ _

theorem highEnergyWeight_outerTrace (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive 1
      (highEnergyWeight lower length positive bounded.le field) =
    annularEnergyTrace lower length positive bounded lengthPositive 1 field := by
  rw [highEnergyWeight_trace]
  change (highPowerCurve lower (-highTiltExponent) positive 1 : ℂ) • _ = _
  rw [highPower_outer lower (-highTiltExponent) positive bounded.le, Complex.ofReal_one, one_smul]

theorem highEnergyWeight_innerTrace (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive 0
      (highEnergyWeight lower length positive bounded.le field) =
    ((lower ^ (-highTiltExponent) : ℝ) : ℂ) • annularEnergyTrace lower length positive bounded lengthPositive 0 field := by
  rw [highEnergyWeight_trace]
  change (highPowerCurve lower (-highTiltExponent) positive lower : ℂ) • _ = _
  rw [highPowerCurve_physical lower (-highTiltExponent) positive lower ⟨le_rfl, bounded.le⟩]

theorem highEnergyWeight_innerZero
    (field : annularInnerZero lower length positive bounded lengthPositive) :
    highEnergyWeight lower length positive bounded.le field.val ∈
      annularInnerZero lower length positive bounded lengthPositive := by
  change annularEnergyTrace lower length positive bounded lengthPositive 0
    (highEnergyWeight lower length positive bounded.le field.val) = 0
  rw [highEnergyWeight_trace]
  have zero : annularEnergyTrace lower length positive bounded lengthPositive 0 field.val = 0 := field.property
  rw [zero, smul_zero]

end Trace
end Grad.AnnularTiltedReference
