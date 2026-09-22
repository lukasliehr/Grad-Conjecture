import AKU50ActualToroidalAxisRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.ChartAxisLift
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.Cor18 Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.PhysicalCoordinates

theorem localizedFiniteJet_mode_zero {dimension : ℕ} (field : ClosedJet dimension) (mode : ℤ)
    (modeZero : angularClosedJet mode field = 0) : angularClosedJet mode (localizedFiniteJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_factor mode _ field (fun point => (finiteLiftCutoff point.val : ℂ))
    (radialCap_closedRadial (1/2) (by norm_num)) (fun point => by
      rw [localizedFiniteJet_value,Complex.coe_smul]),modeZero]
  simp only [closedJet_value_zero,ContinuousMap.zero_apply,smul_zero]

theorem quadraticVectorJet_odd_mode_zero {dimension : ℕ} (data : Fin 3 → ComplexEuclidean dimension)
    (mode : ℤ) (oddMode : mode = 1 ∨ mode = -1) : angularClosedJet mode (quadraticVectorJet data) = 0 := by
  rw [quadraticVectorJet,Fin.sum_univ_three]
  simp only [angularClosedJet_add,quadraticVectorMonomial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  change angularClosedJet mode (coordinateJet 0 (coordinateJet 0 (constantValueJet (data 0)))) +
    angularClosedJet mode (coordinateJet 0 (coordinateJet 1 (constantValueJet (data 1)))) +
    angularClosedJet mode (coordinateJet 1 (coordinateJet 1 (constantValueJet (data 2)))) = 0
  rw [quadraticMonomial_angular_odd _ _ _ mode oddMode,quadraticMonomial_angular_odd _ _ _ mode oddMode,
    quadraticMonomial_angular_odd _ _ _ mode oddMode,add_zero,add_zero]

theorem localizedQuadraticVectorAxisCore_odd_modes {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) :
    ModesVanish {1,-1} (localizedQuadraticVectorAxisCore data) := by
  apply modesVanish_of_cell
  intro mode member cell
  rw [localizedQuadraticVectorAxisCore_val]
  exact localizedFiniteJet_mode_zero _ mode (quadraticVectorJet_odd_mode_zero _ mode member)

theorem originalFiniteLiftU_storage_poloidal_zero (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    poloidalCorrection parameters seed inside
      (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)) = 0 := by
  rw [poloidalCorrection_apply]
  have modes : ModesVanish {1,-1}
      (planarPartCore parameters (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source))) :=
    modesVanish_valueMapCore _ (modesVanish_valueMapCore _ (localizedQuadraticVectorAxisCore_odd_modes _))
  have transposed : ModesVanish {1,-1} (seedTransposeCore parameters seed inside
      (planarPartCore parameters (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)))) :=
    modesVanish_smoothMultiplier _ _ modes
  rw [tangentialCore_eq_zero transposed,map_zero,map_zero]

theorem derivativeDotCore_mean_zero_of_odd_modes {parameters : PhaseParameters}
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (field : ACore parameters 2)
    (modes : ModesVanish {1,-1} field) : angularCore parameters 0 (derivativeDotCore parameters seed inside field) = 0 := by
  have zeroSub : ({0} : Set ℤ) ⊆ {mode | mode - 1 ∈ ({1,-1} : Set ℤ) ∧ mode + 1 ∈ ({1,-1} : Set ℤ)} := by
    intro mode member
    have only : mode = 0 := member
    subst mode
    norm_num
  have dot : ModesVanish {0} (derivativeDotCore parameters seed inside field) := by
    unfold derivativeDotCore
    simp only [LinearMap.add_apply,LinearMap.comp_apply]
    exact modesVanish_add
      (modesVanish_mono zeroSub (modesVanish_coordinateCore 0 (modesVanish_smoothMultiplier _ _ modes)))
      (modesVanish_mono zeroSub (modesVanish_coordinateCore 1 (modesVanish_smoothMultiplier _ _ modes)))
  exact dot 0 (by simp)

theorem valueMapCore_localizedQuadratic {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters input) :
    valueMapCore parameters mapping (localizedQuadraticVectorAxisCore data) =
      localizedQuadraticVectorAxisCore (fun index => axisValueMap mapping (data index)) := by
  apply acore_ext
  intro cell point
  rw [valueMapCore_value,localizedQuadraticVectorAxisCore_val,localizedQuadraticVectorAxisCore_val,
    localizedFiniteJet_value,localizedFiniteJet_value,quadraticVectorJet_value,quadraticVectorJet_value]
  have realScalar (a : ℝ) (v : ComplexEuclidean input) : mapping (a • v) = a • mapping v :=
    (mapping.restrictScalars ℝ).map_smul a v
  simp only [axisValueMap_val,realScalar,map_add]

theorem originalFiniteLiftU_toroidal_core (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    componentCore 3 1 (originalFiniteLiftU parameters length rho epsilon field low source) =
      localizedQuadraticVectorAxisCore (originalC2Axis length source) := by
  change valueMapCore parameters (componentValue 3 1) (localizedQuadraticVectorAxisCore _) = _
  rw [valueMapCore_localizedQuadratic]
  congr 1
  funext index
  exact originalLiftPhysicalUAxis_toroidal parameters length rho epsilon field vanishes low source index

theorem originalFiniteLiftU_toroidal_mean (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    angularCore parameters 0 (componentCore 3 1 (originalFiniteLiftU parameters length rho epsilon field low source)) = 0 := by
  rw [originalFiniteLiftU_toroidal_core parameters length rho epsilon field vanishes low]
  apply Subtype.ext
  funext cell
  change angularClosedJet 0 ((localizedQuadraticVectorAxisCore (originalC2Axis length source)).val cell) = 0
  rw [localizedQuadraticVectorAxisCore_val]
  apply localizedFiniteJet_mean_zero
  have same : quadraticVectorJet (fun index => (originalC2Axis length source index).val cell) =
      (originalC2Core length source).val cell := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    apply PiLp.ext
    intro component
    have only : component = 0 := Subsingleton.elim _ _
    subst component
    rw [quadraticVectorJet_value,originalC2Core_val,quadraticScalarJet_value]
    simp only [PiLp.add_apply,PiLp.smul_apply,originalC2Axis_val,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_mul]
  rw [same]
  exact congrArg (fun core : ACore parameters 1 => core.val cell) (originalC2Core_mean_zero length source)

theorem originalFiniteLiftU_storage_toroidal_zero (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    toroidalCorrection parameters seed inside
      (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)) = 0 := by
  have modes : ModesVanish {1,-1}
      (planarPartCore parameters (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source))) :=
    modesVanish_valueMapCore _ (modesVanish_valueMapCore _ (localizedQuadraticVectorAxisCore_odd_modes _))
  have toroidal : toroidalPartCore parameters
      (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)) =
      componentCore 3 1 (originalFiniteLiftU parameters length rho epsilon field low source) := by
    apply acore_ext
    intro cell point
    change (valueMapJet toroidalPartMap ((toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)).val cell)).value point = _
    rw [valueMapJet_value,toPhysicalCore_value]
    change _ = (valueMapJet (componentValue 3 1) ((originalFiniteLiftU parameters length rho epsilon field low source).val cell)).value point
    rw [valueMapJet_value]
    apply PiLp.ext
    intro coordinate
    have only : coordinate = 0 := Subsingleton.elim _ _
    subst coordinate
    simp [toroidalPartMap,toPhysicalValue,componentValue_apply]
  rw [toroidalCorrection_apply,map_add,map_smul,toroidal,
    originalFiniteLiftU_toroidal_mean parameters length rho epsilon field vanishes low,
    derivativeDotCore_mean_zero_of_odd_modes seed inside _ modes,smul_zero,add_zero,map_zero]

end Grad.FinitePhysicalJetLift
