import AKU27OriginalPolynomialLiftCore
import AKU5PolynomialAngularSectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.QuotientProjection Grad.ChartAxisLift
open Grad.NonlinearDivision Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear partialJetLinear_apply partialJet_coordinate_value)

theorem quadraticVectorJet_origin {dimension : ℕ} (data : Fin 3 → ComplexEuclidean dimension) :
    (quadraticVectorJet data).value closedOrigin = 0 := by
  simp [quadraticVectorJet_value,closedOrigin]

theorem quadraticVectorJet_partial_origin {dimension : ℕ}
    (data : Fin 3 → ComplexEuclidean dimension) (direction : Fin 2) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (quadraticVectorJet data)).value closedOrigin = 0 := by
  rw [quadraticVectorJet,Fin.sum_univ_three]
  change (partialJetLinear dimension direction (_ + _ + _)).value closedOrigin = 0
  rw [map_add,map_add,partialJetLinear_apply,partialJetLinear_apply,partialJetLinear_apply]
  simp [quadraticVectorMonomial,coordinatePairConstantLinear,closedJet_value_add,
    partialJet_coordinate_value,coordinateJet_value,closedOrigin]

theorem localizedFiniteJet_origin {dimension : ℕ} (field : ClosedJet dimension) :
    (localizedFiniteJet field).value closedOrigin = field.value closedOrigin := by
  rw [localizedFiniteJet_value,finiteLiftCutoff_one]
  · exact one_smul _ _
  · simp [closedOrigin]

theorem localizedFiniteJet_originPartial {dimension : ℕ} (field : ClosedJet dimension) (direction : Fin 2) :
    originPartial direction (localizedFiniteJet field) = originPartial direction field := by
  rw [originPartial_eq_closedDerivative,originPartial_eq_closedDerivative]
  exact localizedFiniteJet_axis_derivative field (fun _ => direction)

theorem originalFiniteLiftU_val (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (cell : ℤ) :
    (originalFiniteLiftU parameters length rho epsilon field low source).val cell =
      localizedFiniteJet ((originalU2Core parameters length rho epsilon field low source).val cell) := by
  rw [originalFiniteLiftU,localizedQuadraticVectorAxisCore_val,originalU2Core,quadraticVectorAxisCore_val]

theorem originalFiniteLiftS_val (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (cell : ℤ) :
    (originalFiniteLiftS parameters length rho epsilon field low source).val cell =
      localizedFiniteJet ((originalS2Core source).val cell +
        (originalS3Core parameters length rho epsilon field low source).val cell) := by
  change ((∑ index, fixedAxisJetCore (localizedFiniteJet (quadraticScalarJet (Pi.single index 1)))
    (originalScalarHessianAxis source index)).val cell +
    (localizedCubicScalarAxisCore (originalLiftS3Axis parameters length rho epsilon field low source)).val cell) = _
  rw [localizedCubicScalarAxisCore_val,originalS3Core,cubicScalarAxisCore_val]
  change _ = localizedFiniteJetLinear 1 (_ + _)
  rw [map_add]
  congr 1
  simp only [originalS2Core,quadraticAxisCore,Submodule.coe_sum,Finset.sum_apply,fixedAxisJetCore_val]
  change (∑ index, (originalScalarHessianAxis source index).val cell 0 •
    localizedFiniteJetLinear 1 (quadraticScalarJet (Pi.single index 1))) =
      localizedFiniteJetLinear 1 (∑ index, (originalScalarHessianAxis source index).val cell 0 •
        quadraticScalarJet (Pi.single index 1))
  rw [map_sum]
  simp only [map_smul]

theorem originalFiniteLiftU_zero_jets (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    traceZero (originalFiniteLiftU parameters length rho epsilon field low source) = 0 ∧
      ∀ direction, traceFirst direction (originalFiniteLiftU parameters length rho epsilon field low source) = 0 := by
  constructor
  · apply Subtype.ext
    funext cell
    rw [traceZero_val,originValue,originalFiniteLiftU_val]
    change (localizedFiniteJet _).value closedOrigin = 0
    rw [localizedFiniteJet_origin,originalU2Core,quadraticVectorAxisCore_val,quadraticVectorJet_origin]
  · intro direction
    apply Subtype.ext
    funext cell
    rw [traceFirst_val,originalFiniteLiftU_val,localizedFiniteJet_originPartial,originalU2Core,quadraticVectorAxisCore_val]
    exact quadraticVectorJet_partial_origin _ direction

theorem originalFiniteLiftS_zero_jets (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    traceZero (originalFiniteLiftS parameters length rho epsilon field low source) = 0 ∧
      ∀ direction, traceFirst direction (originalFiniteLiftS parameters length rho epsilon field low source) = 0 := by
  constructor
  · apply Subtype.ext
    funext cell
    rw [traceZero_val,originValue,originalFiniteLiftS_val]
    change (localizedFiniteJet _).value closedOrigin = 0
    rw [localizedFiniteJet_origin,originalS2Core_val,originalS3Core,cubicScalarAxisCore_val]
    apply PiLp.ext
    intro component
    have zeroComponent : component = 0 := Subsingleton.elim _ _
    subst component
    simp [closedJet_value_add,quadraticScalarJet_value,cubicScalarJet_value,closedOrigin]
  · intro direction
    apply Subtype.ext
    funext cell
    rw [traceFirst_val,originalFiniteLiftS_val,localizedFiniteJet_originPartial,originPartial_add,
      originalS2Core_val,originalS3Core,cubicScalarAxisCore_val]
    apply PiLp.ext
    intro component
    have zeroComponent : component = 0 := Subsingleton.elim _ _
    subst component
    change (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (quadraticScalarJet _)).value closedOrigin 0 +
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (cubicScalarJet _)).value closedOrigin 0 = 0
    simp [quadraticScalarJet_partial_value,cubicScalarJet_partial_value,closedOrigin]

theorem originalFiniteLift_outer_support (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (cell : ℤ) (point : ClosedDisk) (outside : 1/4 ≤ ‖point.val‖) :
    ((originalFiniteLiftU parameters length rho epsilon field low source).val cell).value point = 0 ∧
      ((originalFiniteLiftS parameters length rho epsilon field low source).val cell).value point = 0 := by
  rw [originalFiniteLiftU_val,originalFiniteLiftS_val]
  exact ⟨localizedFiniteJet_value_zero _ point outside,localizedFiniteJet_value_zero _ point outside⟩

theorem localizedFiniteJet_mean_zero {dimension : ℕ} (field : ClosedJet dimension)
    (meanFree : angularClosedJet 0 field = 0) : angularClosedJet 0 (localizedFiniteJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_factor 0 _ field (fun point => (finiteLiftCutoff point.val : ℂ))
    (radialCap_closedRadial (1/2) (by norm_num)) (fun point => by
      rw [localizedFiniteJet_value,Complex.coe_smul]),meanFree]
  simp only [closedJet_value_zero,ContinuousMap.zero_apply,smul_zero]

theorem originalFiniteLiftS_mean_zero (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    angularCore parameters 0 (originalFiniteLiftS parameters length rho epsilon field low source) = 0 := by
  apply Subtype.ext
  funext cell
  change angularClosedJet 0 ((originalFiniteLiftS parameters length rho epsilon field low source).val cell) = 0
  rw [originalFiniteLiftS_val]
  apply localizedFiniteJet_mean_zero
  rw [angularClosedJet_add,originalS2Core_val,originalS3Core,cubicScalarAxisCore_val,
    originalScalarSourceJet_mean_zero source flat cell,cubicScalarJet_mean_zero,add_zero]

end Grad.FinitePhysicalJetLift
