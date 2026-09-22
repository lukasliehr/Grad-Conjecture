import GQC4FirstDerivativeGraph

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem coefficientHasFirstDerivative_single (L sigma gamma ell : ℝ) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) :
    CoefficientHasFirstDerivative (singleJetCoefficient L sigma gamma ell 1 cell field) other := by
  intro point inside
  have value : coefficientDerivative (singleJetCoefficient L sigma gamma ell 1 cell field)
      other (zeroDerivativeIndexAt 1) = if other = cell then field.value else 0 := by
    apply ContinuousMap.ext
    intro closedPoint
    rw [singleJetCoefficient_derivative]
    change (if other = cell then smoothOperatorDerivative field (0, 0) closedPoint else 0) = _
    rw [smoothOperator_zero]
    split <;> rfl
  rw [value, closedLift_value _ point inside]
  change HasFDerivAt (closedDiskLift _)
    (planarDerivative
      (coefficientDerivative (singleJetCoefficient L sigma gamma ell 1 cell field) other (firstCoordinateIndex 0) _)
      (coefficientDerivative (singleJetCoefficient L sigma gamma ell 1 cell field) other (firstCoordinateIndex 1) _)) point
  rw [singleJetCoefficient_derivative, singleJetCoefficient_derivative]
  by_cases same : other = cell
  · simp only [if_pos same]
    have derivative := smoothOperator_first field point inside
    rw [closedLift_value _ point inside, closedLift_value _ point inside] at derivative
    exact derivative
  · simp only [if_neg same]
    have zero : planarDerivative (0 : OperatorValue input output) 0 = 0 := by
      apply ContinuousLinearMap.ext
      intro direction
      simp only [planarDerivative_apply, smul_zero, add_zero, zero_apply]
    rw [zero]
    change HasFDerivAt (closedDiskLift (fun _ => 0)) 0 point
    rw [closedLift_zero]
    exact hasFDerivAt_const (0 : OperatorValue input output) point

theorem spanSubtype_property {Source Target : Type*}
    [AddCommGroup Source] [Module ℂ Source] [AddCommGroup Target] [Module ℂ Target]
    (generators : Set Source) (mapping : Submodule.span ℂ generators →ₗ[ℂ] Target)
    (property : Target → Prop) (zero : property 0)
    (add : ∀ first second, property first → property second → property (first + second))
    (smul : ∀ (scalar : ℂ) value, property value → property (scalar • value))
    (onGenerators : ∀ generator membership, property (mapping ⟨generator, Submodule.subset_span membership⟩))
    (core : Submodule.span ℂ generators) : property (mapping core) := by
  have membership := core.property
  generalize valueEq : core.val = value at membership
  have proof : ∀ membership : value ∈ Submodule.span ℂ generators,
      property (mapping ⟨value, membership⟩) := by
    intro membership
    refine Submodule.span_induction
      (p := fun value membership => property (mapping ⟨value, membership⟩))
      ?_ ?_ ?_ ?_ membership
    · exact onGenerators
    · change property (mapping 0)
      rw [map_zero]
      exact zero
    · intro first second firstIn secondIn firstCompatible secondCompatible
      change property (mapping (⟨first, firstIn⟩ + ⟨second, secondIn⟩))
      rw [map_add]
      exact add _ _ firstCompatible secondCompatible
    · intro scalar value member compatible
      change property (mapping (scalar • ⟨value, member⟩))
      rw [map_smul]
      exact smul _ _ compatible
  have coreEq : core = ⟨value, membership⟩ := Subtype.ext valueEq
  rw [coreEq]
  exact proof membership

theorem coefficientHasFirstDerivative_core (L sigma gamma ell : ℝ) (input output : ℕ) (cell : ℤ)
    (core : smoothCore L sigma gamma ell 1 input output) :
    CoefficientHasFirstDerivative (coreInclusion L sigma gamma ell 1 input output core) cell := by
  apply spanSubtype_property _ (coreInclusion L sigma gamma ell 1 input output)
    (fun coefficient => CoefficientHasFirstDerivative coefficient cell)
    (coefficientHasFirstDerivative_zero cell)
    (fun _ _ first second => CoefficientHasFirstDerivative.add first second)
    (fun scalar _ compatible => CoefficientHasFirstDerivative.smul compatible scalar) _ core
  intro generator membership
  rcases membership with ⟨⟨other, field⟩, rfl⟩
  exact coefficientHasFirstDerivative_single L sigma gamma ell other cell field

/-- The first Cartesian derivative of every actual C¹ coefficient is
its stored two-coordinate derivative. This is proved through the genuine
closed-jet core, not assumed of a completed derivative array. -/
theorem coefficientHasFirstDerivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 1 input output) (cell : ℤ) :
    CoefficientHasFirstDerivative coefficient cell :=
  isClosed_property (finiteCellCore_dense 1 input output)
    (coefficientHasFirstDerivative_isClosed admissible input output cell)
    (coefficientHasFirstDerivative_core L sigma gamma ell input output cell) coefficient

end Grad.GaugeCoefficients.Physical.Compensated
