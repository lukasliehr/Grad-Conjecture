import AKU63LiteralLowerSourceJets
import AKN16OriginalFlatSourcePrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.ExhaustionSourceAllocation Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear partialJetLinear_apply)

theorem physicalCartesianForceComponent_traceZero {parameters : PhaseParameters}
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) (direction : Fin 2) :
    traceZero (physicalCartesianForceComponent direction field vector scalar) = traceFirst direction scalar := by
  simp [physicalCartesianForceComponent,rotationCore,map_add,map_sub,dot_coordinate_second,traceZero_coordinateCore]
  rfl

theorem originalFiniteLift_derivative_force_zero (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    traceZero (cartesianSourceVector
      (quotientRowsDerivative parameters length 1 ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
        ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
          originalFiniteLiftS parameters length rho epsilon field low source)])) = 0 := by
  rw [quotientRowsDerivative_etaZero_cartesian]
  apply traceZero_vectorTuple_zero
  all_goals rw [physicalCartesianForceComponent_traceZero,
    (originalFiniteLiftS_zero_jets parameters length rho epsilon field low source).2]

theorem originalFiniteLift_derivative_mean_zero (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (component : Fin 4) (meanComponent : component = 2 ∨ component = 3) :
    traceZero ((quotientRowsDerivative parameters length 1
      ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
      ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
        originalFiniteLiftS parameters length rho epsilon field low source)]) component) = 0 := by
  rw [quotientRowsDerivative_etaZero]
  rcases meanComponent with rfl | rfl
  all_goals exact traceZero_removeAngular _

theorem traceZero_of_angular_zero {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (mean : angularCore parameters 0 field = 0) : traceZero field = 0 := by
  apply Subtype.ext
  funext cell
  have same := congrArg (fun core : ACore parameters dimension => originValue (core.val cell)) mean
  change originValue (angularClosedJet 0 (field.val cell)) = 0 at same
  rwa [angularJet_zero_originValue] at same

theorem vanishingJets_two_of_traces {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (zero : traceZero field = 0)
    (first : ∀ direction, traceFirst direction field = 0) (cell : ℤ) :
    VanishingJets 2 (field.val cell) := by
  intro order smaller word
  have origin : sourceOrigin = originPoint := Subtype.ext rfl
  rw [origin]
  have alternatives : order = 0 ∨ order = 1 := by omega
  rcases alternatives with rfl | rfl
  · have same := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters dimension => axis.val cell) zero
    rw [Subsingleton.elim word emptyCartesianWord,closedDerivative_zero_order]
    exact same
  · have same := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters dimension => axis.val cell) (first (word 0))
    change originPartial (word 0) (field.val cell) = 0 at same
    rw [originPartial_eq_closedDerivative] at same
    have words : (fun _ : Fin 1 => word 0) = word := by funext index; congr 1; exact Subsingleton.elim _ _
    simpa only [words] using same

theorem vanishingJets_three_of_traces {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (zero : traceZero field = 0)
    (first : ∀ direction, traceFirst direction field = 0) (second : secondTaylorAxis field = 0) (cell : ℤ) :
    VanishingJets 3 (field.val cell) := by
  intro order smaller word
  by_cases low : order < 2
  · exact vanishingJets_two_of_traces field zero first cell order low word
  · have only : order = 2 := by omega
    subst order
    have same := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters dimension => axis.val cell)
      (secondAxisTrace_zero_of_secondTaylor_zero field second (word 0) (word 1))
    change (partialJetLinear dimension (word 0) (partialJetLinear dimension (word 1) (field.val cell))).value closedOrigin = 0 at same
    simp only [partialJetLinear_apply] at same
    rw [doublePartial_eq_closedDerivative] at same
    have words : ![word 0,word 1] = word := by funext index; fin_cases index <;> rfl
    have origin : sourceOrigin = closedOrigin := Subtype.ext rfl
    rw [origin]
    simpa only [words] using same

/-- The residual uses the literal original derivative, retaining every source
cell and component; it is not replaced by its finite Taylor polynomial. -/
def originalFiniteLiftResidual (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : SmoothQuotient parameters := source -
      quotientRowsDerivative parameters length 1 ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
        ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
          originalFiniteLiftS parameters length rho epsilon field low source)]

theorem residual_higherVanishing_of_traces {parameters : PhaseParameters}
    (source output : SmoothQuotient parameters) (flat : IsFlat source)
    (forceZero : traceZero (cartesianSourceVector output) = 0)
    (forceFirst : ∀ direction, traceFirst direction (cartesianSourceVector output) = traceFirst direction (cartesianSourceVector source))
    (forceSecond : secondTaylorAxis (cartesianSourceVector output) = secondTaylorAxis (cartesianSourceVector source))
    (gZero : traceZero (output 2) = 0)
    (gFirst : ∀ direction, traceFirst direction (output 2) = traceFirst direction (source 2))
    (hZero : traceZero (output 3) = 0)
    (hFirst : ∀ direction, traceFirst direction (output 3) = 0)
    (hSecond : secondTaylorAxis (output 3) = secondTaylorAxis (source 3)) :
    SourceHigherVanishing (source-output) := by
  have cartesian := (isFlat_iff_cartesian source).mp flat
  have planar : cartesianSourceVector (source-output) = cartesianSourceVector source-cartesianSourceVector output :=
    cartesianSourceLinear.map_sub _ _
  refine ⟨?_,?_,?_⟩
  · intro cell
    rw [planar]
    apply vanishingJets_three_of_traces
    · rw [map_sub,cartesian.2.1,forceZero,sub_self]
    · intro direction
      rw [map_sub,forceFirst,sub_self]
    · rw [secondTaylorAxis_sub,forceSecond,sub_self]
  · intro cell
    change VanishingJets 2 ((source 2-output 2).val cell)
    apply vanishingJets_two_of_traces
    · rw [map_sub,traceZero_of_angular_zero _ cartesian.2.2.2.1,gZero,sub_self]
    · intro direction
      rw [map_sub,gFirst,sub_self]
  · intro cell
    change VanishingJets 3 ((source 3-output 3).val cell)
    apply vanishingJets_three_of_traces
    · rw [map_sub,traceZero_of_angular_zero _ cartesian.2.2.2.2.1,hZero,sub_self]
    · intro direction
      rw [map_sub,cartesian.2.2.2.2.2 direction,hFirst,sub_self]
    · rw [secondTaylorAxis_sub,hSecond,sub_self]

/-- Every required original EX vanishing jet follows from the actual current
row identities. This statement does not yet claim the domain gauge conditions. -/
theorem originalFiniteLiftResidual_higherVanishing (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (positive : 0 < length) (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    SourceHigherVanishing (originalFiniteLiftResidual parameters length rho epsilon field potential low source) := by
  exact residual_higherVanishing_of_traces source _ flat
    (originalFiniteLift_derivative_force_zero parameters length rho epsilon field potential low source)
    (originalFiniteLift_derivative_force_linear parameters length rho epsilon field potential low source flat)
    (originalFiniteLift_derivative_force_quadratic parameters length rho epsilon field potential low source)
    (originalFiniteLift_derivative_mean_zero parameters length rho epsilon field potential low source 2 (Or.inl rfl))
    (originalFiniteLift_derivative_determinant_linear parameters length rho epsilon positive field potential vanishes low source)
    (originalFiniteLift_derivative_mean_zero parameters length rho epsilon field potential low source 3 (Or.inr rfl))
    (originalFiniteLift_derivative_fourth_linear parameters length rho epsilon field potential low source)
    (originalFiniteLift_derivative_fourth_quadratic parameters length rho epsilon positive field potential vanishes low source flat)

end Grad.FinitePhysicalJetLift
