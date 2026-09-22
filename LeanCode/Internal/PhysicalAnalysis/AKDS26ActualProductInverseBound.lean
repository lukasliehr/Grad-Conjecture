import AKDS25ActualFlatReferenceOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 5000
namespace Grad.OriginalInverseNeighborhood.OriginalPhysicalProduct
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit Grad.NonlinearQuotientBounds
open Grad.OriginalCoreRealization Grad.FinitePhysicalJetLift Grad.GaugeCoefficients.Physical.Allocation
open Grad.SmoothingFamily Grad.QuotientProjection Grad.ChartAxisProjections

variable {parameters : PhaseParameters} {positive : 0<parameters.length}
  {reference : Seed.Parameters} {insideR : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}

/-- The actual flat inverse estimate supplies the exact one-high estimate
of the SAME original inverse map. The only extra reserve is the already
proved nine-loss source projection, on one fixed higher base. -/
theorem inverseMap_bound_of_actual_flat
    (product : OriginalPhysicalProduct parameters positive reference insideR center)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (higher loss : ℕ) (higherLarge : 24≤higher) (lossLarge : 20≤loss) (lowFits : loss+6≤higher)
    (flatConstants : ℕ→ℝ) (flatNonnegative : ∀ grade,0≤flatConstants grade)
    (flatSolve : ∀ finite (member : finite∈product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference insideR)
      (low : stateSize parameters reference insideR higher 0 state≤2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length),
      ∃ reconstructed : stateSmoothRange parameters reference insideR,
        literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
          (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
          ((product.neighborhood.raiseBase higher higherLarge).axis state low) reconstructed=source.val ∧
        ∀ grade, ‖stateToGrade parameters grade reconstructed.val‖≤flatConstants grade*
          (‖quotientEta parameters (grade+loss) source.val.val‖+
            physicalBudget parameters (actualFiniteCurrentField parameters reference insideR finite.1
              (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
              (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖)) :
    ∃ constants : ℕ→ℝ, (∀ grade,0≤constants grade) ∧
      ∀ grade finite, finite∈product.neighborhood.parameterDomain →
      ∀ state : stateSmoothRange parameters reference insideR,
      stateSize parameters reference insideR higher 0 state≤2*product.neighborhood.radius →
      ∀ source : sourceSmoothRange parameters,
      stateSize parameters reference insideR higher grade
        (product.inverseMap widthHalf widthLength finite state source) ≤
      constants grade*(sourceSize parameters higher (grade+(loss+9)) source+
        (1+stateSize parameters reference insideR higher (grade+(loss+9)) state)*
          sourceSize parameters higher (loss+9) source) := by
  let assembled := fullSource_reference_assembly parameters parameters.length 1 zero_lt_one le_rfl
    reference insideR product.neighborhood.seedPatch product.neighborhood.compact product.neighborhood.patchInside
  let axisConstants := assembled.choose
  have axisNonnegative := assembled.choose_spec.1
  have axisAssemble := assembled.choose_spec.2
  let projected := fun grade => actualProjectedSource_oneHigh_payment parameters parameters.length positive 1 zero_lt_one le_rfl
    (higher+grade+loss) loss (by omega) (by omega) reference insideR product.neighborhood.seedPatch
    product.neighborhood.compact product.neighborhood.patchInside product.neighborhood.curvatureBound product.coefficientBound
    (2*product.neighborhood.radius) (mul_nonneg (by norm_num) product.neighborhood.radiusPositive.le)
  let projectionConstants := fun grade => (projected grade).choose
  have projectionNonnegative (grade : ℕ) : 0≤projectionConstants grade := (projected grade).choose_spec.1
  refine ⟨fun grade => axisConstants (higher+grade)+flatConstants (higher+grade)*projectionConstants grade,
    fun grade => add_nonneg (axisNonnegative _) (mul_nonneg (flatNonnegative _) (projectionNonnegative _)),?_⟩
  intro grade finite member state low source
  let insideS := product.neighborhood.patchInside (product.neighborhood.seedInside finite member)
  let base : RealJointCore parameters reference insideR := (finite.2,state)
  let axis := (product.neighborhood.raiseBase higher higherLarge).axis state low
  let sourceFlat : OriginalFlatSource parameters parameters.length :=
    ⟨realRangeProjection 1 zero_lt_one le_rfl parameters.length reference insideR finite.1 insideS base axis source,
      realRangeProjection_mem 1 zero_lt_one le_rfl parameters.length positive reference insideR finite.1 insideS base axis source⟩
  let solved := flatSolve finite member state low sourceFlat
  let flatState := solved.choose
  have flatLaw := solved.choose_spec.1
  have flatBound := solved.choose_spec.2
  let flatPayment := fun index => flatConstants index*
    (‖quotientEta parameters (index+loss) sourceFlat.val.val‖+
      physicalBudget parameters (actualFiniteCurrentField parameters reference insideR finite.1 insideS base)
        (finite.1 0) finite.2 (index+loss)*‖quotientEta parameters loss sourceFlat.val.val‖)
  let full := axisAssemble finite.1 (product.neighborhood.seedInside finite member) insideS base axis source
    flatState flatPayment flatLaw flatBound
  let reconstructed := full.choose
  have fullLaw := full.choose_spec.1
  have fullBound := full.choose_spec.2
  have same : product.inverseMap widthHalf widthLength finite state source=reconstructed := by
    rw [← fullLaw]
    exact product.inverseMap_higher_left widthHalf widthLength higher higherLarge finite member state low reconstructed
  rw [same]
  let payment := ‖quotientEta parameters (higher+grade+loss+9) source.val‖+
    (1+‖stateToGrade parameters (higher+grade+loss+9) state.val‖)*‖quotientEta parameters (higher+loss+9) source.val‖
  have stateReserve : ‖stateToGrade parameters (loss+6) state.val‖≤2*product.neighborhood.radius :=
    (referenceState_norm_mono parameters (by omega : loss+6≤higher+0) state.val).trans low
  have curvature : |base.1|≤product.neighborhood.curvatureBound := by
    simpa only [Real.norm_eq_abs] using product.neighborhood.curvature finite member
  have projectionBound := (projected grade).choose_spec.2 finite.1
    (product.neighborhood.seedInside finite member) insideS base curvature (product.seedBound finite member 0)
    axis source stateReserve
  change ‖quotientEta parameters (higher+grade+loss) sourceFlat.val.val‖+
    (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR finite.1 insideS base)
      (finite.1 0) finite.2 (higher+grade+loss))*‖quotientEta parameters loss sourceFlat.val.val‖ ≤
    projectionConstants grade*(‖quotientEta parameters (higher+grade+loss+9) source.val‖+
      (1+‖stateToGrade parameters (higher+grade+loss+9) state.val‖)*‖quotientEta parameters (loss+9) source.val‖)
      at projectionBound
  have sourceLow := referenceSource_norm_mono parameters (by omega : loss+9≤higher+loss+9) source.val
  have projectionPaid := projectionBound.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ‖quotientEta parameters (higher+grade+loss+9) source.val‖)
      (mul_le_mul_of_nonneg_left sourceLow (add_nonneg zero_le_one (norm_nonneg _)))) (projectionNonnegative grade))
  have flatToProjection : flatPayment (higher+grade) ≤
      flatConstants (higher+grade)*projectionConstants grade*payment := by
    have enlarge := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one : physicalBudget parameters
        (actualFiniteCurrentField parameters reference insideR finite.1 insideS base) (finite.1 0) finite.2
        (higher+grade+loss)≤1+physicalBudget parameters
        (actualFiniteCurrentField parameters reference insideR finite.1 insideS base) (finite.1 0) finite.2
        (higher+grade+loss)) (norm_nonneg (quotientEta parameters loss sourceFlat.val.val))
    have paid := (add_le_add (le_refl ‖quotientEta parameters (higher+grade+loss) sourceFlat.val.val‖) enlarge).trans projectionPaid
    exact (mul_le_mul_of_nonneg_left paid (flatNonnegative (higher+grade))).trans_eq (mul_assoc _ _ _).symm
  have axisHigh := referenceSource_norm_mono parameters (by omega : higher+grade+3≤higher+grade+loss+9) source.val
  have axisState := referenceState_norm_mono parameters (by omega : higher+grade≤higher+grade+loss+9) state.val
  have axisLow := referenceSource_norm_mono parameters (by omega : 3≤higher+loss+9) source.val
  have axisPaid : ‖quotientEta parameters (higher+grade+3) source.val‖+
      (1+‖stateToGrade parameters (higher+grade) state.val‖)*‖quotientEta parameters 3 source.val‖ ≤ payment :=
    add_le_add axisHigh (mul_le_mul (add_le_add_right axisState 1) axisLow (norm_nonneg _)
      (add_nonneg zero_le_one (norm_nonneg _)))
  have bound := (fullBound (higher+grade) (by omega)).trans
    (add_le_add (mul_le_mul_of_nonneg_left axisPaid (axisNonnegative (higher+grade))) flatToProjection)
  have combined : ‖stateToGrade parameters (higher+grade) reconstructed.val‖ ≤
      (axisConstants (higher+grade)+flatConstants (higher+grade)*projectionConstants grade)*payment :=
    bound.trans_eq (by ring)
  dsimp only [payment] at combined
  rw [show higher+grade+loss+9=higher+(grade+(loss+9)) by omega,
    show higher+loss+9=higher+(loss+9) by omega] at combined
  exact combined

end Grad.OriginalInverseNeighborhood.OriginalPhysicalProduct
