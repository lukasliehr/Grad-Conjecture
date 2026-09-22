import AxisProjections

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

theorem axisInsertion_zero {dimension : ℕ} (firstJet secondJet : ClosedJet dimension) :
    axisInsertion (0 : TCore parameters) firstJet secondJet = 0 := by
  apply Subtype.ext
  funext cell
  change ((0 : TCore parameters).val cell 0) • firstJet +
    ((0 : TCore parameters).val cell 1) • secondJet = 0
  have firstComponent : (0 : TCore parameters).val cell 0 = 0 := rfl
  have secondComponent : (0 : TCore parameters).val cell 1 = 0 := rfl
  rw [firstComponent, secondComponent, zero_smul, zero_smul, add_zero]

section ProjectionLaws

variable (cellLength : ℝ) (interfaceRadius : ℝ)
variable (radiusPositive : 0 < interfaceRadius)
variable (base : QuotientState parameters)
variable (transverseMap : AxisData parameters → ACore parameters 3)

/-- The lift of the zero axis data is the zero direction. -/
theorem liftMap_zero (transverseZero : transverseMap 0 = 0) :
    liftMap interfaceRadius radiusPositive transverseMap (0 : AxisData parameters) = 0 := by
  unfold liftMap axisLiftDirection liftPhysicalField liftScalarField
  have firstData : (0 : AxisData parameters).1 = 0 := rfl
  have secondData : (0 : AxisData parameters).2 = 0 := rfl
  rw [firstData, secondData, transverseZero, axisInsertion_zero, axisInsertion_zero,
    add_zero]
  rfl

/-- AL19, bundled: the direction extraction inverts the lift on axis data. -/
theorem kappa_liftMap
    (transverseTangential : ∀ (data : AxisData parameters) (cell : ℤ) (direction : Fin 2),
      originPartial direction ((transverseMap data).val cell) 1 = 0)
    (data : AxisData parameters) :
    kappaData (liftMap interfaceRadius radiusPositive transverseMap data) = data := by
  have rawIdentity := kappa_axisLift interfaceRadius radiusPositive (transverseMap data)
    data (transverseTangential data)
  have firstVal := congrArg Prod.fst rawIdentity
  have secondVal := congrArg Prod.snd rawIdentity
  apply Prod.ext
  · exact Subtype.ext firstVal
  · exact Subtype.ext secondVal

/-- The domain projection lands in the kernel of the direction extraction. -/
theorem kappa_domainProjection
    (transverseTangential : ∀ (data : AxisData parameters) (cell : ℤ) (direction : Fin 2),
      originPartial direction ((transverseMap data).val cell) 1 = 0)
    (direction : QuotientState parameters) :
    kappaData (domainProjection interfaceRadius radiusPositive transverseMap direction) =
      0 := by
  unfold domainProjection
  rw [kappaData_sub, kappa_liftMap interfaceRadius radiusPositive transverseMap
    transverseTangential, sub_self]

/-- AL22: the domain projection is idempotent. -/
theorem domainProjection_idempotent (transverseZero : transverseMap 0 = 0)
    (transverseTangential : ∀ (data : AxisData parameters) (cell : ℤ) (direction : Fin 2),
      originPartial direction ((transverseMap data).val cell) 1 = 0)
    (direction : QuotientState parameters) :
    domainProjection interfaceRadius radiusPositive transverseMap
        (domainProjection interfaceRadius radiusPositive transverseMap direction) =
      domainProjection interfaceRadius radiusPositive transverseMap direction := by
  have kernelValue := kappa_domainProjection interfaceRadius radiusPositive transverseMap
    transverseTangential direction
  unfold domainProjection
  unfold domainProjection at kernelValue
  rw [kernelValue, liftMap_zero interfaceRadius radiusPositive transverseMap
    transverseZero, sub_zero]

/-- AL22: the domain projection fixes the flat kernel. -/
theorem domainProjection_fixes (transverseZero : transverseMap 0 = 0)
    (direction : QuotientState parameters)
    (flat : kappaData direction = 0) :
    domainProjection interfaceRadius radiusPositive transverseMap direction = direction := by
  unfold domainProjection
  rw [flat, liftMap_zero interfaceRadius radiusPositive transverseMap transverseZero,
    sub_zero]

/-- AL11, bundled at the current state: the source extraction of the
linearization is the direction extraction. -/
theorem extraction_forward (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (direction : QuotientState parameters)
    (directionVanishes : ∀ cell : ℤ, originValue ((stateField direction).val cell) = 0) :
    extractionData cellLength (forwardMap cellLength base direction) =
      kappaData direction := by
  have rawIdentity := axisExtraction_linearization cellLength lengthPositive base direction
    baseVanishes directionVanishes
  have leftVal := extractionData_val cellLength (forwardMap cellLength base direction)
  have rightVal := kappaData_val direction
  have combined : ((extractionData cellLength (forwardMap cellLength base direction)).1.val,
      (extractionData cellLength (forwardMap cellLength base direction)).2.val) =
      ((kappaData direction).1.val, (kappaData direction).2.val) := by
    rw [leftVal, rightVal]
    exact rawIdentity
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst combined)
  · exact Subtype.ext (congrArg Prod.snd combined)

/-- AL20, bundled: the source extraction inverts the lifted source. -/
theorem extraction_sourceLift (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (transverseValueVanishes : ∀ (data : AxisData parameters) (cell : ℤ),
      originValue ((transverseMap data).val cell) = 0)
    (transverseTangential : ∀ (data : AxisData parameters) (cell : ℤ) (direction : Fin 2),
      originPartial direction ((transverseMap data).val cell) 1 = 0)
    (data : AxisData parameters) :
    extractionData cellLength (sourceLift cellLength interfaceRadius radiusPositive base
        transverseMap data) = data := by
  unfold sourceLift
  rw [extraction_forward cellLength base lengthPositive baseVanishes
    (liftMap interfaceRadius radiusPositive transverseMap data)
    (fun cell => axisLift_field_originValue interfaceRadius radiusPositive
      (transverseMap data) data (transverseValueVanishes data) cell)]
  exact kappa_liftMap interfaceRadius radiusPositive transverseMap transverseTangential data

/-- The range projection lands in the kernel of the source extraction. -/
theorem extraction_rangeProjection (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (transverseValueVanishes : ∀ (data : AxisData parameters) (cell : ℤ),
      originValue ((transverseMap data).val cell) = 0)
    (transverseTangential : ∀ (data : AxisData parameters) (cell : ℤ) (direction : Fin 2),
      originPartial direction ((transverseMap data).val cell) 1 = 0)
    (source : QuotientRows parameters) :
    extractionData cellLength (rangeProjection cellLength interfaceRadius radiusPositive
        base transverseMap source) = 0 := by
  unfold rangeProjection
  rw [extractionData_sub, extraction_sourceLift cellLength interfaceRadius radiusPositive
    base transverseMap lengthPositive baseVanishes transverseValueVanishes
    transverseTangential, sub_self]

theorem sourceLift_zero (transverseZero : transverseMap 0 = 0) :
    sourceLift cellLength interfaceRadius radiusPositive base transverseMap
      (0 : AxisData parameters) = 0 := by
  unfold sourceLift
  rw [liftMap_zero interfaceRadius radiusPositive transverseMap transverseZero]
  exact rowsDerivative_direction_zero cellLength base

/-- AL22: the range projection is idempotent. -/
theorem rangeProjection_idempotent (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (transverseZero : transverseMap 0 = 0)
    (transverseValueVanishes : ∀ (data : AxisData parameters) (cell : ℤ),
      originValue ((transverseMap data).val cell) = 0)
    (transverseTangential : ∀ (data : AxisData parameters) (cell : ℤ) (direction : Fin 2),
      originPartial direction ((transverseMap data).val cell) 1 = 0)
    (source : QuotientRows parameters) :
    rangeProjection cellLength interfaceRadius radiusPositive base transverseMap
        (rangeProjection cellLength interfaceRadius radiusPositive base transverseMap
          source) =
      rangeProjection cellLength interfaceRadius radiusPositive base transverseMap
        source := by
  have kernelValue := extraction_rangeProjection cellLength interfaceRadius radiusPositive
    base transverseMap lengthPositive baseVanishes transverseValueVanishes
    transverseTangential source
  conv_lhs => rw [rangeProjection]
  rw [kernelValue, sourceLift_zero cellLength interfaceRadius radiusPositive base
    transverseMap transverseZero, sub_zero]

/-- AL22: the range projection fixes the flat source kernel. -/
theorem rangeProjection_fixes (transverseZero : transverseMap 0 = 0)
    (source : QuotientRows parameters)
    (flat : extractionData cellLength source = 0) :
    rangeProjection cellLength interfaceRadius radiusPositive base transverseMap source =
      source := by
  unfold rangeProjection
  rw [flat, sourceLift_zero cellLength interfaceRadius radiusPositive base transverseMap
    transverseZero, sub_zero]

/-- AL23: the exact intertwining `A_b P_X = P_Y A_b` on axis-vanishing
directions. -/
theorem forward_domainProjection (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (direction : QuotientState parameters)
    (directionVanishes : ∀ cell : ℤ, originValue ((stateField direction).val cell) = 0) :
    forwardMap cellLength base
        (domainProjection interfaceRadius radiusPositive transverseMap direction) =
      rangeProjection cellLength interfaceRadius radiusPositive base transverseMap
        (forwardMap cellLength base direction) := by
  unfold domainProjection rangeProjection sourceLift
  unfold forwardMap
  rw [rowsDerivative_direction_sub]
  rw [show extractionData cellLength (quotientRowsDerivative parameters cellLength 1 base
      ![direction]) = kappaData direction from
    extraction_forward cellLength base lengthPositive baseVanishes direction
      directionVanishes]

end ProjectionLaws

end Grad.AxisSplit
