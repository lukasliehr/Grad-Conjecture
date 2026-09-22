import AxisProjectionLaws

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### The zero-transverse instantiation

The lift is consumed with the transverse slot set to zero, which satisfies
every hypothesis of the split identities outright. The state-specific
transverse profile `- (tau·eta)/(2a) iota M y` of AL15 is a further
instance of the same `transverseMap` slot once the axis coefficient
algebra inverse is released; no identity below changes. -/

def zeroTransverse : AxisData parameters → ACore parameters 3 := fun _ => 0

theorem zeroTransverse_zero : zeroTransverse (parameters := parameters) 0 = 0 := rfl

theorem zeroTransverse_value_vanishes (data : AxisData parameters) (cell : ℤ) :
    originValue ((zeroTransverse data).val cell) = 0 := by
  change originValue ((0 : ACore parameters 3).val cell) = 0
  rw [acore_val_zero, originValue_zero]

theorem zeroTransverse_tangential (data : AxisData parameters) (cell : ℤ)
    (direction : Fin 2) :
    originPartial direction ((zeroTransverse data).val cell) 1 = 0 := by
  change originPartial direction ((0 : ACore parameters 3).val cell) 1 = 0
  rw [acore_val_zero, originPartial_zero]
  rfl

section Consumer

variable (cellLength : ℝ) (interfaceRadius : ℝ)
variable (radiusPositive : 0 < interfaceRadius)
variable (base : QuotientState parameters)

/-- Immediate consumer of AL19/AL20: at the zero-transverse instantiation
the lifted source is an exact unconditional right inverse of the source
extraction. -/
theorem consumed_right_inverse (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (data : AxisData parameters) :
    extractionData cellLength (sourceLift cellLength interfaceRadius radiusPositive base
        (zeroTransverse (parameters := parameters)) data) = data :=
  extraction_sourceLift cellLength interfaceRadius radiusPositive base zeroTransverse
    lengthPositive baseVanishes zeroTransverse_value_vanishes zeroTransverse_tangential
    data

/-- Immediate consumer of AL22/AL31: every compatible source splits exactly
into its lifted axis part and a flat remainder, and the remainder has zero
axis extraction. This applies the axis split to the source exactly once. -/
theorem consumed_source_split (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (source : QuotientRows parameters) :
    source = sourceLift cellLength interfaceRadius radiusPositive base
        (zeroTransverse (parameters := parameters))
        (extractionData cellLength source) +
      rangeProjection cellLength interfaceRadius radiusPositive base
        (zeroTransverse (parameters := parameters)) source ∧
    extractionData cellLength (rangeProjection cellLength interfaceRadius radiusPositive
        base (zeroTransverse (parameters := parameters)) source) = 0 := by
  constructor
  · unfold rangeProjection
    rw [add_sub_cancel]
  · exact extraction_rangeProjection cellLength interfaceRadius radiusPositive base
      zeroTransverse lengthPositive baseVanishes zeroTransverse_value_vanishes
      zeroTransverse_tangential source

/-- Immediate consumer of AL22 on the domain side: every direction splits
into its lifted axis data and a flat remainder with zero direction
extraction, and the flat remainder is fixed by the projection. -/
theorem consumed_direction_split (direction : QuotientState parameters) :
    direction = liftMap interfaceRadius radiusPositive
        (zeroTransverse (parameters := parameters)) (kappaData direction) +
      domainProjection interfaceRadius radiusPositive
        (zeroTransverse (parameters := parameters)) direction ∧
    kappaData (domainProjection interfaceRadius radiusPositive
        (zeroTransverse (parameters := parameters)) direction) = 0 ∧
    domainProjection interfaceRadius radiusPositive
        (zeroTransverse (parameters := parameters))
        (domainProjection interfaceRadius radiusPositive
          (zeroTransverse (parameters := parameters)) direction) =
      domainProjection interfaceRadius radiusPositive
        (zeroTransverse (parameters := parameters)) direction := by
  refine ⟨?_, ?_, ?_⟩
  · unfold domainProjection
    rw [add_sub_cancel]
  · exact kappa_domainProjection interfaceRadius radiusPositive zeroTransverse
      zeroTransverse_tangential direction
  · exact domainProjection_idempotent interfaceRadius radiusPositive zeroTransverse
      zeroTransverse_zero zeroTransverse_tangential direction

/-- Immediate consumer of AL23: the exact one-sided intertwining of the two
flat projections through the compiled linearization. -/
theorem consumed_intertwining (lengthPositive : 0 < cellLength)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (direction : QuotientState parameters)
    (directionVanishes : ∀ cell : ℤ, originValue ((stateField direction).val cell) = 0) :
    forwardMap cellLength base (domainProjection interfaceRadius radiusPositive
        (zeroTransverse (parameters := parameters)) direction) =
      rangeProjection cellLength interfaceRadius radiusPositive base
        (zeroTransverse (parameters := parameters))
        (forwardMap cellLength base direction) :=
  forward_domainProjection cellLength interfaceRadius radiusPositive base zeroTransverse
    lengthPositive baseVanishes direction directionVanishes

end Consumer

end Grad.AxisSplit
