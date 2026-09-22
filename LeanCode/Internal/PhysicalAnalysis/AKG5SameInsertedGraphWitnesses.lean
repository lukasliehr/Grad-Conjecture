import AKG4RegularRadialActionLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardDatum Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowOrbit

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)

/-- The SAME inserted witness restricts in all energy, flux derivative and
low derivative coordinates. No higher-grade witness is chosen afresh. -/
theorem coupledEndpointRestriction_inserted (grade : ℕ)
    (field weighted : CoupledSpace lower length lowerPositive lengthPositive)
    (same : CoupledInsertedGrade lower length lowerPositive lengthPositive grade field weighted) :
    CoupledInsertedGrade upper length upperPositive lengthPositive grade
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted) := by
  refine ⟨?_,?_,?_⟩
  · intro mode
    change highModeRadialMap lower upper (collarL2Restriction 1 lower upper included) (weighted.ofLp.1.ofLp.1.val mode) =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        highModeRadialMap lower upper (collarL2Restriction 1 lower upper included) (field.ofLp.1.ofLp.1.val mode)
    rw [same.1 mode,map_smul]
  · intro slot mode
    change collarL2Restriction 1 lower upper included (weighted.ofLp.1.ofLp.2.val slot mode) =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        collarL2Restriction 1 lower upper included (field.ofLp.1.ofLp.2.val slot mode)
    rw [same.2.1 slot mode,map_smul]
  · intro slot index
    change collarL2Restriction 1 lower upper included (weighted.ofLp.2.val slot index) =
      ((lowInsertedFrequency index ^ grade : ℝ) : ℂ) •
        collarL2Restriction 1 lower upper included (field.ofLp.2.val slot index)
    rw [same.2.2 slot index,map_smul]

theorem originalRetainedRestriction_inserted (grade : ℕ)
    (field weighted : OriginalCoupledSpace lower length lowerPositive)
    (same : CoupledInsertedGrade lower length lowerPositive lengthPositive grade
      (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive field)
      (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive weighted)) :
    CoupledInsertedGrade upper length upperPositive lengthPositive grade
      (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field))
      (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted)) := by
  rw [originalRetainedRestriction_weighted,originalRetainedRestriction_weighted]
  exact coupledEndpointRestriction_inserted lower upper length lowerPositive upperPositive upperBounded lengthPositive included grade _ _ same

/-- The four original copied source/residual insertion relations are
preserved together, with no added angular order on F2 or either residual. -/
theorem originalFiveBlockRestriction_sourceInserted (grade : ℕ)
    (field weighted : ForwardFiveBlocks parameters lower length lowerPositive)
    (first : ∀ mode : ℤ × ℤ, weighted.ofLp.2.ofLp.1.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.2.ofLp.1.ofLp.1 mode)
    (second : ∀ mode : ℤ × ℤ, weighted.ofLp.2.ofLp.1.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.2.ofLp.1.ofLp.2 mode)
    (third : ∀ mode : ℤ × ℤ, weighted.ofLp.2.ofLp.2.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.2.ofLp.2.ofLp.1 mode)
    (fourth : ∀ mode : ℤ × ℤ, weighted.ofLp.2.ofLp.2.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.2.ofLp.2.ofLp.2 mode) :
    let output := originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
    let inserted := originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted
    (∀ mode : ℤ × ℤ, inserted.ofLp.2.ofLp.1.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.2.ofLp.1.ofLp.1 mode) ∧
    (∀ mode : ℤ × ℤ, inserted.ofLp.2.ofLp.1.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.2.ofLp.1.ofLp.2 mode) ∧
    (∀ mode : ℤ × ℤ, inserted.ofLp.2.ofLp.2.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.2.ofLp.2.ofLp.1 mode) ∧
    (∀ mode : ℤ × ℤ, inserted.ofLp.2.ofLp.2.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.2.ofLp.2.ofLp.2 mode) :=
  originalFullSourceRestriction_inserted parameters lower upper included grade field.ofLp.2 weighted.ofLp.2 first second third fourth

end Grad.AnnularRestriction
