import AJW3HighOmegaGraphRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.AnnularReconstruction Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Exact locality of the accepted stored scalar radial operator. -/
theorem scalarRadialMap_restrict (lower upper : ℝ) (included : lower ≤ upper)
    (first second : C(ℝ, ℝ)) (firstBound secondBound : ℝ)
    (firstBounded : ∀ radius ∈ Icc lower 1, |first radius| ≤ firstBound)
    (secondBounded : ∀ radius ∈ Icc upper 1, |second radius| ≤ secondBound)
    (same : EqOn first second (Icc upper 1)) (field : RadialL2 1 lower) :
    collarL2Restriction 1 lower upper included (scalarRadialMap lower first firstBound firstBounded field) =
      scalarRadialMap upper second secondBound secondBounded (collarL2Restriction 1 lower upper included field) := by
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae 1 lower upper included (scalarRadialMap lower first firstBound firstBounded field),
    (scalarRadialMap_ae lower first firstBound firstBounded field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    scalarRadialMap_ae upper second secondBound secondBounded (collarL2Restriction 1 lower upper included field),
    collarL2Restriction_ae 1 lower upper included field, ae_restrict_mem measurableSet_Icc]
    with radius restricted source target original inside
  rw [restricted, source, target, original, same inside]

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (included : lower ≤ upper) (field : annularEnergySpace lower length lowerPositive)

theorem highEnergyRestriction_derivative :
    annularEnergyDerivative upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
      collarBulkRestriction HighAnnularMode 1 lower upper included (annularEnergyDerivative lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  rfl

theorem highEnergyRestriction_mass :
    annularEnergyMass upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
      collarBulkRestriction HighAnnularMode 1 lower upper included (annularEnergyMass lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  rfl

theorem highEnergyRestriction_outer :
    annularEnergyOuter upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
      annularEnergyOuter lower length lowerPositive field := by
  apply lp.ext
  funext mode
  change annularModeOuter upper
    (highModeRadialMap lower upper (collarL2Restriction 1 lower upper included) (field.val mode)) =
      annularModeOuter lower (field.val mode)
  exact highModeRadialMap_outer lower upper _ (field.val mode)

/-- The actual recovered stored scalar is the same restricted field. -/
theorem highEnergyRestriction_value :
    annularEnergyValue upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
      collarBulkRestriction HighAnnularMode 1 lower upper included (annularEnergyValue lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  change annularValueMassMap upper length upperPositive mode
    (collarL2Restriction 1 lower upper included (annularEnergyMass lower length lowerPositive field mode)) =
      collarL2Restriction 1 lower upper included
        (annularValueMassMap lower length lowerPositive mode (annularEnergyMass lower length lowerPositive field mode))
  symm
  apply scalarRadialMap_restrict lower upper included
  intro radius inside
  change (annularPotentialWeight lower length lowerPositive mode.val.1 mode.val.2 radius)⁻¹ =
    (annularPotentialWeight upper length upperPositive mode.val.1 mode.val.2 radius)⁻¹
  rw [annularPotentialWeight_restrict lower upper length lowerPositive upperPositive included mode.val.1 mode.val.2 inside]

theorem annularImaginarySymbolMap_restrict (mode : HighAnnularMode) (symbol : ℝ)
    (firstDominated : ∀ radius ∈ Icc lower 1, symbol ^ 2 ≤ annularPotential length radius mode.val.1 mode.val.2)
    (secondDominated : ∀ radius ∈ Icc upper 1, symbol ^ 2 ≤ annularPotential length radius mode.val.1 mode.val.2)
    (value : RadialL2 1 lower) :
    collarL2Restriction 1 lower upper included
      (annularImaginarySymbolMap lower length lowerPositive mode symbol firstDominated value) =
      annularImaginarySymbolMap upper length upperPositive mode symbol secondDominated
        (collarL2Restriction 1 lower upper included value) := by
  change collarL2Restriction 1 lower upper included (Complex.I • _) = Complex.I • _
  rw [map_smul]
  apply congrArg (fun value : RadialL2 1 upper => Complex.I • value)
  apply scalarRadialMap_restrict lower upper included
  intro radius inside
  change symbol / annularPotentialWeight lower length lowerPositive mode.val.1 mode.val.2 radius =
    symbol / annularPotentialWeight upper length upperPositive mode.val.1 mode.val.2 radius
  rw [annularPotentialWeight_restrict lower upper length lowerPositive upperPositive included mode.val.1 mode.val.2 inside]

theorem highEnergyRestriction_angular :
    annularEnergyD upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
      collarBulkRestriction HighAnnularMode 1 lower upper included (annularEnergyD lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  exact (annularImaginarySymbolMap_restrict lower upper length lowerPositive upperPositive included mode
    ((mode.val.1 : ℝ) * highMultiplier mode.val.1)
    (annularDSymbol_dominated lower length lowerPositive mode)
    (annularDSymbol_dominated upper length upperPositive mode) (annularEnergyMass lower length lowerPositive field mode)).symm

theorem highEnergyRestriction_cell :
    annularEnergyCell upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
      collarBulkRestriction HighAnnularMode 1 lower upper included (annularEnergyCell lower length lowerPositive field) := by
  apply lp.ext
  funext mode
  exact (annularImaginarySymbolMap_restrict lower upper length lowerPositive upperPositive included mode
    (highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length)
    (annularCellSymbol_dominated lower length lowerPositive mode)
    (annularCellSymbol_dominated upper length upperPositive mode) (annularEnergyMass lower length lowerPositive field mode)).symm

end Grad.AnnularRestriction
