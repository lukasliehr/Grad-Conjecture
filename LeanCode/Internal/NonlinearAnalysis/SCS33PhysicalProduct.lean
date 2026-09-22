import SCS32PhysicalSourceCoefficients

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.BoundaryTrace
open Grad.SourceCollarDivision Grad.QuotientProjection Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Algebra

def physicalKappaDeviation (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3)
    (angles : ℝ × ℝ) : ℂ :=
  physicalKappa angles.1 (originalPhysicalSignedCofactor parameters L epsilon field angles.2
    (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 nonnegative bounded)) component -
    (![0, -1, 0] : Fin 3 → ℂ) component

/-- The convolution is the actual product of the physical cofactor and the
original source, before the angular mean-free projection. -/
theorem actualSourceProductCoefficient_physical {grade : ℕ} (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (large : 3 ≤ grade) (source : SmoothQuotient parameters) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3) (mode : ℤ × ℤ) :
    actualSourceProductCoefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
      radius nonnegative bounded component mode =
    angularCoefficient (fun polar => angularCoefficient (fun axial =>
      physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component (polar, axial) •
      physicalDividedSources parameters L source radius nonnegative bounded component (polar, axial)) mode.2) mode.1 := by
  let physical := physicalDividedSources parameters L source radius nonnegative bounded component
  have continuousPhysical : Continuous physical :=
    physicalDividedSources_continuous parameters L source radius nonnegative bounded component
  obtain ⟨bound, dominated⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi) continuousPhysical.continuousOn
  have series := doubleCoefficient_series_product
    (kappaScalar parameters L rho epsilon field small component 0 radius)
    (kappaScalar_norm_summable parameters L rho epsilon field small component radius nonnegative bounded)
    (physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component) physical
    (fun cell => coreDividedSourceCells parameters L source cell radius nonnegative bounded component)
    (fun polar => continuousPhysical.comp (continuous_const.prodMk continuous_id))
    (fun cell => coreDividedSourceCells_continuous parameters L source cell radius nonnegative bounded component)
    (physicalDividedSources_axialCoefficient parameters L source radius nonnegative bounded component)
    (max bound 0) (le_max_right _ _)
    (fun polar polarInside axial axialInside => (dominated (polar, axial) ⟨polarInside, axialInside⟩).trans (le_max_left _ _))
    (fun polar _ axial _ => by
      simpa only [fourierPhase, cellExponential, physicalKappaDeviation] using
        kappaScalar_double_hasSum parameters L rho epsilon field small component radius polar axial nonnegative bounded)
    mode
  rw [← series.tsum_eq]
  apply tsum_congr
  intro shift
  rw [originalDividedSourceCells_core]
  rfl

end Grad.SourceCollarFullSource
