import AKDN35ActualKappaProductEulerAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.SourceCollarBulk

theorem originalRowRadialCurves_typeTransport {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {row target : DivisionRow dimension lower} (same : row=target)
    (transport : OriginalRowRadialCurves parameters lower row=OriginalRowRadialCurves parameters lower target)
    (curves : OriginalRowRadialCurves parameters lower target) :
    (Eq.mpr transport curves).curve=curves.curve := by
  cases same
  rfl

/-- The stored restriction-row transport preserves its literal curve. -/
theorem actualRestrictedCoreRadialCurves_formula {dimension grade : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : ACore parameters dimension) (power : ℕ) (radius : ℝ) :
    (actualRestrictedCoreRadialCurves (grade := grade) parameters lower positive bounded field).curve power radius =
      cartesianWeightedRadialCurve parameters lower positive bounded field power 0 radius := by
  have same := congrFun (congrFun (originalRowRadialCurves_transport
    (cartesianRestrictionRow_exact (grade := grade) (power := 0) (radial := 0) parameters lower positive bounded (by omega) field)
    (cartesianOriginalRowRadialCurves parameters lower positive bounded field)) power) radius
  exact same

theorem actualDividedCoreRadialCurves_formula {dimension grade : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (large : 3 ≤ grade) (field : ACore parameters dimension)
    (flat : OriginalValueFlat parameters large (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field)))
    (power : ℕ) (radius : ℝ) :
    (actualDividedCoreRadialCurves parameters lower positive bounded large field flat).curve power radius =
      (radius : ℂ)⁻¹ • cartesianWeightedRadialCurve parameters lower positive bounded field power 0 radius := by
  change (radius : ℂ)⁻¹ • (actualRestrictedCoreRadialCurves (grade := grade) parameters lower positive bounded field).curve power radius = _
  rw [actualRestrictedCoreRadialCurves_formula]

/-- The divided inputs are exactly F1/r, F0/r and F2/r in the stored
order. This allows rG3 to cancel its radius before any differentiation. -/
theorem actualDividedSourceRadialCurves_formula {grade : ℕ}
    (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (large : 3 ≤ grade) (source : SmoothQuotient parameters) (flat : IsFlat source)
    (power : ℕ) (radius : ℝ) :
    (actualDividedSourceRadialCurves parameters length lower positive bounded large source flat 0).curve power radius =
      (radius : ℂ)⁻¹ • actualCartesianPrimitiveCurve parameters length lower positive bounded source 3 power radius ∧
    (actualDividedSourceRadialCurves parameters length lower positive bounded large source flat 1).curve power radius =
      (radius : ℂ)⁻¹ • actualCartesianPrimitiveCurve parameters length lower positive bounded source 0 power radius ∧
    (actualDividedSourceRadialCurves parameters length lower positive bounded large source flat 2).curve power radius =
      (radius : ℂ)⁻¹ • actualCartesianPrimitiveCurve parameters length lower positive bounded source 2 power radius := by
  have formulas := actualPrimitiveCurve_formulas parameters length lower positive bounded source power radius
  have flatInputs := originalFlatSource_division_inputs parameters large source flat
  have planarFlat : OriginalValueFlat parameters large
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (cartesianSourceVector source))) := by
    rw [←originalSourcePlanar_core]
    exact flatInputs.1
  have scalarFlat : OriginalValueFlat parameters large
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (source 3))) := flatInputs.2
  have radialRowSame := congrArg (fun datum : AGrade parameters 2 grade =>
    radialRowContraction lower positive 0
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded.le parameters large datum))
    (originalSourcePlanar_core parameters grade source)
  have tangentialRowSame := congrArg (fun datum : AGrade parameters 2 grade =>
    tangentialRowContraction lower positive 0
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded.le parameters large datum))
    (originalSourcePlanar_core parameters grade source)
  refine ⟨?_,?_,?_⟩
  · rw [formulas.2.2.2]
    change (Eq.mpr (congrArg (OriginalRowRadialCurves parameters lower) radialRowSame)
      ((actualDividedCoreRadialCurves parameters lower positive bounded large (cartesianSourceVector source) planarFlat).radial positive)).curve power radius = _
    rw [originalRowRadialCurves_transport radialRowSame]
    change weightedHilbertRadial parameters power
      ((actualDividedCoreRadialCurves parameters lower positive bounded large (cartesianSourceVector source) planarFlat).curve power radius) = _
    rw [actualDividedCoreRadialCurves_formula,map_smul]
  · rw [formulas.1]
    change (Eq.mpr (congrArg (OriginalRowRadialCurves parameters lower) tangentialRowSame)
      ((actualDividedCoreRadialCurves parameters lower positive bounded large (cartesianSourceVector source) planarFlat).tangential positive)).curve power radius = _
    rw [originalRowRadialCurves_transport tangentialRowSame]
    change weightedHilbertTangential parameters power
      ((actualDividedCoreRadialCurves parameters lower positive bounded large (cartesianSourceVector source) planarFlat).curve power radius) = _
    rw [actualDividedCoreRadialCurves_formula,map_smul]
  · rw [formulas.2.2.1]
    change (length : ℂ)⁻¹ • (actualDividedCoreRadialCurves parameters lower positive bounded large (source 3) scalarFlat).curve power radius = _
    rw [actualDividedCoreRadialCurves_formula,smul_comm]

end Grad.OriginalCartesianTameEstimate
