import AKDN37LiteralFullG3Curve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.AnnularWeightedSmoothness Grad.AnnularSmoothCore Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual rG3 formula expressed directly in the original undivided
source primitives. Each kappa remains an actual coefficient action. -/
def actualExpandedThirdCurve (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters) (power : ℕ) (radius : ℝ) : CellL2 1 :=
  let primitive := fun slot => actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power radius
  let action := fun component => radialConjugatedAction parameters lower positive bounded.le
    (actualSourceKappaKernel parameters length rho epsilon field small component) power 0 radius
  radius • ((length : ℂ)⁻¹ • cartesianWeightedRadialCurve parameters lower positive bounded (source 2) power 0 radius)+
    hilbertMeanFree parameters (((action 0 (primitive 3)+action 1 (primitive 0))-action 2 (primitive 2))-primitive 0)

/-- Literal positive-radius cancellation is performed BEFORE Euler
differentiation. Thus neither r inverse derivatives nor any extra source
regularity premise enters the actual forcing allocation. -/
theorem actualThirdCurve_expanded (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat (grade+1) radius =
      actualExpandedThirdCurve parameters length rho epsilon field small lower positive bounded source (grade+1) radius := by
  rw [actualThirdCurve_formula,actualOriginalG3RadialCurves_formula parameters length rho epsilon field small lower positive bounded
    source flat (grade+1) radius inside,actualFullG3RadialCurves_formula]
  dsimp only
  have divided := actualDividedSourceRadialCurves_formula parameters length lower positive bounded
    (by norm_num : 3≤6) source flat (grade+1) radius
  rw [divided.1,divided.2.1,divided.2.2]
  unfold actualExpandedThirdCurve
  dsimp only
  rw [smul_add]
  congr 1
  have nonzero : (radius : ℂ) ≠ 0 := by exact_mod_cast (positive.trans_le inside.1).ne'
  have scalar (value : CellL2 1) : radius • value = (radius : ℂ) • value := (Complex.coe_smul radius value).symm
  have cancel (action : CellL2 1 →L[ℂ] CellL2 1) (value : CellL2 1) :
      (radius : ℂ) • action ((radius : ℂ)⁻¹ • value) = action value := by
    rw [←map_smul,smul_inv_smul₀ nonzero]
  rw [scalar,←map_smul,smul_sub,smul_sub,smul_add,cancel,cancel,cancel,smul_inv_smul₀ nonzero]

end Grad.OriginalCartesianTameEstimate
