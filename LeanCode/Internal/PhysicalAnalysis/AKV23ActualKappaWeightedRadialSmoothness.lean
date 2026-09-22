import AKV22ActualOriginalRowRadialCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)

def actualSourceKappaKernel (component : Fin 3) (radius : RadialPoint) : RadialKernel parameters radius 1 1 :=
  radialScalarKernel parameters radius 1 (kappaScalar parameters length rho epsilon field small component 0 radius.val)
    (fun moment => kappaScalarMoment_summable parameters length rho epsilon field small component moment 0 radius.val radius.property.1 radius.property.2)

/-- The original kappa coefficients have genuine radial jets and all
original-width moments, so their actual weighted action is regular. -/
theorem actualSourceKappaKernel_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (component : Fin 3) :
    SmoothConjugatedFamily parameters lower positive bounded.le
      (actualSourceKappaKernel parameters length rho epsilon field small component) := by
  apply scalarRadialJet_conjugated_smooth parameters 1 lower positive bounded
    (fun order radius => kappaScalar parameters length rho epsilon field small component order radius)
    (fun order radius mode => kappaScalar_hasDerivAt parameters length rho epsilon field small component mode order radius)
    (fun order radius moment => kappaScalarMoment_summable parameters length rho epsilon field small component moment order radius.val radius.property.1 radius.property.2)
    ?_ 0
  intro order moment
  exact ⟨_,fun radius => kappaScalarMoment_bound parameters length rho epsilon field small component moment order radius.val radius.property.1 radius.property.2⟩

end Grad.AnnularGeneralSourceRegularity
