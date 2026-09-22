import AKV25OriginalRowCurveAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularOriginalCoreRealization Grad.AnnularRadialSmoothness Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- The SAME actual kappa convolution of a genuine original source row.
The input and output physical coefficients are supplied by the stored SCS
product equality, and all regularity is proved by the actual kernel jets. -/
def actualKappaProductRadialCurves (component : Fin 3)
    {row target : DivisionRow 1 lower} (curves : OriginalRowRadialCurves parameters lower row)
    (actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift : ℤ × ℤ => kappaScalar parameters length rho epsilon field small component 0 radius shift •
        originalRowCoefficient parameters 0 lower row radius (mode-shift))
        (originalRowCoefficient parameters 0 lower target radius mode)) :
    OriginalRowRadialCurves parameters lower target where
  curve grade radius := radialConjugatedAction parameters lower positive bounded.le
    (actualSourceKappaKernel parameters length rho epsilon field small component) grade 0 radius (curves.curve grade radius)
  smooth grade := coherentConjugatedKernelCurve_smooth parameters lower positive bounded.le
    (actualSourceKappaKernel parameters length rho epsilon field small component) curves.curve curves.smooth
    (curves.shift bounded) grade
    (actualSourceKappaKernel_smooth parameters length rho epsilon field small lower positive bounded component grade)
  same grade := by
    filter_upwards [curves.same grade,actual,ae_restrict_mem measurableSet_Icc] with radius same actual inside
    intro mode
    have literal := collarRadius_literal lower positive bounded.le radius inside
    have inputSame : ∀ query, curves.curve grade radius query =
        (Grad.AnnularVariational.annularFrequency query.1 query.2 ^ grade : ℂ) •
          ((Real.exp (Grad.PhaseAlgebra.radialPhase parameters (collarRadius lower positive bounded.le radius).val query.2) : ℂ) •
            originalRowCoefficient parameters 0 lower row radius query) := by
      intro query
      rw [literal]
      exact same query
    have product : HasSum (fun shift =>
        (actualSourceKappaKernel parameters length rho epsilon field small component
          (collarRadius lower positive bounded.le radius)).entry shift (twoFrequencyTranslation shift mode)
          (originalRowCoefficient parameters 0 lower row radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters 0 lower target radius mode) := by
      change HasSum (fun shift => kappaScalar parameters length rho epsilon field small component 0
        (collarRadius lower positive bounded.le radius).val shift • originalRowCoefficient parameters 0 lower row radius (mode-shift)) _
      rw [literal]
      exact actual mode
    have result := conjugatedKernelAction_exactCoefficient parameters grade (collarRadius lower positive bounded.le radius)
      (actualSourceKappaKernel parameters length rho epsilon field small component (collarRadius lower positive bounded.le radius))
      (curves.curve grade radius) (originalRowCoefficient parameters 0 lower row radius) inputSame mode _ product
    simpa only [radialConjugatedAction,literal,Grad.SourceCollarDivision.annularFrequency,Grad.AnnularVariational.annularFrequency] using result

end Grad.AnnularGeneralSourceRegularity
