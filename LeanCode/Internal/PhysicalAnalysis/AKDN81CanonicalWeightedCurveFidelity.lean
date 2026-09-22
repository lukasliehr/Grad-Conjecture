import AKDN80ActualCartesianCovariantEulerEnergy
import AKBA2ExactOriginalPhysicalRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.AnnularGeneralSourceRegularity
open Grad.OriginalKernelRetainedDecay
open Grad.OriginalKernelGraphRestriction Grad.NonlinearRange Grad.SourceCollarFullSource Grad.PhaseAlgebra

/-- Exact canonical weighted curve of a core from the full closed-collar
physical identity. The original exponential phase is retained. -/
theorem canonicalWeightedCurve_sameNative {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (core : ACore parameters dimension)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      originalCoreCircle parameters core ⟨radius,positive.le.trans inside.1,inside.2⟩ angles=
        curves.fullField bounded (radius,angles))
    (power : ℕ) (radius : ℝ) (inside : radius∈Icc lower 1) :
    cartesianWeightedRadialCurve parameters lower positive bounded core power 0 radius=curves.curve power radius := by
  apply lp.ext
  funext mode
  rw [cartesianWeightedRadialCurve_coefficient parameters lower positive bounded core power 0 mode radius inside]
  unfold cartesianWeightedRadialCoefficient
  rw [originalCore_weighted_radial_zero parameters core ⟨radius,positive.le.trans inside.1,inside.2⟩ mode,
    show originalCoreCircle parameters core ⟨radius,positive.le.trans inside.1,inside.2⟩=
      (fun angles => curves.fullField bounded (radius,angles)) from funext (same radius inside),
    curves.fullField_doubleCoefficient bounded radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode,
    Real.exp_neg,Complex.ofReal_inv,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  symm
  simpa only [Nat.zero_add] using (curves.shift bounded 0 power radius inside mode)

end Grad.OriginalCartesianTameEstimate
