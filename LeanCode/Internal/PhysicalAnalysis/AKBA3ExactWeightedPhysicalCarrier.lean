import AKBA2ExactOriginalPhysicalRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.AnnularOriginalSmoothCore

/-- Every actual all-grade row has the precise original weighted closed
physical smoothness required by the immutable AKI/AKR carrier. -/
theorem originalWeightedPhysicalSmooth_of_lowCurves {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1) :
    OriginalWeightedPhysicalSmooth parameters lower (curves.fullField bounded) := by
  refine ⟨⟨curves.fullField_smooth bounded,curves.fullField_angular_periodic bounded,curves.fullField_cell_periodic bounded⟩,
    curves.curve,curves.smooth,?_⟩
  intro grade radius inside mode
  rw [originalPhysicalCoefficient,curves.fullField_coefficient bounded radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode,Real.exp_neg,Complex.ofReal_inv,
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  simpa only [zero_add,Complex.ofReal_pow,Grad.SourceCollarDivision.annularFrequency,Grad.AnnularVariational.annularFrequency] using curves.shift bounded 0 grade radius inside mode

end Grad.OriginalKernelGraphRestriction
