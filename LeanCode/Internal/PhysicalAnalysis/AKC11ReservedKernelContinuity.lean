import AKC10ExactReservedMatrixSeries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open Set
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity

theorem conjugatedMatrixPoint_continuous {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (index : (ℤ × ℤ) × (ℤ × ℤ)) :
    Continuous (fun radius => conjugatedMatrixPoint parameters grade reserve radius (kernel radius) index) := by
  apply (fourierMatrixPoint ((twoFrequencyTranslation index.1).symm index.2) index.2).continuous.comp
  exact (((Complex.continuous_ofReal.comp
    ((bulkWeightRatio_continuous parameters grade index.1 ((twoFrequencyTranslation index.1).symm index.2)).comp
      continuous_subtype_val)).mul continuous_const).smul (regular.1 index.1 index.2))

/-- Four polynomial input degrees make every actual uniformly regular kernel
operator-norm continuous. The analytic envelope and all Fourier entries are unchanged. -/
theorem conjugatedKernelAction_reserved_continuous {source target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) :
    Continuous (fun radius => conjugatedKernelAction parameters grade 4 radius (kernel radius)) := by
  obtain ⟨constant, _, bounded⟩ := regular.2 (grade + 4)
  have series : Continuous (fun radius => ∑' index,
      conjugatedMatrixPoint parameters grade 4 radius (kernel radius) index) := by
    apply continuous_tsum (conjugatedMatrixPoint_continuous parameters grade 4 kernel regular)
      (latticeDoubleDecay_summable.mul_left constant)
    intro index radius
    simpa only [mul_assoc] using conjugatedMatrixPoint_bound parameters grade 4 4 radius (kernel radius)
      constant (bounded radius) index
  apply series.congr
  intro radius
  exact (conjugatedKernelAction_matrixSeries parameters grade 4 radius (kernel radius)
    (conjugatedMatrixPoint_summable parameters grade radius (kernel radius))).symm

theorem radialConjugatedAction_reserved_continuous {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (regular : RegularKernelFamily kernel) (grade : ℕ) :
    Continuous (radialConjugatedAction parameters lower positive bounded kernel grade 4) :=
  (conjugatedKernelAction_reserved_continuous parameters grade kernel regular).comp
    (collarRadius_continuous lower positive bounded)

end Grad.AnnularWeightedSmoothness
