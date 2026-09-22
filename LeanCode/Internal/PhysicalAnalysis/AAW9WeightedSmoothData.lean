import AAW8DenseFullSmoothData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularGradedSmoothData (lower : ℝ) (angular cell inserted : ℕ)
    (core : AnnularSmoothDataCore) : AnnularForcing lower × AnnularBoundary :=
  annularDataDecode lower angular cell inserted (annularFiniteSmoothData lower core)

theorem annularGradedSmoothData_hasGrade (lower : ℝ) (angular cell inserted : ℕ)
    (core : AnnularSmoothDataCore) :
    HasAnnularDataGrade lower angular cell inserted (annularGradedSmoothData lower angular cell inserted core) :=
  annularDataDecode_hasGrade lower angular cell inserted _

theorem annularGradedSmoothData_weighted (lower : ℝ) (angular cell inserted : ℕ)
    (core : AnnularSmoothDataCore) :
    annularWeightedData lower angular cell inserted (annularGradedSmoothData lower angular cell inserted core)
      (annularGradedSmoothData_hasGrade lower angular cell inserted core) = annularFiniteSmoothData lower core := by
  apply annularDataDecode_injective lower angular cell inserted
  exact annularDataDecode_weighted lower angular cell inserted _ _

theorem annularDecodedSmoothBulk_physical (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (angular cell inserted : ℕ) (core : AnnularSmoothBulkCore) (mode : HighAnnularMode) :
    annularDecodeMode parameters lower positive mode (annularLpDecode angular cell inserted (annularFiniteSmoothBulk lower core) mode)
      =ᵐ[volume.restrict (Icc lower 1)]
        (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) • annularSmoothPhysicalCurve parameters mode (core mode) := by
  change annularDecodeMode parameters lower positive mode
    ((((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) • annularFiniteSmoothBulk lower core mode) =ᵐ[_] _
  rw [map_smul, annularFiniteSmoothBulk_apply]
  filter_upwards [Lp.coeFn_smul (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ)
      (annularDecodeMode parameters lower positive mode (annularSmoothBulkMode lower (core mode))),
    annularSmoothBulkMode_physical parameters lower positive mode (core mode)] with radius scaled physical
  rw [scaled, Pi.smul_apply, physical]
  rfl

theorem annularGradedSmoothData_solution (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (angular cell inserted : ℕ) (core : AnnularSmoothDataCore) (mode : HighAnnularMode) :
    let data := annularGradedSmoothData lower angular cell inserted core
    ContDiffOn ℝ ∞ (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) := by
  let scalar : ℂ := (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ)
  dsimp only
  apply annularSameSolution_smooth parameters lower length positive bounded lengthPositive widthHalf widthLength _ _ mode
    (scalar • annularSmoothPhysicalCurve parameters mode (core.1.1 mode))
    (scalar • annularSmoothPhysicalCurve parameters mode (core.1.2.1 mode))
    (scalar • annularSmoothPhysicalCurve parameters mode (core.1.2.2.1 mode))
    ((annularSmoothPhysicalCurve_smooth parameters mode (core.1.1 mode)).const_smul scalar).contDiffOn
    ((annularSmoothPhysicalCurve_smooth parameters mode (core.1.2.1 mode)).const_smul scalar).contDiffOn
    ((annularSmoothPhysicalCurve_smooth parameters mode (core.1.2.2.1 mode)).const_smul scalar).contDiffOn
  all_goals exact annularDecodedSmoothBulk_physical parameters lower positive angular cell inserted _ mode

end Grad.AnnularRegularity
