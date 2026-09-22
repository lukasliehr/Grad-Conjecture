import AKI4LiteralOriginalResidualReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff Topology
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.PhaseAlgebra Grad.AnnularPhysicalFourier Grad.AnnularSmoothSources
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularCurrentSource

/-- A fixed original Fourier coefficient is genuinely smooth, since its
exact inverse phase is a scalar smooth function at that mode. -/
theorem PhaseWeightedRadialSmooth.coefficient_smooth {parameters : PhaseParameters} {lower : ℝ}
    {coefficient : AnnularCoefficient} (smooth : PhaseWeightedRadialSmooth parameters lower coefficient)
    (mode : ℤ × ℤ) : ContDiffOn ℝ ∞ (fun radius => coefficient radius mode) (Icc lower 1) := by
  obtain ⟨curve, regular, same⟩ := smooth
  have scalar : ContDiff ℝ ∞ (fun radius => (Real.exp (-radialPhase parameters radius mode.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Grad.AnnularWeightedSmoothness.radialPhase_smooth parameters mode.2).neg.exp)
  have evaluation : ContDiffOn ℝ ∞ (fun radius => curve 0 radius mode) (Icc lower 1) :=
    (lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).contDiff.comp_contDiffOn (regular 0)
  apply (scalar.contDiffOn.smul evaluation).congr
  intro radius inside
  change coefficient radius mode = (Real.exp (-radialPhase parameters radius mode.2) : ℂ) • curve 0 radius mode
  rw [same 0 radius inside mode]
  simp only [pow_zero, Complex.ofReal_one, one_smul, Real.exp_neg, Complex.ofReal_inv]
  symm
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') _

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : OriginalSmoothSourceCore parameters)

theorem originalCopiedF0_weightedSmooth :
    OriginalWeightedPhysicalSmooth parameters lower
      (originalSmoothSourcePhysicalF0 parameters lower positive bounded core) := by
  refine ⟨⟨originalSmoothSourcePhysicalF0_smooth_closed parameters lower positive bounded core,
    originalSmoothSourcePhysicalF0_angular_periodic parameters lower positive bounded core,
    originalSmoothSourcePhysicalF0_cell_periodic parameters lower positive bounded core⟩, ?_⟩
  exact originalSmoothSourcePhysicalF0_conjugated_radial parameters lower positive bounded core

theorem originalCopiedF2_weightedSmooth :
    OriginalWeightedPhysicalSmooth parameters lower
      (originalSmoothSourcePhysicalF2 parameters lower positive bounded core) := by
  refine ⟨⟨originalSmoothSourcePhysicalF2_smooth_closed parameters lower positive bounded core,
    originalSmoothSourcePhysicalF2_angular_periodic parameters lower positive bounded core,
    originalSmoothSourcePhysicalF2_cell_periodic parameters lower positive bounded core⟩, ?_⟩
  exact originalSmoothSourcePhysicalF2_conjugated_radial parameters lower positive bounded core

private theorem storedCoefficient_cast {first second : DivisionRow 1 lower}
    (same : first = second) (source : FiniteSmoothStoredRow lower second)
    (mode : ℤ × ℤ) (radius : ℝ) :
    (Eq.mpr (congrArg (FiniteSmoothStoredRow lower) same) source).coefficient mode radius =
      source.coefficient mode radius := by
  cases same
  rfl

private theorem originalSmoothF2Row_coefficient (mode : ℤ × ℤ) (radius : ℝ) :
    (originalSmoothF2Row parameters lower positive bounded.le core).coefficient mode radius =
      Real.sqrt radius • (meanFreeRadialCore core.1.1.2 mode).val.val.1 radius := by
  exact storedCoefficient_cast lower
    (congrArg (unweightedSourceF2Bulk parameters lower)
      (originalSmoothStrongData_graphs parameters lower positive bounded.le core).2)
    (finiteGraphSmoothRow parameters 1 lower positive (meanFreeRadialCore core.1.1.2)) mode radius

theorem originalCopiedF2_meanFree (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    originalPhysicalCoefficient (originalSmoothSourcePhysicalF2 parameters lower positive bounded core)
      radius (0, cell) = 0 := by
  unfold originalPhysicalCoefficient originalSmoothSourcePhysicalF2
  rw [finiteSourcePhysicalField_coefficient parameters lower positive bounded _ radius inside (0, cell),
    FiniteSmoothStoredRow.physicalPolynomial_mode]
  change (Grad.AnnularVariational.annularFrequency 0 cell ^ 0 : ℂ) •
    (rawPhysicalFactor parameters radius (0, cell) •
      (((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • (originalSmoothF2Row parameters lower positive bounded.le core).coefficient (0, cell) radius)) = 0
  rw [originalSmoothF2Row_coefficient parameters lower positive bounded core]
  simp [meanFreeRadialCore_apply]

end Grad.AnnularOriginalSmoothCore
