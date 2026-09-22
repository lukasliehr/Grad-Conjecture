import AJG5SevenModeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularCurrentSource
open Grad.AnnularSourceGraph Grad.AnnularStrongData Grad.AnnularStrongSolution

theorem unweightedSourceRF0Bulk_genuine (parameters : PhaseParameters) (lower : ℝ)
    (source : AnnularTotalSourceH1 parameters 1 lower 1 0 0) (mode : ℤ × ℤ) :
    unweightedSourceRF0Bulk parameters lower source mode =
      (Complex.I * (mode.1 : ℂ)) • unweightedSourceF0Bulk parameters lower source mode := by
  change sourceAngularRatio mode • (annularSourceCoordinate parameters 1 lower 1 0 0 source mode) =
    (Complex.I * (mode.1 : ℂ)) •
      (sourceGradeRatio 0 0 1 0 mode • annularSourceCoordinate parameters 1 lower 1 0 0 source mode)
  have ratio : sourceAngularRatio mode = (Complex.I * (mode.1 : ℂ)) * (sourceGradeRatio 0 0 1 0 mode : ℂ) := by
    simp only [sourceAngularRatio, sourceGradeRatio, splitTangentialWeight, pow_zero, pow_one,
      mul_one, div_eq_mul_inv, one_mul, Complex.ofReal_inv]
  rw [ratio, mul_smul]
  rfl

theorem unweightedSourceRF0Bulk_genuine_ae (parameters : PhaseParameters) (lower : ℝ)
    (source : AnnularTotalSourceH1 parameters 1 lower 1 0 0) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      unweightedSourceRF0Bulk parameters lower source mode radius =
        (Complex.I * (mode.1 : ℂ)) • unweightedSourceF0Bulk parameters lower source mode radius := by
  rw [ae_all_iff]
  intro mode
  rw [unweightedSourceRF0Bulk_genuine]
  exact Lp.coeFn_smul _ _

/-- The exact same radial weight multiplies F0 and RF0, so the prescribed
weighted source retains its genuine angular derivative. -/
theorem weightedSource_genuineAngular (parameters : PhaseParameters) (lower : ℝ) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) (weighted : HighKnownSourceBulk lower)
    (compatible : WeightedGraphCompatibility parameters lower grade graphs weighted) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      weighted 1 mode radius = (Complex.I * (mode.1 : ℂ)) • weighted 0 mode radius := by
  filter_upwards [compatible, unweightedSourceRF0Bulk_genuine_ae parameters lower graphs.1]
    with radius compatible derivative
  intro mode
  rw [(compatible mode).2.1, (compatible mode).1, derivative mode]
  exact smul_comm _ _ _

theorem strongKnownBulk_genuineAngular (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      strongKnownBulk parameters lower positive bounded data 1 mode radius =
        (Complex.I * (mode.1 : ℂ)) • strongKnownBulk parameters lower positive bounded data 0 mode radius :=
  weightedSource_genuineAngular parameters lower 0
    (highKnownF0GraphProjection parameters lower 0 0 data.val.ofLp.1,
      highKnownF2GraphProjection parameters lower 0 0 data.val.ofLp.1)
    (strongKnownBulk parameters lower positive bounded data)
    (StrongDataCarrier.compatibility parameters lower positive bounded 0 0 data)

theorem strongKnownBulk_second_meanFree (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) (mode : ℤ × ℤ) (mean : mode.1 = 0) :
    strongKnownBulk parameters lower positive bounded data 2 mode = 0 :=
  (meanFreeRow_fixed_iff lower _).mp
    (StrongDataCarrier.mean_free parameters lower positive bounded 0 0 data).1 mode mean

end Grad.AnnularPhysicalReconstruction
