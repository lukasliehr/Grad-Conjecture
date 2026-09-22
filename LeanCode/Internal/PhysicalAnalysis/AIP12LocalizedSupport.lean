import AIP11CompletedCoefficientIdentity

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization

theorem periodizationCutoff_one_on_interior_support :
    Set.EqOn periodizationCutoff.toFun (fun _ => 1) (tsupport interiorCutoff.toFun) := by
  intro point member
  apply periodizationCutoff_one
  rw [interiorCutoff_support] at member
  have bound : ‖point‖ ≤ (2 / 3 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

theorem periodizationCutoff_absorbs_scalar (scalar : SpatialPlane → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) (supported : tsupport scalar ⊆ tsupport interiorCutoff.toFun)
    (field : DiskL2 1) :
    diskScalar periodizationCutoff.toFun periodizationCutoff.smooth (diskScalar scalar smooth field) =
      diskScalar scalar smooth field := by
  have identity (point : SpatialPlane) : periodizationCutoff.toFun point * scalar point = scalar point := by
    by_cases inside : point ∈ tsupport scalar
    · rw [periodizationCutoff_one_on_interior_support (supported inside), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport inside, mul_zero]
  apply Lp.ext
  filter_upwards [diskScalar_ae periodizationCutoff.toFun periodizationCutoff.smooth (diskScalar scalar smooth field),
    diskScalar_ae scalar smooth field] with point outer inner
  rw [outer, inner, smul_smul, identity]

theorem periodizationCutoff_absorbs_bulk (field : DiskL2 1) :
    diskScalar periodizationCutoff.toFun periodizationCutoff.smooth
      (diskScalar interiorCutoff.toFun interiorCutoff.smooth field) =
    diskScalar interiorCutoff.toFun interiorCutoff.smooth field :=
  periodizationCutoff_absorbs_scalar _ _ Subset.rfl field

private theorem secondTest_support (direction : Fin 2) (test : SpatialPlane → ℝ) :
    tsupport (secondTestDerivative direction test) ⊆ tsupport test := by
  rw [secondTestDerivative_ordered]
  exact Grad.WeakTesting.orderedTestDerivative_support_subset 2 (fun _ => direction) test

private theorem fixedCombination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (operator : E →L[ℂ] E) (a b c d e : E)
    (ha : operator a = a) (hb : operator b = b) (hc : operator c = c)
    (hd : operator d = d) (he : operator e = e) :
    operator (a + (2 : ℂ) • b + (2 : ℂ) • c + d + e) =
      a + (2 : ℂ) • b + (2 : ℂ) • c + d + e := by
  simp only [map_add, map_smul, ha, hb, hc, hd, he]

theorem periodizationCutoff_absorbs_laplacian (field : diskGrade) (laplacian : DiskL2 1) :
    diskScalar periodizationCutoff.toFun periodizationCutoff.smooth (localizedDiskLaplacian field laplacian) =
      localizedDiskLaplacian field laplacian := by
  have baseIdentity := periodizationCutoff_absorbs_bulk laplacian
  have firstX := periodizationCutoff_absorbs_scalar (firstTestDerivative 0 interiorCutoff.toFun)
    (firstTestDerivative_smooth 0 _ interiorCutoff.smooth)
    (firstTestDerivative_supported 0 _) (diskGradX field)
  have firstY := periodizationCutoff_absorbs_scalar (firstTestDerivative 1 interiorCutoff.toFun)
    (firstTestDerivative_smooth 1 _ interiorCutoff.smooth)
    (firstTestDerivative_supported 1 _) (diskGradY field)
  have secondX := periodizationCutoff_absorbs_scalar (secondTestDerivative 0 interiorCutoff.toFun)
    (secondTestDerivative_smooth 0 _ interiorCutoff.smooth)
    (secondTest_support 0 _) (diskBulk field)
  have secondY := periodizationCutoff_absorbs_scalar (secondTestDerivative 1 interiorCutoff.toFun)
    (secondTestDerivative_smooth 1 _ interiorCutoff.smooth)
    (secondTest_support 1 _) (diskBulk field)
  exact fixedCombination (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth)
    _ _ _ _ _ baseIdentity firstX firstY secondX secondY

end Grad.InteriorPeriodization
