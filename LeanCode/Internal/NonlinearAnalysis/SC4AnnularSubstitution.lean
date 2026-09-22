import SC3AngularMeanFree

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped Interval

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.Constraints

/-- One physical polar circle of a Cartesian source `(f,g,h)`. -/
@[ext] structure AngularCartesianSource where
  planar : ℝ → ComplexEuclidean 2
  scalarG : ℝ → ℂ
  scalarH : ℝ → ℂ

/-- The four bulk coordinates in BS30.  Traces are deliberately not included:
they are restrictions of this bulk data, not values set by the conversion. -/
@[ext] structure AnnularBulkSource where
  F0 : ℝ → ℂ
  F1 : ℝ → ℂ
  F2 : ℝ → ℂ
  G3 : ℝ → ℂ

/-- The complete expression inside the mean-free projector in BS30. -/
def annularCorrection (kappa : ℝ → Fin 3 → ℂ) (source : AnnularBulkSource) : ℝ → ℂ :=
  fun angle => kappa angle 0 * source.F1 angle +
    kappa angle 1 * source.F0 angle - kappa angle 2 * source.F2 angle

/-- Literal physical Cartesian-to-annular conversion BS30. -/
def cartesianToAnnular (radius L : ℝ) (kappa : ℝ → Fin 3 → ℂ)
    (source : AngularCartesianSource) : AnnularBulkSource where
  F0 angle := polarTangentialComponent angle (source.planar angle)
  F1 angle := polarRadialComponent angle (source.planar angle)
  F2 angle := source.scalarH angle / (L : ℂ)
  G3 angle := source.scalarG angle / (L : ℂ) +
    sourceAngularMeanFree (fun theta =>
      kappa theta 0 * polarRadialComponent theta (source.planar theta) +
      kappa theta 1 * polarTangentialComponent theta (source.planar theta) -
      kappa theta 2 * (source.scalarH theta / (L : ℂ))) angle / (radius : ℂ)

/-- Literal reverse substitution BS32. -/
def annularToCartesian (radius L : ℝ) (kappa : ℝ → Fin 3 → ℂ)
    (source : AnnularBulkSource) : AngularCartesianSource where
  planar angle := polarSourceReconstruct angle (source.F0 angle) (source.F1 angle)
  scalarH angle := (L : ℂ) * source.F2 angle
  scalarG angle := (L : ℂ) * (source.G3 angle -
    sourceAngularMeanFree (annularCorrection kappa source) angle / (radius : ℂ))

theorem cartesianToAnnular_correction (radius L : ℝ) (kappa : ℝ → Fin 3 → ℂ)
    (source : AngularCartesianSource) :
    annularCorrection kappa (cartesianToAnnular radius L kappa source) =
      fun angle => kappa angle 0 * polarRadialComponent angle (source.planar angle) +
        kappa angle 1 * polarTangentialComponent angle (source.planar angle) -
        kappa angle 2 * (source.scalarH angle / (L : ℂ)) := rfl

/-- Substituting BS30 into BS32 recovers the actual Cartesian source. -/
theorem annularToCartesian_cartesianToAnnular (radius L : ℝ)
    (LPositive : 0 < L) (kappa : ℝ → Fin 3 → ℂ)
    (source : AngularCartesianSource) :
    annularToCartesian radius L kappa (cartesianToAnnular radius L kappa source) = source := by
  apply AngularCartesianSource.ext
  · funext angle
    exact polarSourceReconstruct_components angle (source.planar angle)
  · funext angle
    have nonzero : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt LPositive)
    change (L : ℂ) * (source.scalarG angle / (L : ℂ) +
      sourceAngularMeanFree (annularCorrection kappa
        (cartesianToAnnular radius L kappa source)) angle / (radius : ℂ) -
      sourceAngularMeanFree (annularCorrection kappa
        (cartesianToAnnular radius L kappa source)) angle / (radius : ℂ)) = source.scalarG angle
    rw [add_sub_cancel_right, mul_div_cancel₀ _ nonzero]
  · funext angle
    dsimp only [annularToCartesian, cartesianToAnnular]
    have nonzero : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt LPositive)
    exact mul_div_cancel₀ (source.scalarH angle) nonzero

/-- Substituting BS32 into BS30 recovers every annular bulk tuple. -/
theorem cartesianToAnnular_annularToCartesian (radius L : ℝ)
    (LPositive : 0 < L) (kappa : ℝ → Fin 3 → ℂ)
    (source : AnnularBulkSource) :
    cartesianToAnnular radius L kappa (annularToCartesian radius L kappa source) = source := by
  have nonzero : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt LPositive)
  apply AnnularBulkSource.ext
  · funext angle
    exact polarTangentialComponent_reconstruct angle (source.F0 angle) (source.F1 angle)
  · funext angle
    exact polarRadialComponent_reconstruct angle (source.F0 angle) (source.F1 angle)
  · funext angle
    dsimp only [cartesianToAnnular, annularToCartesian]
    exact mul_div_cancel_left₀ (source.F2 angle) nonzero
  · funext angle
    have correctionEquality :
        annularCorrection kappa
          (cartesianToAnnular radius L kappa (annularToCartesian radius L kappa source)) =
          annularCorrection kappa source := by
      funext theta
      simp only [annularCorrection, cartesianToAnnular, annularToCartesian,
        polarTangentialComponent_reconstruct, polarRadialComponent_reconstruct]
      rw [mul_div_cancel_left₀ _ nonzero]
    change ((L : ℂ) * (source.G3 angle -
      sourceAngularMeanFree (annularCorrection kappa source) angle / (radius : ℂ))) / (L : ℂ) +
        sourceAngularMeanFree (annularCorrection kappa
          (cartesianToAnnular radius L kappa (annularToCartesian radius L kappa source))) angle /
          (radius : ℂ) = source.G3 angle
    rw [correctionEquality]
    rw [mul_div_cancel_left₀ _ nonzero]
    abel

/-- The conversion leaves `F0` unrestricted: it is exactly the tangential
component of the incoming Cartesian source, with no mean hypothesis. -/
theorem cartesianToAnnular_F0 (radius L : ℝ) (kappa : ℝ → Fin 3 → ℂ)
    (source : AngularCartesianSource) (angle : ℝ) :
    (cartesianToAnnular radius L kappa source).F0 angle =
      polarTangentialComponent angle (source.planar angle) := rfl

theorem cartesianToAnnular_F2_mean_zero (radius L : ℝ) (kappa : ℝ → Fin 3 → ℂ)
    (source : AngularCartesianSource)
    (meanZero : sourceAngularAverage source.scalarH = 0) :
    sourceAngularAverage (cartesianToAnnular radius L kappa source).F2 = 0 := by
  change sourceAngularAverage (fun angle => source.scalarH angle / (L : ℂ)) = 0
  rw [sourceAngularAverage_div, meanZero, zero_div]

theorem cartesianToAnnular_G3_mean_zero (radius L : ℝ)
    (radiusPositive : 0 < radius) (kappa : ℝ → Fin 3 → ℂ)
    (source : AngularCartesianSource)
    (gIntegrable : IntervalIntegrable source.scalarG volume 0 (2 * Real.pi))
    (correctionIntegrable : IntervalIntegrable
      (annularCorrection kappa (cartesianToAnnular radius L kappa source))
      volume 0 (2 * Real.pi))
    (gMeanZero : sourceAngularAverage source.scalarG = 0) :
    sourceAngularAverage (cartesianToAnnular radius L kappa source).G3 = 0 := by
  have _radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt radiusPositive)
  change sourceAngularAverage (fun angle => source.scalarG angle / (L : ℂ) +
    sourceAngularMeanFree (annularCorrection kappa
      (cartesianToAnnular radius L kappa source)) angle / (radius : ℂ)) = 0
  rw [show (fun angle => source.scalarG angle / (L : ℂ) +
      sourceAngularMeanFree (annularCorrection kappa
        (cartesianToAnnular radius L kappa source)) angle / (radius : ℂ)) =
      (fun angle => source.scalarG angle / (L : ℂ)) +
        (fun angle => sourceAngularMeanFree (annularCorrection kappa
          (cartesianToAnnular radius L kappa source)) angle / (radius : ℂ)) by rfl]
  unfold sourceAngularAverage
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add (gIntegrable.div_const _)
    ((sourceAngularMeanFree_intervalIntegrable correctionIntegrable).div_const _), smul_add]
  change sourceAngularAverage (fun angle => source.scalarG angle / (L : ℂ)) +
    sourceAngularAverage (fun angle => sourceAngularMeanFree
      (annularCorrection kappa (cartesianToAnnular radius L kappa source)) angle /
        (radius : ℂ)) = 0
  rw [sourceAngularAverage_div, sourceAngularAverage_div, gMeanZero,
    sourceAngularAverage_meanFree correctionIntegrable, zero_div, zero_div, add_zero]

end Grad.SourceCollar
