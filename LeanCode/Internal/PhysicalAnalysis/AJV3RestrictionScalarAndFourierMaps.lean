import AJV2ActualWeakDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CircularHighRegularity Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Radius-local scalar multiplication commutes with actual restriction,
even when the ambient continuous extension depends on the lower endpoint. -/
theorem collarL2Restriction_scalar (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (first second : C(ℝ, ℝ)) (same : EqOn first second (Icc upper 1))
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarL2Restriction dimension lower upper included (collarScalar dimension lower first field) =
      collarScalar dimension upper second (collarL2Restriction dimension lower upper included field) := by
  apply Lp.ext
  filter_upwards [collarL2Restriction_ae dimension lower upper included (collarScalar dimension lower first field),
    (collarScalar_ae dimension lower first field).filter_mono (ae_mono (collarMeasure_le lower upper included)),
    collarScalar_ae dimension upper second (collarL2Restriction dimension lower upper included field),
    collarL2Restriction_ae dimension lower upper included field,
    ae_restrict_mem measurableSet_Icc] with radius restriction source target actual inside
  rw [restriction, source, target, actual, same inside]

/-- The unchanged full countable Fourier family of actual restricted modes. -/
def collarBulkRestriction (Index : Type*) (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper) :
    lp (fun _ : Index => CollarL2 (ComplexEuclidean dimension) lower) 2 →L[ℂ]
      lp (fun _ : Index => CollarL2 (ComplexEuclidean dimension) upper) 2 :=
  complexLpTwoMap (fun _ => collarL2Restriction dimension lower upper included) 1 (by norm_num)
    (fun _ field => by simpa only [one_mul] using collarL2Restriction_bound dimension lower upper included field)

theorem collarBulkRestriction_apply (Index : Type*) (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : lp (fun _ : Index => CollarL2 (ComplexEuclidean dimension) lower) 2) (index : Index) :
    collarBulkRestriction Index dimension lower upper included field index =
      collarL2Restriction dimension lower upper included (field index) := rfl

theorem collarBulkRestriction_bound (Index : Type*) (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : lp (fun _ : Index => CollarL2 (ComplexEuclidean dimension) lower) 2) :
    ‖collarBulkRestriction Index dimension lower upper included field‖ ≤ ‖field‖ := by
  unfold collarBulkRestriction
  simpa only [one_mul] using complexLpTwoMap_bound
    (fun _ : Index => collarL2Restriction dimension lower upper included) 1 (by norm_num)
    (fun _ value => by simpa only [one_mul] using collarL2Restriction_bound dimension lower upper included value) field

theorem collarBulkRestriction_id (Index : Type*) (dimension : ℕ) (lower : ℝ)
    (field : lp (fun _ : Index => CollarL2 (ComplexEuclidean dimension) lower) 2) :
    collarBulkRestriction Index dimension lower lower le_rfl field = field := by
  apply lp.ext
  funext index
  exact collarL2Restriction_id dimension lower (field index)

theorem collarBulkRestriction_comp (Index : Type*) (dimension : ℕ) (lower middle upper : ℝ)
    (first : lower ≤ middle) (second : middle ≤ upper)
    (field : lp (fun _ : Index => CollarL2 (ComplexEuclidean dimension) lower) 2) :
    collarBulkRestriction Index dimension middle upper second
        (collarBulkRestriction Index dimension lower middle first field) =
      collarBulkRestriction Index dimension lower upper (first.trans second) field := by
  apply lp.ext
  funext index
  exact collarL2Restriction_comp dimension lower middle upper first second (field index)

end Grad.AnnularRestriction
