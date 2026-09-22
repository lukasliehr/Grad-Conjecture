import AKO13CanonicalIncomingDensityGluing
import AKO11ActualRetainedFamilyCommonRadii

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularRestriction

variable (upper length : ℝ) (upperBounded : upper < 1) (lengthPositive : 0 < length)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (bounded : ∀ index, collars index < 1)
    (decreasing : Antitone collars)
    (fields : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)

def actualFamilyLocalSquares (index : ℕ) : ℝ → ℝ≥0∞ :=
  coupledIncomingSquare (collars index) length (positive index) (bounded index) lengthPositive (fields index)

def actualFamilyIncomingNorm : ℝ → ℝ :=
  cofinalIncomingNorm upper collars (actualFamilyLocalSquares length lengthPositive collars positive bounded fields)

/-- Compatibility is equality of the original retained graph restriction,
not an assumed equality of traces or of arbitrary L2 representatives. -/
def ActualRetainedFamilyCompatible : Prop :=
  ∀ first second (order : first ≤ second),
    coupledEndpointRestriction (collars second) (collars first) length (positive second) (positive first)
      (bounded first) lengthPositive (decreasing order) (fields second) = fields first

include upperBounded in
theorem actualFamilyLocalSquares_compatible
    (compatible : ActualRetainedFamilyCompatible length lengthPositive collars positive bounded decreasing fields) :
    ∀ first second radius, radius ∈ Icc (collars first) upper → radius ∈ Icc (collars second) upper →
      actualFamilyLocalSquares length lengthPositive collars positive bounded fields first radius =
        actualFamilyLocalSquares length lengthPositive collars positive bounded fields second radius := by
  have ordered (first second : ℕ) (order : first ≤ second) (radius : ℝ)
      (inside : radius ∈ Icc (collars first) upper) :
      actualFamilyLocalSquares length lengthPositive collars positive bounded fields first radius =
        actualFamilyLocalSquares length lengthPositive collars positive bounded fields second radius := by
    have actual := coupledIncomingSquare_restriction (collars second) (collars first) radius length
      (positive second) (positive first) ((positive first).trans_le inside.1) (inside.2.trans_lt upperBounded)
      lengthPositive (decreasing order) inside.1 (fields second)
    rw [compatible first second order] at actual
    exact actual
  intro first second radius firstInside secondInside
  rcases le_total first second with order | order
  · exact ordered first second order radius firstInside
  · exact (ordered second first order radius secondInside).symm

include upperBounded in
theorem actualFamilyLocalSquares_ne_top (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (collars index) upper) :
    actualFamilyLocalSquares length lengthPositive collars positive bounded fields index radius ≠ ⊤ := by
  have actual := coupledIncomingSquare_eq_restricted_norm (collars index) length (positive index) lengthPositive radius
    ((positive index).trans_le inside.1) (inside.2.trans_lt upperBounded) inside.1 (fields index)
  exact actual.trans_ne ENNReal.ofReal_ne_top

theorem actualFamilyIncomingNorm_measurable :
    Measurable (actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields) :=
  cofinalIncomingNorm_measurable upper collars _ (fun index =>
    coupledIncomingSquare_measurable (collars index) length (positive index) (bounded index) lengthPositive (fields index))

theorem actualFamilyIncomingNorm_nonnegative (radius : ℝ) :
    0 ≤ actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields radius :=
  cofinalIncomingNorm_nonnegative upper collars _ radius

include upperBounded in
theorem actualFamilyIncomingNorm_square
    (cofinal : Tendsto collars atTop (𝓝 0))
    (compatible : ActualRetainedFamilyCompatible length lengthPositive collars positive bounded decreasing fields)
    (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (collars index) upper) :
    ENNReal.ofReal (actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields radius ^ 2) =
      coupledIncomingSquare (collars index) length (positive index) (bounded index) lengthPositive (fields index) radius := by
  have same := actualFamilyLocalSquares_compatible upper length upperBounded lengthPositive collars positive bounded decreasing fields compatible
  have finite := cofinalIncomingSquare_ne_top upper collars positive cofinal _ same
    (actualFamilyLocalSquares_ne_top upper length upperBounded lengthPositive collars positive bounded fields) radius
  exact (cofinalIncomingNorm_square upper collars _ radius finite).trans
    (cofinalIncomingSquare_same upper collars _ same index radius inside)

/-- At every allowed radius, the glued real function is literally the norm
of the original full incoming boundary pair of the SAME restricted field. -/
theorem actualFamilyIncomingNorm_eq_trace
    (compatible : ActualRetainedFamilyCompatible length lengthPositive collars positive bounded decreasing fields)
    (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (collars index) upper) :
    actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields radius =
      ‖coupledIncomingTrace radius length ((positive index).trans_le inside.1) (inside.2.trans_lt upperBounded) lengthPositive
        (coupledEndpointRestriction (collars index) radius length (positive index) ((positive index).trans_le inside.1)
          (inside.2.trans_lt upperBounded) lengthPositive inside.1 (fields index))‖ := by
  have same := actualFamilyLocalSquares_compatible upper length upperBounded lengthPositive collars positive bounded decreasing fields compatible
  have actual := coupledIncomingSquare_eq_restricted_norm (collars index) length (positive index) lengthPositive radius
    ((positive index).trans_le inside.1) (inside.2.trans_lt upperBounded) inside.1 (fields index)
  unfold actualFamilyIncomingNorm cofinalIncomingNorm
  rw [cofinalIncomingSquare_same upper collars _ same index radius inside]
  change Real.sqrt (coupledIncomingSquare (collars index) length (positive index) (bounded index) lengthPositive (fields index) radius).toReal = _
  refine (congrArg (fun value : ℝ≥0∞ => Real.sqrt value.toReal) actual).trans ?_
  exact (congrArg Real.sqrt (ENNReal.toReal_ofReal (sq_nonneg _))).trans (Real.sqrt_sq (norm_nonneg _))

end Grad.AnnularIncomingIntegrability
