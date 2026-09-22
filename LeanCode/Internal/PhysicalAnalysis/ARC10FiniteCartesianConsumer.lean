import ARC9ArbitraryCutoff

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

/-- Cartesian L2 row from arbitrary mixed polar rows and an arbitrary smooth cutoff.
The local derivative equality records only the coordinate representation of this field. -/
theorem finiteFamily_cartesian_row_bound {dimension : ℕ}
    (cutoff : ℝ × ℝ → ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff)
    (modes : Finset ℤ) (profiles : ℤ → ℝ → ComplexEuclidean dimension)
    (profilesSmooth : ∀ mode, ContDiff ℝ ∞ (profiles mode))
    (field : SpatialPlane → ComplexEuclidean dimension) (fieldSmooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0)
    (index : CartesianMultiIndex) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (cutoffBounds : ∀ order, order ≤ cartesianOrder index → ∀ point ∈ halfCollarRectangle,
      ‖iteratedFDeriv ℝ order cutoff point‖ ≤ bound)
    (representation : ∀ order, order ≤ cartesianOrder index → ∀ point ∈ halfCollarRectangle,
      iteratedFDeriv ℝ order (field ∘ collarPlane) point =
        iteratedFDeriv ℝ order (fun point => cutoff point • finiteProfileField modes profiles point) point) :
    ‖closedDerivativeL2 index (globalClosedJet field fieldSmooth)‖ ^ 2 ≤
      (halfReverseConstant (cartesianOrder index) * cutoffDensityConstant bound (cartesianOrder index)) *
        finiteProfileEnergy modes profiles (cartesianOrder index) := by
  let grade := cartesianOrder index
  have profileSmooth := finiteProfileField_smooth modes profiles profilesSmooth
  have comparison := halfCollarIntegral_mono
    (polarJetSquaredDensity (field ∘ collarPlane) grade)
    (fun point => cutoffDensityConstant bound grade *
      polarJetSquaredDensity (finiteProfileField modes profiles) grade point)
    (polarJetSquaredDensity_continuous _ (fieldSmooth.comp collarPlane_smooth) grade)
    (continuous_const.mul (polarJetSquaredDensity_continuous _ profileSmooth grade)) (by
      intro point inside
      have equality : polarJetSquaredDensity (field ∘ collarPlane) grade point =
          polarJetSquaredDensity (fun point => cutoff point • finiteProfileField modes profiles point) grade point := by
        apply Finset.sum_congr rfl
        intro order orderIn
        rw [representation order (by have := Finset.mem_range.mp orderIn; omega) point inside]
      rw [equality]
      exact cutoff_density_bound cutoff cutoffSmooth _ profileSmooth grade bound boundNonnegative point
        (fun order upper => cutoffBounds order upper point inside))
  rw [halfCollarIntegral_const_mul] at comparison
  have polarBound := comparison.trans (mul_le_mul_of_nonneg_left
    (finiteProfileField_density_energy modes profiles profilesSmooth grade)
    (cutoffDensityConstant_nonnegative bound grade))
  exact (closedDerivative_halfCollar_energy field fieldSmooth vanishes index).trans
    ((mul_le_mul_of_nonneg_left polarBound (halfReverseConstant_nonnegative grade)).trans_eq (by ring))

/-- One constant depends only on the cutoff and derivative row, uniformly over
value dimension, every finite mode set, and arbitrary smooth radial profiles. -/
theorem arbitraryFiniteFamily_cartesian_consumer (cutoff : ℝ × ℝ → ℝ)
    (cutoffSmooth : ContDiff ℝ ∞ cutoff) (index : CartesianMultiIndex) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (dimension : ℕ) (modes : Finset ℤ)
      (profiles : ℤ → ℝ → ComplexEuclidean dimension),
      (∀ mode, ContDiff ℝ ∞ (profiles mode)) →
      ∀ (field : SpatialPlane → ComplexEuclidean dimension) (fieldSmooth : ContDiff ℝ ∞ field),
      (∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0) →
      (∀ point ∈ halfCollarRectangle, (field ∘ collarPlane) =ᶠ[𝓝 point]
        (fun point => cutoff point • finiteProfileField modes profiles point)) →
      ‖closedDerivativeL2 index (globalClosedJet field fieldSmooth)‖ ^ 2 ≤
        constant * finiteProfileEnergy modes profiles (cartesianOrder index) := by
  obtain ⟨bound, boundNonnegative, cutoffBounds⟩ :=
    exists_polarCutoffBound cutoff cutoffSmooth (cartesianOrder index)
  refine ⟨halfReverseConstant (cartesianOrder index) * cutoffDensityConstant bound (cartesianOrder index),
    mul_nonneg (halfReverseConstant_nonnegative _) (cutoffDensityConstant_nonnegative _ _), ?_⟩
  intro dimension modes profiles profilesSmooth field fieldSmooth vanishes representation
  exact finiteFamily_cartesian_row_bound cutoff cutoffSmooth modes profiles profilesSmooth field fieldSmooth
    vanishes index bound boundNonnegative cutoffBounds
    (fun order _ point inside => ((representation point inside).iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds)

end Grad.CollarCartesian
