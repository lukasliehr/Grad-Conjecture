import ACB13ActualAllRadialBounds
import ARW7RadialMeasure

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.CollarCartesian Grad.ActualRadialWords Grad.ActualOuterCollar Grad.ActualInverseInduction
open Grad.BoundaryTrace Grad.BoundaryLift

def centerWordRows (profile : ℝ → ComplexEuclidean 1) (order : ℕ)
    (word : CartesianWord order) (mode : ℤ) (time : ℝ) : ComplexEuclidean 1 := wordAmplitude mode profile word time

theorem centerWordRows_continuousOn (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1)) (order : ℕ) (word : CartesianWord order) (mode : ℤ) :
    ContinuousOn (centerWordRows profile order word mode) (Icc (0 : ℝ) (1 / 2)) :=
  wordAmplitude_continuousOn mode profile smooth word

def centerOuterField (mode : ℤ) (field : ClosedJet 1) (point : SpatialPlane) : ComplexEuclidean 1 :=
  outerCutoffScalar point • pureExtension mode field point

theorem centerOuterField_smooth (mode : ℤ) (field : ClosedJet 1) : ContDiff ℝ ∞ (centerOuterField mode field) :=
  outerCutoffScalar_smooth.smul (pureExtension_smooth mode field)

def centerOuterJet (mode : ℤ) (field : ClosedJet 1) : ClosedJet 1 :=
  globalClosedJet (centerOuterField mode field) (centerOuterField_smooth mode field)

theorem centerOuterField_zero (mode : ℤ) (field : ClosedJet 1) (point : SpatialPlane)
    (small : ‖point‖ < (7 / 12 : ℝ)) : centerOuterField mode field point = 0 := by
  rw [centerOuterField, (outerCutoff_zero_germ point small).eq_of_nhds, zero_smul]

theorem pureExtension_collar (mode : ℤ) (field : ClosedJet 1) (point : ℝ × ℝ) :
    pureExtension mode field (collarPlane point) = polarMode mode (pureProfile mode field) point := by
  have equality : polarPlane (1 - point.1, point.2) = collarPlane point := by
    simp only [polarPlane, sub_sub_cancel]
  rw [← equality, pureExtension_polar]
  rfl

theorem centerOuterField_polar (mode : ℤ) (field : ClosedJet 1) :
    centerOuterField mode field ∘ collarPlane =
      fun point => actualPolarCutoff point • polarMode mode (pureProfile mode field) point := by
  funext point
  change outerCutoffScalar (collarPlane point) • pureExtension mode field (collarPlane point) = _
  rw [pureExtension_collar]
  rfl

theorem centerPolar_word_expansion (mode : ℤ) (field : ClosedJet 1) (order : ℕ)
    (word : CartesianWord order) (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    iteratedFDeriv ℝ order (polarMode mode (pureProfile mode field)) point
      (fun position => productBasis (word position)) =
        ∑ selected ∈ ({mode} : Finset ℤ), fourier selected (point.2 : CellCircle) •
          centerWordRows (pureProfile mode field) order word selected point.1 := by
  rw [Finset.sum_singleton, polarMode_word_derivative mode _ (pureProfile_smooth mode field).contDiffOn order word point inside]
  rw [centerWordRows, wordAmplitude, polarRadialDerivative,
    show fourier mode (point.2 : CellCircle) = cellExponential mode point.2 from cellCharacter_coe _ _]
  exact smul_comm _ _ _

/-- The fixed actual cutoff controls every Cartesian row of the genuine
center outer field. No cutoff radiality or assumed outer representative is used. -/
theorem centerOuterJet_mixedRows_bound (index : CartesianMultiIndex) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (mode : ℤ) (field : ClosedJet 1),
      ‖closedDerivativeL2 index (centerOuterJet mode field)‖ ^ 2 ≤
        constant * ∫ time in (0 : ℝ)..(1 / 2 : ℝ),
          mixedRowsDensity {mode} (centerWordRows (pureProfile mode field)) (cartesianOrder index) time := by
  obtain ⟨constant, nonnegative, estimates⟩ :=
    localRows_cartesian_consumer actualPolarCutoff actualPolarCutoff_smooth index
  refine ⟨constant, nonnegative, ?_⟩
  intro mode field
  exact estimates 1 (centerOuterField mode field) (centerOuterField_smooth mode field)
    (centerOuterField_zero mode field) (polarMode mode (pureProfile mode field))
    (polarMode_smoothOn mode _ (pureProfile_smooth mode field).contDiffOn) {mode}
    (centerWordRows (pureProfile mode field))
    (centerWordRows_continuousOn _ (pureProfile_smooth mode field).contDiffOn)
    (fun _ _ => Filter.Eventually.of_forall (congrFun (centerOuterField_polar mode field)))
    (fun order _ time inside angle word => centerPolar_word_expansion mode field order word (time, angle) ⟨inside, mem_univ _⟩)

end Grad.ActualCenterBounds
