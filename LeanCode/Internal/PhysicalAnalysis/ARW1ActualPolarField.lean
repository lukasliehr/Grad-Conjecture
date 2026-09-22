import ARC14LocalRowConsumer
import AOC4ActualFiniteOuterConsumer
import CDO2OrdinaryDiskConsumer
import AQR6ActualSecondRadialConsumer

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.CollarCartesian Grad.BoundaryLift Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.ActualInverseInduction Grad.InteriorLocalization

def actualProfile (mode : ℤ) (parameter : ℝ) (source : highDiskL2) : ℝ → ComplexEuclidean 1 :=
  actualRadialValue (1 / 2) (by norm_num) (by norm_num) mode parameter source

theorem actualProfile_smooth (mode : ℤ) (high : mode ∉ lowAngularModes) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ContDiffOn ℝ ∞ (actualProfile mode parameter source) (Icc (1 / 2 : ℝ) 1) :=
  weakInverse_closedCollar_smooth (1 / 2) (by norm_num) (by norm_num) mode high parameter source core same

def polarMode (mode : ℤ) (profile : ℝ → ComplexEuclidean 1) (point : ℝ × ℝ) : ComplexEuclidean 1 :=
  cellExponential mode point.2 • profile (1 - point.1)

theorem polarMode_smoothOn (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1)) :
    ContDiffOn ℝ ∞ (polarMode mode profile) openHalfCollar := by
  apply (angularExponential_smooth mode).contDiffOn.smul
  exact smooth.comp (contDiff_const.sub contDiff_fst).contDiffOn (by
    intro point inside
    constructor <;> linarith [inside.1.1, inside.1.2])

def actualPolarFinite (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) :
    ℝ × ℝ → ComplexEuclidean 1 :=
  ∑ mode ∈ finiteHighModes modes, polarMode mode (actualProfile mode parameter source)

theorem actualPolarFinite_smooth (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ContDiffOn ℝ ∞ (actualPolarFinite modes parameter source) openHalfCollar := by
  have expression : actualPolarFinite modes parameter source =
      fun point => ∑ mode ∈ finiteHighModes modes, polarMode mode (actualProfile mode parameter source) point := by
    funext point
    simp only [actualPolarFinite, Finset.sum_apply]
  rw [expression]
  apply ContDiffOn.sum
  intro mode inside
  exact polarMode_smoothOn mode _ (actualProfile_smooth mode (Finset.mem_filter.mp inside).2 parameter source core same)

def actualOuterJet (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) : ClosedJet 1 :=
  withinClosedJet (finiteOuterField modes parameter source) (finiteOuterField_smooth modes parameter source core same)

end Grad.ActualRadialWords
