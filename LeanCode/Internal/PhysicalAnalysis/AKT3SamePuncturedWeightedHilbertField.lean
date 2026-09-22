import AKT2SamePhaseWeightedLocalFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularRestriction
open Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower) (cofinal : Tendsto lower atTop (𝓝 0))
    (fields : ∀ index, CoupledSpace (lower index) length (positive index) lengthPositive)
    (allGrades : ∀ index grade, ∃ weighted : CoupledSpace (lower index) length (positive index) lengthPositive,
      CoupledInsertedGrade (lower index) length (positive index) lengthPositive grade (fields index) weighted)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing fields)

/-- One original-phase full Fourier field on every positive radius. It is
formed from the actual annular graphs, with no alternate source or width. -/
def puncturedWeightedPair (grade : ℕ) : ℝ → CellL2 1 × CellL2 1 :=
  gluedClosedSections lower cofinal
    (fun index => nativeLocalWeightedPair parameters (lower index) length (positive index) (bounded index) lengthPositive
      (fields index) (allGrades index) grade)

include compatible

/-- Exact recovery of every collar, with its full original endpoint values. -/
theorem puncturedWeightedPair_same (grade index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) :
    puncturedWeightedPair parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius =
      nativeLocalWeightedPair parameters (lower index) length (positive index) (bounded index) lengthPositive
        (fields index) (allGrades index) grade ⟨radius,inside⟩ :=
  gluedClosedSections_same lower cofinal _ positive
    (nativeLocalWeightedPair_compatible parameters length lengthPositive lower positive bounded decreasing fields allGrades compatible grade)
    index radius inside

theorem puncturedWeightedPair_continuous (grade : ℕ) :
    ContinuousOn (puncturedWeightedPair parameters length lengthPositive lower positive bounded cofinal fields allGrades grade) (Ioc (0 : ℝ) 1) :=
  gluedClosedSections_continuous lower cofinal _ positive
    (nativeLocalWeightedPair_compatible parameters length lengthPositive lower positive bounded decreasing fields allGrades compatible grade)
    (fun index => (bounded index).le)

/-- The glued Hilbert pair is the SAME original physical X,xi Fourier pair
multiplied by exactly the original exponential phase, at every collar. -/
theorem puncturedWeightedPair_physical (grade index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (mode : ℤ × ℤ) :
    ((puncturedWeightedPair parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).1 mode,
      (puncturedWeightedPair parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).2 mode) =
    (Real.exp (radialPhase parameters radius mode.2) •
      sameCoupledXCoefficient parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) grade ⟨radius,inside⟩ mode,
     Real.exp (radialPhase parameters radius mode.2) •
      sameCoupledXiCoefficient parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) grade ⟨radius,inside⟩ mode) := by
  rw [puncturedWeightedPair_same parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible grade index radius inside]
  exact Prod.ext
    (conjugatedCoupledXSection_physical parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) (allGrades index) grade ⟨radius,inside⟩ mode)
    (conjugatedCoupledXiSection_physical parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) (allGrades index) grade ⟨radius,inside⟩ mode)

end Grad.ActualPuncturedFamily
