import AFU4FullReferenceRightInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceLinearity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundedScalarInverse Grad.ActualForcingSupport Grad.FullReferenceAssembly Grad.CircularHighWeak
variable {L sigma gamma ell : ℝ}

/-- The literal original cell-band source condition is a complex subspace. -/
def capSourceBandSpace (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) :
    Submodule ℂ (SmoothCapSource L sigma gamma ell) where
  carrier := OriginalCapSourceBand admissible ceiling
  zero_mem' := by
    intro cell outside
    change apSmoothJet admissible 2 cell 0 = 0 ∧ apSmoothJet admissible 1 cell 0 = 0 ∧ apSmoothJet admissible 1 cell 0 = 0
    exact ⟨map_zero _, map_zero _, map_zero _⟩
  add_mem' := fun first second => capSourceBand_add admissible ceiling _ _ first second
  smul_mem' := by
    intro scalar source band cell outside
    have absent := band cell outside
    change apSmoothJet admissible 2 cell (scalar • source.1) = 0 ∧
      apSmoothJet admissible 1 cell (scalar • source.2.1) = 0 ∧ apSmoothJet admissible 1 cell (scalar • source.2.2) = 0
    exact ⟨(map_smul (apSmoothJet admissible 2 cell) scalar source.1).trans ((congrArg (scalar • ·) absent.1).trans (smul_zero _)),
      (map_smul (apSmoothJet admissible 1 cell) scalar source.2.1).trans ((congrArg (scalar • ·) absent.2.1).trans (smul_zero _)),
      (map_smul (apSmoothJet admissible 1 cell) scalar source.2.2).trans ((congrArg (scalar • ·) absent.2.2).trans (smul_zero _))⟩

def compatibleBandSource (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) :
    Submodule ℂ (SmoothCapSource L sigma gamma ell) := smoothCapSourceCore admissible ⊓ capSourceBandSpace admissible ceiling

abbrev OriginalBoundaryFamily (L sigma gamma ell : ℝ) :=
  (grade : ℕ) → APBoundaryGrade L sigma gamma ell 1 (grade + 1)

def boundaryEvaluation (grade : ℕ) (pair : ℤ × ℤ) :
    OriginalBoundaryFamily L sigma gamma ell →ₗ[ℂ] ComplexEuclidean 1 :=
  (apBoundaryCoefficientCLM L sigma gamma ell (grade + 1) pair).toLinearMap.comp (LinearMap.proj grade)

/-- The same coherent high boundary families, with literal original band support. -/
def coherentHighBandBoundary (L sigma gamma ell ceiling : ℝ) :
    Submodule ℂ (OriginalBoundaryFamily L sigma gamma ell) where
  carrier := fun family =>
    (∀ grade pair, boundaryEvaluation grade pair family = boundaryEvaluation 0 pair family) ∧
    (∀ mode ∈ lowAngularModes, ∀ cell, boundaryEvaluation 0 (mode, cell) family = 0) ∧
    (∀ cell, ¬ InCellBand L ell ceiling cell → ∀ mode, boundaryEvaluation 0 (mode, cell) family = 0)
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp only [map_zero]
  add_mem' := by
    intro first second left right
    refine ⟨?_, ?_, ?_⟩
    · intro grade pair
      exact (map_add (boundaryEvaluation grade pair) first second).trans
        ((congrArg₂ (fun a b : ComplexEuclidean 1 => a + b) (left.1 grade pair) (right.1 grade pair)).trans
          (map_add (boundaryEvaluation 0 pair) first second).symm)
    · intro mode low cell
      exact (map_add (boundaryEvaluation 0 (mode, cell)) first second).trans
        ((congrArg₂ (fun a b : ComplexEuclidean 1 => a + b) (left.2.1 mode low cell) (right.2.1 mode low cell)).trans (add_zero _))
    · intro cell outside mode
      exact (map_add (boundaryEvaluation 0 (mode, cell)) first second).trans
        ((congrArg₂ (fun a b : ComplexEuclidean 1 => a + b) (left.2.2 cell outside mode) (right.2.2 cell outside mode)).trans (add_zero _))
  smul_mem' := by
    intro scalar family member
    refine ⟨?_, ?_, ?_⟩
    · intro grade pair
      exact (map_smul (boundaryEvaluation grade pair) scalar family).trans
        ((congrArg (scalar • ·) (member.1 grade pair)).trans (map_smul (boundaryEvaluation 0 pair) scalar family).symm)
    · intro mode low cell
      exact (map_smul (boundaryEvaluation 0 (mode, cell)) scalar family).trans
        ((congrArg (scalar • ·) (member.2.1 mode low cell)).trans (smul_zero _))
    · intro cell outside mode
      exact (map_smul (boundaryEvaluation 0 (mode, cell)) scalar family).trans
        ((congrArg (scalar • ·) (member.2.2 cell outside mode)).trans (smul_zero _))

def boundaryOfFamily {ceiling : ℝ} (family : coherentHighBandBoundary L sigma gamma ell ceiling) :
    BandSmoothBoundary L sigma gamma ell := ⟨family.val, family.property.1⟩

theorem boundaryOfFamily_high {ceiling : ℝ} (family : coherentHighBandBoundary L sigma gamma ell ceiling) :
    OriginalBoundaryHigh (boundaryOfFamily family) := family.property.2.1

theorem boundaryOfFamily_band {ceiling : ℝ} (family : coherentHighBandBoundary L sigma gamma ell ceiling) :
    OriginalBoundaryBand ceiling (boundaryOfFamily family) := family.property.2.2

abbrev OriginalReferenceInput (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) :=
  compatibleBandSource admissible ceiling × coherentHighBandBoundary L sigma gamma ell ceiling

end Grad.FullReferenceLinearity
