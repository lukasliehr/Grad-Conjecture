import AJI21ActualSmoothRadialSystemSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients

/-- The literal original source RHS, ordered as (x, xi), with P at m=0. -/
def rawOriginalSourceRHS (length radius : ℝ) (mode : ℤ × ℤ)
    (j c v f g : ComplexEuclidean 1) : ComplexEuclidean 1 × ComplexEuclidean 1 :=
  ((-((length : ℂ)⁻¹)) • (frequencyNumerator (some true) mode • c) -
    (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • v) +
    frequencyNumerator (some false) mode • g,
    (if mode.1 = 0 then (0 : ℂ) else 1) • (j + f))

/-- In the genuine third forcing r*g, reciprocal radius cancels exactly. -/
theorem originalSource_radius_cancel (radius : ℝ) (nonzero : radius ≠ 0)
    (angular : ℂ) (g : ComplexEuclidean 1) :
    (radius : ℂ)⁻¹ • (angular • (radius • g)) = angular • g := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (radius : ℂ)⁻¹ • (angular • ((radius : ℂ) • g)) = angular • g
  rw [smul_comm ((radius : ℂ)⁻¹) angular, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr nonzero)]

/-- Frequency drop, original P, and r*g cancellation are purely scalar. -/
theorem originalSource_frequency_algebra (length radius : ℝ) (nonzero : radius ≠ 0)
    (mode : ℤ × ℤ) (grade : ℕ) (j c v f g : ComplexEuclidean 1) :
    let weight := ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ)
    let next := ((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ)
    ((-((length : ℂ)⁻¹)) • (frequencyRatioSymbol (some true) mode • (next • c)) -
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • (next • v)) +
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • (next • (radius • g))),
      (if mode.1 = 0 then (0 : ℂ) else 1) •
        (frequencyRatioSymbol none mode • (next • j) + weight • f)) =
      weight • rawOriginalSourceRHS length radius mode j c v f g := by
  dsimp only
  rw [frequencyRatio_weighted, frequencyRatio_weighted, frequencyRatio_weighted,
    frequencyRatio_weighted]
  simp only [rawOriginalSourceRHS, Prod.smul_mk, smul_add, smul_sub, frequencyNumerator, one_smul]
  rw [smul_comm (-((length : ℂ)⁻¹)) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ),
    smul_comm ((radius : ℂ)⁻¹) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ),
    smul_comm ((radius : ℂ)⁻¹) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ),
    originalSource_radius_cancel radius nonzero]
  congr 1
  exact congrArg₂ (fun a b : ComplexEuclidean 1 => a + b)
    (smul_comm (if mode.1 = 0 then (0 : ℂ) else 1)
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) j)
    (smul_comm (if mode.1 = 0 then (0 : ℂ) else 1)
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) f)

end Grad.AnnularSmoothCore
