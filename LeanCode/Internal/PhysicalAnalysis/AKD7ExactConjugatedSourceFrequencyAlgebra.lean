import AKD6SameConjugatedKnownPhysicalRows
import AJQ2ActualKnownSourceRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.SourceCollarCoefficients

theorem rawOriginalSourceRHS_smul (length radius : ℝ) (mode : ℤ × ℤ)
    (scalar : ℂ) (j c v f g : ComplexEuclidean 1) :
    rawOriginalSourceRHS length radius mode (scalar • j) (scalar • c) (scalar • v) (scalar • f) (scalar • g) =
      scalar • rawOriginalSourceRHS length radius mode j c v f g := by
  apply Prod.ext <;> apply PiLp.ext <;> intro entry
  · simp only [rawOriginalSourceRHS, Prod.smul_mk, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [rawOriginalSourceRHS, Prod.smul_mk, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

/-- The same original source algebra after inserting the common original
phase at the SAME radius. P and the positive Rg term remain literal. -/
theorem conjugatedSourceFrequency_ae (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (grade : ℕ)
    (row raw : Fin 3 → ℝ → (ℤ × ℤ) → ComplexEuclidean 1)
    (f g3 rawF rawG : ℝ → (ℤ × ℤ) → ComplexEuclidean 1)
    (rowSame : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      row index radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • raw index radius mode))
    (fSame : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      f radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ grade •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • rawF radius mode))
    (gSame : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      g3 radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • (radius • rawG radius mode))) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      ((-((length : ℂ)⁻¹)) • (frequencyRatioSymbol (some true) mode • row 1 radius mode) -
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2 radius mode) +
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • g3 radius mode),
        (if mode.1 = 0 then (0 : ℂ) else 1) •
          (frequencyRatioSymbol none mode • row 0 radius mode + f radius mode)) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          rawOriginalSourceRHS length radius mode (raw 0 radius mode) (raw 1 radius mode)
            (raw 2 radius mode) (rawF radius mode) (rawG radius mode)) := by
  have radiusSame : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      g3 radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) •
        (radius • ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • rawG radius mode)) := by
    filter_upwards [gSame] with radius same
    intro mode
    exact (same mode).trans (congrArg
      (fun value : ComplexEuclidean 1 => (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) • value)
      (smul_comm _ radius _))
  have actual := sourceFrequency_ae length lower positive grade row
    (fun index radius mode => (Real.exp (radialPhase parameters radius mode.2) : ℂ) • raw index radius mode)
    f g3 (fun radius mode => (Real.exp (radialPhase parameters radius mode.2) : ℂ) • rawF radius mode)
    (fun radius mode => (Real.exp (radialPhase parameters radius mode.2) : ℂ) • rawG radius mode)
    rowSame fSame radiusSame
  filter_upwards [actual] with radius actual
  intro mode
  rw [actual mode, rawOriginalSourceRHS_smul]

end Grad.AnnularSmoothCore
