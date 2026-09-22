import AKAW4FullCellPolarEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.PhaseAlgebra Grad.ActualPuncturedReconstruction Grad.PuncturedRetainedEnergy

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

include compatible bounded in
theorem weightedFamilyCurve_agree (first second grade : ℕ) (radius : ℝ)
    (firstInside : radius ∈ Icc (lower first) 1) (secondInside : radius ∈ Icc (lower second) 1) :
    (curves first).curve grade radius = (curves second).curve grade radius := by
  apply Subtype.ext
  funext mode
  have same := congrArg (fun value : CellL2 dimension => value mode)
    (physicalFamilyCurve_agree parameters lower positive bounded decreasing rows curves compatible
      first second grade radius firstInside secondInside)
  rw [(curves first).physicalCurve_coefficient (bounded first) grade radius firstInside mode,
    (curves second).physicalCurve_coefficient (bounded second) grade radius secondInside mode] at same
  exact (smul_right_injective _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')) same

def weightedFamilySections (grade : ℕ) (index : ℕ) : C(Icc (lower index) (1 : ℝ),CellL2 dimension) :=
  ⟨fun radius => (curves index).curve grade radius.val,(curves index).smooth grade |>.continuousOn.domRestrict⟩

def gluedWeightedFamilyCurve (grade : ℕ) : ℝ → CellL2 dimension :=
  gluedClosedSections lower cofinal (weightedFamilySections parameters lower positive rows curves grade)

include compatible bounded in
theorem gluedWeightedFamilyCurve_same (grade index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) :
    gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius = (curves index).curve grade radius :=
  gluedClosedSections_same lower cofinal (weightedFamilySections parameters lower positive rows curves grade) positive
    (fun first second radius one two => weightedFamilyCurve_agree parameters lower positive bounded decreasing rows curves compatible
      first second grade radius one two) index radius inside

include compatible bounded in
theorem gluedWeightedFamilyCurve_continuous (grade : ℕ) :
    ContinuousOn (gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade) (Ioc (0 : ℝ) 1) :=
  gluedClosedSections_continuous lower cofinal (weightedFamilySections parameters lower positive rows curves grade) positive
    (fun first second radius one two => weightedFamilyCurve_agree parameters lower positive bounded decreasing rows curves compatible
      first second grade radius one two) (fun index => (bounded index).le)

include compatible bounded in
/-- The accepted physical Fourier curve is weighted back by the exact phase,
without changing its width or selecting a different representative. -/
theorem gluedWeightedFamilyCurve_physical (grade : ℕ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ × ℤ) :
    gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius mode =
      (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves grade radius mode := by
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  rw [gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible grade index radius localInside,
    gluedPhysicalFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible grade index radius localInside,
    (curves index).physicalCurve_coefficient (bounded index) grade radius localInside mode]
  rw [Real.exp_neg,Complex.ofReal_inv,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]

end Grad.ActualNativeCellMoments
