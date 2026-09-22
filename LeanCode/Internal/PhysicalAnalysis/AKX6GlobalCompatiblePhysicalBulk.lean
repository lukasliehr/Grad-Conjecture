import AKX5ActualPhysicalBulkEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators
namespace Grad.ActualPuncturedReconstruction
open Grad.SourceCollarDivision Grad.AnnularIncomingIntegrability Grad.AnnularRestriction
open Grad.PuncturedRetainedEnergy

variable (dimension : ℕ) (collars : ℕ → ℝ)
    (fields : ∀ index, DivisionRow dimension (collars index))

/-- The actual weighted bulk square, glued by almost-everywhere restriction. -/
def globalPhysicalBulkSquare : ℝ → ℝ≥0∞ :=
  cofinalIncomingSquare 1 collars (fun index => physicalBulkSquare dimension (collars index) (fields index))

def globalPhysicalBulkEnergy : ℝ≥0∞ :=
  ∫⁻ radius, globalPhysicalBulkSquare dimension collars fields radius ∂volume.restrict (Ioc 0 1)

variable (decreasing : Antitone collars)
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (collars second) (collars first) (decreasing ordered) (fields second) = fields first)
include compatible

theorem physicalBulkSquares_overlap (first second : ℕ) :
    physicalBulkSquare dimension (collars first) (fields first) =ᵐ[volume.restrict (Icc (max (collars first) (collars second)) 1)]
      physicalBulkSquare dimension (collars second) (fields second) := by
  rcases le_total first second with ordered | ordered
  · simpa only [max_eq_left (decreasing ordered),compatible first second ordered] using
      physicalBulkSquare_restriction dimension (collars second) (collars first) (decreasing ordered) (fields second)
  · simpa only [max_eq_right (decreasing ordered),compatible second first ordered] using
      (physicalBulkSquare_restriction dimension (collars first) (collars second) (decreasing ordered) (fields first)).symm

theorem globalPhysicalBulkSquare_same (index : ℕ) :
    globalPhysicalBulkSquare dimension collars fields =ᵐ[volume.restrict (Icc (collars index) 1)]
      physicalBulkSquare dimension (collars index) (fields index) :=
  cofinalSquare_same_ae 1 collars _ (physicalBulkSquares_overlap dimension collars fields decreasing compatible) index

theorem globalPhysicalBulkEnergy_on_collar (index : ℕ) :
    (∫⁻ radius, globalPhysicalBulkSquare dimension collars fields radius ∂volume.restrict (Icc (collars index) 1)) =
      ENNReal.ofReal (‖fields index‖ ^ 2) :=
  (lintegral_congr_ae (globalPhysicalBulkSquare_same dimension collars fields decreasing compatible index)).trans
    (physicalBulkSquare_integral dimension (collars index) (fields index))

variable (positive : ∀ index, 0 < collars index) (cofinal : Tendsto collars atTop (𝓝 0))
include positive cofinal

/-- A single punctured-disk integral, exactly the supremum of its collar
energies. No overlapping collar norms are added. -/
theorem globalPhysicalBulkEnergy_eq_iSup :
    globalPhysicalBulkEnergy dimension collars fields = ⨆ index, ENNReal.ofReal (‖fields index‖ ^ 2) := by
  have identity := cofinalEnergy_eq_iSup 1 collars positive decreasing cofinal
    (globalPhysicalBulkSquare dimension collars fields) 0
  simpa only [globalPhysicalBulkEnergy,add_zero,globalPhysicalBulkEnergy_on_collar dimension collars fields decreasing compatible] using identity

theorem globalPhysicalBulkEnergy_bound (constant : ℝ) (estimate : ∀ index, ‖fields index‖ ≤ constant) :
    globalPhysicalBulkEnergy dimension collars fields ≤ ENNReal.ofReal (constant ^ 2) := by
  rw [globalPhysicalBulkEnergy_eq_iSup dimension collars fields decreasing compatible positive cofinal]
  apply iSup_le
  intro index
  exact ENNReal.ofReal_le_ofReal (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (estimate index)) |>.mpr (estimate index))

theorem globalPhysicalBulkEnergy_finite (constant : ℝ) (estimate : ∀ index, ‖fields index‖ ≤ constant) :
    globalPhysicalBulkEnergy dimension collars fields < ⊤ :=
  (globalPhysicalBulkEnergy_bound dimension collars fields decreasing compatible positive cofinal constant estimate).trans_lt
    ENNReal.ofReal_lt_top

end Grad.ActualPuncturedReconstruction
