import GC18APFourier
import GC18CMapComplement

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.NonlinearQuotientBounds

theorem apComplement_physical_core {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (core : ℤ →₀ ClosedJet 3) :
    apPhysicalValue admissible large angle (apComplement L sigma gamma ell grade (apFiniteInto L sigma gamma ell core)) =
      cMapComplement (apPhysicalValue admissible large angle (apFiniteInto L sigma gamma ell core)) := by
  rw [apComplement_core]
  have first := apPhysicalValue_hasSum admissible large angle
    (apFiniteInto L sigma gamma ell (apFiniteJetMap fixedComplementJet core))
  have second := cMapComplement.hasSum (apPhysicalValue_hasSum admissible large angle
    (apFiniteInto L sigma gamma ell core))
  apply first.unique
  apply second.congr_fun
  intro cell
  rw [map_smul, apTrace_core, apTrace_core, cMapComplement_jet]
  rfl

theorem apComplement_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) :
    apPhysicalValue admissible large angle (apComplement L sigma gamma ell grade field) =
      cMapComplement (apPhysicalValue admissible large angle field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((apPhysicalValue admissible large angle).continuous.comp (apComplement L sigma gamma ell grade).continuous)
      (cMapComplement.continuous.comp (apPhysicalValue admissible large angle).continuous)) _ field
  intro core
  exact apComplement_physical_core admissible large angle core

theorem apComplementRange_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell 3 grade) :
    field ∈ apComplementRange L sigma gamma ell grade ↔
      ∀ angle : ℝ, apPhysicalValue admissible large angle field ∈ cartesianPhysicalRange := by
  rw [apComplementRange_mem_iff]
  constructor
  · intro fixed angle
    apply (mem_cartesianPhysicalRange_iff _).mpr
    rw [← cMapComplement_apply, ← apComplement_physical, fixed]
  · intro member
    apply apPhysicalValue_ext admissible large
    intro angle
    rw [apComplement_physical, cMapComplement_apply]
    exact (mem_cartesianPhysicalRange_iff _).mp (member angle)

end Grad.GaugeCoefficients.Physical.RadialLedger
