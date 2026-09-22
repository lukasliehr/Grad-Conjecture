import GQ4ComplementRotation

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.GaugeCoefficients.Physical.RadialLedger

theorem apStoredQuarter_exists (L sigma gamma ell : ℝ) (grade : ℕ) :
    ∃ completed : apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade,
      (∀ core, completed (apFiniteInto L sigma gamma ell core) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap (valueMapJetLinear 3 3 storedQuarterMap) core)) ∧
      (∀ field, ‖completed field‖ ≤ ‖field‖) := by
  have bounded : ∀ core : ℤ →₀ ClosedJet 3,
      ‖apFiniteInto (grade := grade) L sigma gamma ell (apFiniteJetMap (valueMapJetLinear 3 3 storedQuarterMap) core)‖ ≤
        1 * ‖apFiniteInto (grade := grade) L sigma gamma ell core‖ := by
    apply apFiniteJetMap_bound L sigma gamma ell _ 1 zero_le_one
    intro cell field
    exact (apValueMap_row_bound L sigma gamma ell cell storedQuarterMap field).trans
      (mul_le_mul_of_nonneg_right storedQuarterMap_norm_le (norm_nonneg _))
  obtain ⟨completed, coreLaw, bound⟩ := apDense_extension (apFiniteInto (grade := grade) L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto (grade := grade) L sigma gamma ell).comp (apFiniteJetMap (valueMapJetLinear 3 3 storedQuarterMap)))
    1 zero_le_one bounded
  exact ⟨completed, coreLaw, fun field => by simpa only [one_mul] using bound field⟩

def apStoredQuarter (L sigma gamma ell : ℝ) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  (apStoredQuarter_exists L sigma gamma ell grade).choose

theorem apStoredQuarter_core (L sigma gamma ell : ℝ) (grade : ℕ) (core : ℤ →₀ ClosedJet 3) :
    apStoredQuarter L sigma gamma ell grade (apFiniteInto L sigma gamma ell core) =
      apFiniteInto L sigma gamma ell (apFiniteJetMap (valueMapJetLinear 3 3 storedQuarterMap) core) :=
  (apStoredQuarter_exists L sigma gamma ell grade).choose_spec.1 core

theorem apStoredQuarter_bound (L sigma gamma ell : ℝ) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    ‖apStoredQuarter L sigma gamma ell grade field‖ ≤ ‖field‖ :=
  (apStoredQuarter_exists L sigma gamma ell grade).choose_spec.2 field

theorem apStoredQuarter_lowering {low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (field : apGrade L sigma gamma ell 3 high) :
    apLowering L sigma gamma ell ordered (apStoredQuarter L sigma gamma ell high field) =
      apStoredQuarter L sigma gamma ell low (apLowering L sigma gamma ell ordered field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp (apStoredQuarter L sigma gamma ell high).continuous)
      ((apStoredQuarter L sigma gamma ell low).continuous.comp (apLowering L sigma gamma ell ordered).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apStoredQuarter_core, apLowering_core, apLowering_core, apStoredQuarter_core]

end Grad.GaugeCoefficients.Physical.GaugeTransfer
