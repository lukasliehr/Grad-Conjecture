import GQF28CompletedRows

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem hilbert_closed_range {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (source : Set F) (closed : IsClosed source)
    (projection : G →L[ℂ] G) :
    IsClosed {field : WithLp 2 (F × G) | (WithLp.ofLp field).1 ∈ source ∧
      projection (WithLp.ofLp field).2 = (WithLp.ofLp field).2} := by
  have decode : Continuous (WithLp.ofLp : WithLp 2 (F × G) → F × G) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ F G).continuous
  exact (closed.preimage (continuous_fst.comp decode)).inter
    (isClosed_eq (projection.continuous.comp (continuous_snd.comp decode)) (continuous_snd.comp decode))

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

theorem capAugmentedRange_isClosed (grade : ℕ) :
      IsClosed {field : CapAugmentedAmbient L sigma gamma ell grade | capAugmentedRange admissible grade field} :=
  hilbert_closed_range (F := CapSourceAmbient L sigma gamma ell grade)
    (G := APBoundaryGrade L sigma gamma ell 1 (grade + 1)) (capSourceClosure admissible grade)
    (LinearMap.range ((capSourceGrade grade).comp (smoothCapSourceCore admissible).subtype)).isClosed_topologicalClosure
    (apHighProjection L sigma gamma ell (grade + 1))

theorem circularAugmentedCore_range (grade : ℕ) (state : compensatedFlatCore admissible) :
    capAugmentedRange admissible grade (circularAugmentedCore admissible grade state.val) := by
  constructor
  · exact Submodule.le_topologicalClosure _ ⟨⟨circularRows admissible state.val,
      circularRows_source_mem admissible state⟩, rfl⟩
  · exact apHighProjection_idempotent L sigma gamma ell (grade + 1)
      (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (apSmoothGrade L sigma gamma ell 1 (grade + 1)
          (apSmoothRadial admissible (compensatedReconstruct admissible state.val))))

theorem actualAugmentedCore_range (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (state : compensatedFlatCore admissible) :
    capAugmentedRange admissible grade (actualAugmentedCore admissible data coherent grade state.val) := by
  constructor
  · exact Submodule.le_topologicalClosure _ ⟨⟨actualRows admissible data coherent state.val,
      actualRows_source_mem admissible data coherent state⟩, rfl⟩
  · exact apHighProjection_idempotent L sigma gamma ell (grade + 1)
      (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (apSmoothGrade L sigma gamma ell 1 (grade + 1)
          (apSmoothMultiplier admissible (normalRowFamily data) (normalRowFamily_coherent data coherent)
            (compensatedReconstruct admissible state.val))))

theorem completedCircularRows_range (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (flat : core ≤ compensatedFlatCore admissible)
    (field : compensatedClosure admissible grade core) :
    capAugmentedRange admissible grade (completedCircularRows admissible grade core field) := by
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade core)
    ((capAugmentedRange_isClosed admissible grade).preimage (completedCircularRows admissible grade core).continuous) _ field
  intro state
  rw [completedCircularRows_core]
  exact circularAugmentedCore_range admissible grade ⟨state.val, flat state.property⟩

theorem completedCurrentRows_range (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (flat : core ≤ compensatedFlatCore admissible) (field : compensatedClosure admissible grade core) :
    capAugmentedRange admissible grade (completedCurrentRows admissible data coherent grade core field) := by
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade core)
    ((capAugmentedRange_isClosed admissible grade).preimage
      (completedCurrentRows admissible data coherent grade core).continuous) _ field
  intro state
  rw [completedCurrentRows_core]
  exact actualAugmentedCore_range admissible data coherent grade ⟨state.val, flat state.property⟩

end Grad.GaugeCoefficients.Physical.Compensated
