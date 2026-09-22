import GQD1GraphClosure

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

local instance apNormedSpace (dimension grade : ℕ) :
    NormedSpace ℂ (apGrade L sigma gamma ell dimension grade) := inferInstance

local instance graphNormedSpace (grade : ℕ) :
    NormedSpace ℂ (CompensatedGraphAmbient L sigma gamma ell grade) := by
  unfold CompensatedGraphAmbient
  infer_instance

local instance coreGroup (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    AddCommGroup core := inferInstance

local instance coreModule (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    Module ℂ core := inferInstance

def compensatedCoreGraph (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    core →ₗ[ℂ] CompensatedGraphAmbient L sigma gamma ell grade :=
  (compensatedGraphLinear admissible grade).comp core.subtype

/-- The specified original AN8 closure of the actual constrained smooth core. -/
def compensatedClosure (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    Submodule ℂ (CompensatedGraphAmbient L sigma gamma ell grade) :=
  (LinearMap.range (compensatedCoreGraph admissible grade core)).topologicalClosure

instance compensatedClosure_complete (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    CompleteSpace (compensatedClosure admissible grade core) :=
  (LinearMap.range (compensatedCoreGraph admissible grade core)).isClosed_topologicalClosure.completeSpace_coe

def compensatedIntoClosure (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    core →ₗ[ℂ] compensatedClosure admissible grade core :=
  (compensatedCoreGraph admissible grade core).codRestrict _
    (fun point => Submodule.le_topologicalClosure _ ⟨point, rfl⟩)

theorem compensatedIntoClosure_norm (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (data : core) :
    ‖compensatedIntoClosure admissible grade core data‖ = compensatedNorm admissible grade data.val := rfl

theorem compensatedIntoClosure_denseRange (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    DenseRange (compensatedIntoClosure admissible grade core) :=
  coreGraphInto_denseRange (C := core) (E := CompensatedGraphAmbient L sigma gamma ell grade)
    (compensatedCoreGraph admissible grade core)

theorem compensatedGraphLinear_injective (grade : ℕ) :
    Function.Injective (compensatedGraphLinear admissible grade) := by
  intro first second equality
  apply sub_eq_zero.mp
  apply (compensatedNorm_eq_zero_iff admissible grade (first - second)).mp
  change ‖compensatedGraphLinear admissible grade (first - second)‖ = 0
  rw [map_sub, equality, sub_self, norm_zero]

theorem compensatedIntoClosure_injective (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    Function.Injective (compensatedIntoClosure admissible grade core) := by
  intro first second equality
  apply Subtype.ext
  exact compensatedGraphLinear_injective admissible grade (congrArg Subtype.val equality)

abbrev circularCompensatedClosure (grade : ℕ) :=
  compensatedClosure admissible grade (circularCompensatedCore admissible)

abbrev currentCompensatedClosure (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) :=
  compensatedClosure admissible grade (currentCompensatedCore admissible gauge coherent)

end Grad.GaugeCoefficients.Physical.Compensated
