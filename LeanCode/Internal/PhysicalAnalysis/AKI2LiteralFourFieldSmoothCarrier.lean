import AKI1OriginalWeightedRadialGrades
import SCS39DoubleCoefficientAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
open scoped ContDiff BigOperators Topology
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarDivision
open Grad.SourceCollarFullSource Grad.AnnularClosedJointRegularity

abbrev OriginalPhysicalField := (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1

def originalPhysicalCoefficient (field : OriginalPhysicalField) : AnnularCoefficient :=
  fun radius mode => angularCoefficient (fun axial => angularCoefficient
    (fun polar => field (radius, polar, axial)) mode.1) mode.2

def OriginalPhysicalClosedSmooth (lower : ℝ) (field : OriginalPhysicalField) : Prop :=
  ContDiffOn ℝ ∞ field (annularJointClosed lower) ∧
    (∀ radius axial, Function.Periodic (fun polar => field (radius, polar, axial)) (2 * Real.pi)) ∧
    ∀ radius polar, Function.Periodic (fun axial => field (radius, polar, axial)) (2 * Real.pi)

theorem OriginalPhysicalClosedSmooth.slice {lower : ℝ} {field : OriginalPhysicalField}
    (smooth : OriginalPhysicalClosedSmooth lower field) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (fun angles : ℝ × ℝ => field (radius, angles)) := by
  rw [← continuousOn_univ]
  exact smooth.1.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨inside, mem_univ _⟩)

theorem originalPhysicalCoefficient_add {lower : ℝ} {first second : OriginalPhysicalField}
    (firstSmooth : OriginalPhysicalClosedSmooth lower first)
    (secondSmooth : OriginalPhysicalClosedSmooth lower second) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    originalPhysicalCoefficient (first + second) radius mode =
      originalPhysicalCoefficient first radius mode + originalPhysicalCoefficient second radius mode := by
  exact doubleCoefficient_add (fun angles => first (radius, angles.2, angles.1))
    (fun angles => second (radius, angles.2, angles.1))
    ((firstSmooth.slice radius inside).comp continuous_swap)
    ((secondSmooth.slice radius inside).comp continuous_swap) mode.swap

theorem originalPhysicalCoefficient_smul (scalar : ℂ) (field : OriginalPhysicalField)
    (radius : ℝ) (mode : ℤ × ℤ) :
    originalPhysicalCoefficient (scalar • field) radius mode =
      scalar • originalPhysicalCoefficient field radius mode := by
  unfold originalPhysicalCoefficient
  simp only [Pi.smul_apply]
  have inner (axial : ℝ) :
      angularCoefficient (fun polar => scalar • field (radius, polar, axial)) mode.1 =
        scalar • angularCoefficient (fun polar => field (radius, polar, axial)) mode.1 :=
    angularCoefficient_smul_continuous scalar (fun polar => field (radius, polar, axial)) mode.1
  simp_rw [inner]
  exact angularCoefficient_smul_continuous scalar _ mode.2

/-- Smooth original physical field with the full original analytic phase
and every closed radial/tangential grade. -/
def OriginalWeightedPhysicalSmooth (parameters : PhaseParameters) (lower : ℝ)
    (field : OriginalPhysicalField) : Prop :=
  OriginalPhysicalClosedSmooth lower field ∧
    PhaseWeightedRadialSmooth parameters lower (originalPhysicalCoefficient field)

theorem originalWeightedPhysicalSmooth_zero (parameters : PhaseParameters) (lower : ℝ) :
    OriginalWeightedPhysicalSmooth parameters lower 0 := by
  constructor
  · exact ⟨contDiffOn_const, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · have zeroCoefficient : originalPhysicalCoefficient 0 = 0 := by
      funext radius mode
      simp [originalPhysicalCoefficient, angularCoefficient_zero]
    rw [zeroCoefficient]
    exact phaseWeightedRadialSmooth_zero parameters lower

theorem OriginalWeightedPhysicalSmooth.add {parameters : PhaseParameters} {lower : ℝ}
    {first second : OriginalPhysicalField} (firstSmooth : OriginalWeightedPhysicalSmooth parameters lower first)
    (secondSmooth : OriginalWeightedPhysicalSmooth parameters lower second) :
    OriginalWeightedPhysicalSmooth parameters lower (first + second) := by
  constructor
  · exact ⟨firstSmooth.1.1.add secondSmooth.1.1,
      fun radius axial => (firstSmooth.1.2.1 radius axial).add (secondSmooth.1.2.1 radius axial),
      fun radius polar => (firstSmooth.1.2.2 radius polar).add (secondSmooth.1.2.2 radius polar)⟩
  · obtain ⟨curve, regular, same⟩ := firstSmooth.2.add secondSmooth.2
    refine ⟨curve, regular, ?_⟩
    intro grade radius inside mode
    rw [originalPhysicalCoefficient_add firstSmooth.1 secondSmooth.1 radius inside]
    exact same grade radius inside mode

theorem OriginalWeightedPhysicalSmooth.smul {parameters : PhaseParameters} {lower : ℝ}
    {field : OriginalPhysicalField} (smooth : OriginalWeightedPhysicalSmooth parameters lower field)
    (scalar : ℂ) : OriginalWeightedPhysicalSmooth parameters lower (scalar • field) := by
  constructor
  · refine ⟨smooth.1.1.const_smul scalar, ?_, ?_⟩
    · intro radius axial polar
      change scalar • field (radius, polar + 2 * Real.pi, axial) = scalar • field (radius, polar, axial)
      exact congrArg (fun value => scalar • value) (smooth.1.2.1 radius axial polar)
    · intro radius polar axial
      change scalar • field (radius, polar, axial + 2 * Real.pi) = scalar • field (radius, polar, axial)
      exact congrArg (fun value => scalar • value) (smooth.1.2.2 radius polar axial)
  · have same : originalPhysicalCoefficient (scalar • field) = scalar • originalPhysicalCoefficient field := by
      funext radius mode
      exact originalPhysicalCoefficient_smul scalar field radius mode
    rw [same]
    exact smooth.2.smul scalar

/-- Slots are exactly p, xi, full F0, and F2. Residuals and traces are not
coordinates of this linear core carrier. -/
def originalSmoothTupleSpace (parameters : PhaseParameters) (lower : ℝ) :
    Submodule ℂ (Fin 4 → OriginalPhysicalField) where
  carrier := fun fields => (∀ slot, OriginalWeightedPhysicalSmooth parameters lower (fields slot)) ∧
    ∀ slot, slot ≠ 2 → ∀ radius, radius ∈ Icc lower 1 → ∀ cell,
      originalPhysicalCoefficient (fields slot) radius (0, cell) = 0
  zero_mem' := by
    refine ⟨fun _ => originalWeightedPhysicalSmooth_zero parameters lower, ?_⟩
    intro slot _ radius _ cell
    simp [originalPhysicalCoefficient, angularCoefficient_zero]
  add_mem' := by
    intro first second firstMember secondMember
    refine ⟨fun slot => (firstMember.1 slot).add (secondMember.1 slot), ?_⟩
    intro slot meanFree radius inside cell
    change originalPhysicalCoefficient (first slot + second slot) radius (0, cell) = 0
    rw [originalPhysicalCoefficient_add (firstMember.1 slot).1 (secondMember.1 slot).1 radius inside,
      firstMember.2 slot meanFree radius inside cell, secondMember.2 slot meanFree radius inside cell, add_zero]
  smul_mem' := by
    intro scalar field member
    refine ⟨fun slot => (member.1 slot).smul scalar, ?_⟩
    intro slot meanFree radius inside cell
    change originalPhysicalCoefficient (scalar • field slot) radius (0, cell) = 0
    rw [originalPhysicalCoefficient_smul, member.2 slot meanFree radius inside cell, smul_zero]

abbrev OriginalSmoothTuple (parameters : PhaseParameters) (lower : ℝ) :=
  originalSmoothTupleSpace parameters lower

end Grad.AnnularOriginalSmoothCore
