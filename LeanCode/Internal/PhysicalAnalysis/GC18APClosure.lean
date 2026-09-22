import GC18APCoreProduct

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apAmbientMultiplier_mem_core {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : smoothCore L sigma gamma ell grade inputDimension outputDimension)
    (field : apSmoothCore L sigma gamma ell inputDimension grade) :
    apAmbientMultiplier admissible coefficient.val field.val ∈ apSmoothCore L sigma gamma ell outputDimension grade := by
  let target := apSmoothCore L sigma gamma ell outputDimension grade
  let bilinear := apAmbientBilinear admissible inputDimension outputDimension grade
  change bilinear coefficient.val field.val ∈ target
  refine Submodule.span_induction₂ (p := fun coefficient field _ _ => bilinear coefficient field ∈ target)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ coefficient.property field.property
  · intro coefficient field coefficientMember fieldMember
    rcases coefficientMember with ⟨⟨shift, coefficient⟩, rfl⟩
    rcases fieldMember with ⟨⟨input, field⟩, rfl⟩
    change apAmbientMultiplier admissible _ _ ∈ target
    rw [apAmbientMultiplier_core]
    exact Submodule.subset_span (Set.mem_range.mpr ⟨(input + shift, apProductJet coefficient field), rfl⟩)
  · intro field _
    rw [map_zero, zero_apply]
    exact target.zero_mem
  · intro coefficient _
    rw [map_zero]
    exact target.zero_mem
  · intro first second field _ _ _ firstMember secondMember
    rw [map_add, add_apply]
    exact target.add_mem firstMember secondMember
  · intro coefficient first second _ _ _ firstMember secondMember
    rw [map_add]
    exact target.add_mem firstMember secondMember
  · intro scalar coefficient field _ _ member
    rw [map_smul, smul_apply]
    exact target.smul_mem scalar member
  · intro scalar coefficient field _ _ member
    rw [map_smul]
    exact target.smul_mem scalar member

theorem apAmbientMultiplier_coefficient_closure {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (field : apSmoothCore L sigma gamma ell inputDimension grade) :
    apAmbientMultiplier admissible coefficient.val field.val ∈ apGrade L sigma gamma ell outputDimension grade := by
  let source := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let target := apSmoothCore L sigma gamma ell outputDimension grade
  let mapping : WeightedAmbient grade inputDimension outputDimension →L[ℂ] APAmbient outputDimension grade :=
    (ContinuousLinearMap.apply ℂ (APAmbient outputDimension grade) field.val).comp
      (apAmbientBilinear admissible inputDimension outputDimension grade)
  have maps : source.map mapping.toLinearMap ≤ target := by
    rintro _ ⟨input, member, rfl⟩
    exact apAmbientMultiplier_mem_core admissible ⟨input, member⟩ field
  exact (Submodule.topologicalClosure_mono maps)
    ((source.topologicalClosure_map mapping) ⟨coefficient.val, coefficient.property, rfl⟩)

theorem apAmbientMultiplier_closure {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (field : apGrade L sigma gamma ell inputDimension grade) :
    apAmbientMultiplier admissible coefficient.val field.val ∈ apGrade L sigma gamma ell outputDimension grade := by
  let source := apSmoothCore L sigma gamma ell inputDimension grade
  let target := apSmoothCore L sigma gamma ell outputDimension grade
  let mapping := apAmbientMultiplier admissible coefficient.val
  have maps : source.map mapping.toLinearMap ≤ target.topologicalClosure := by
    rintro _ ⟨input, member, rfl⟩
    exact apAmbientMultiplier_coefficient_closure admissible coefficient ⟨input, member⟩
  have member := (Submodule.topologicalClosure_mono maps)
    ((source.topologicalClosure_map mapping) ⟨field.val, field.property, rfl⟩)
  rw [target.isClosed_topologicalClosure.submodule_topologicalClosure_eq] at member
  exact member

/-- The literal AP2 completed multiplication, obtained by restricting the
actual derivative-array product, with no projection or substituted norm. -/
def apMultiplier {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) :
    apGrade L sigma gamma ell inputDimension grade →L[ℂ] apGrade L sigma gamma ell outputDimension grade :=
  ((apAmbientMultiplier admissible coefficient.val).comp
    (apGrade L sigma gamma ell inputDimension grade).subtypeL).codRestrict
      (apGrade L sigma gamma ell outputDimension grade) (apAmbientMultiplier_closure admissible coefficient)

theorem apMultiplier_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (field : apGrade L sigma gamma ell inputDimension grade) :
    ‖apMultiplier admissible coefficient field‖ ≤ apMultiplierConstant L sigma gamma grade * ‖coefficient‖ * ‖field‖ :=
  apAmbientMultiplier_apply_bound admissible coefficient.val field.val

theorem apCoreInclusion_denseRange (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    DenseRange (apCoreInclusion L sigma gamma ell dimension grade) := by
  change DenseRange (Set.inclusion (Submodule.le_topologicalClosure (apSmoothCore L sigma gamma ell dimension grade)))
  apply (denseRange_inclusion_iff _).2
  intro point member
  exact member

end Grad.GaugeCoefficients.Physical.RadialLedger
