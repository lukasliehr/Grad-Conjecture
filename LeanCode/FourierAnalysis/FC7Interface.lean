import FC7Conjugation

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal BigOperators Topology ComplexConjugate

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The exact FA-COR07 public boundary.  The same literal centered cell
truncation preserves the all-grade core and converges in every fixed original
grade.  Conjugate reflection is an actual real-linear involution of that core,
and an isometry on every grade-tagged norm.  The final clause is the literal
coefficient fixed-point relation used by the later Fourier reconstruction. -/
def CartesianCoreTruncationRealityGoal : Prop :=
  ∀ dimension parameters,
    (∀ (cutoff : ℕ) (field : ACore parameters dimension) (cell : ℤ),
      (cartesianCoreTruncation parameters cutoff field).1 cell =
        if cell.natAbs ≤ cutoff then field.1 cell else 0) ∧
    (∀ (field : ACore parameters dimension) (grade : ℕ),
      Tendsto
        (fun cutoff : ℕ => GradeCore.ofCoreLinear (grade := grade)
          (cartesianCoreTruncation parameters cutoff field))
        atTop (𝓝 (GradeCore.ofCoreLinear (grade := grade) field))) ∧
    Function.Involutive (cartesianCoreConjugation parameters :
      ACore parameters dimension → ACore parameters dimension) ∧
    (∀ (field : ACore parameters dimension) (cell : ℤ)
        (point : ClosedDisk) (coordinate : Fin dimension),
      ((cartesianCoreConjugation parameters field).1 cell).value point coordinate =
        conj ((field.1 (-cell)).value point coordinate)) ∧
    (∀ (cutoff : ℕ) (field : ACore parameters dimension),
      cartesianCoreConjugation parameters
          (cartesianCoreTruncation parameters cutoff field) =
        cartesianCoreTruncation parameters cutoff
          (cartesianCoreConjugation parameters field)) ∧
    ∀ grade,
      (∀ field : GradeCore parameters dimension grade,
        ‖gradeCoreConjugation parameters field‖ = ‖field‖) ∧
      Function.Involutive (gradeCoreConjugation parameters :
        GradeCore parameters dimension grade →
          GradeCore parameters dimension grade) ∧
      ∀ field : GradeCore parameters dimension grade,
        gradeCoreConjugation parameters field = field ↔
          ∀ (cell : ℤ) (point : ClosedDisk) (coordinate : Fin dimension),
            conj ((field.toCore.1 (-cell)).value point coordinate) =
              (field.toCore.1 cell).value point coordinate

end Grad.CartesianState
