import JRConsumer
import WTCSmooth
import MK1Construction
import Mathlib.Data.Nat.Choose.Sum

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

def scalarDerivative (index : ℕ × ℕ) (scalar : Spatial → ℝ) : Spatial → ℝ :=
  Grad.WeakTesting.orderedTestDerivative (index.1 + index.2)
    (Grad.WeakTesting.Commutation.canonicalWord index.1 index.2) scalar

theorem scalarDerivative_eq {order : ℕ} (index : JetIndex order) (scalar : Spatial → ℝ) :
    scalarDerivative index.val scalar =
      Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) scalar := rfl

theorem scalarDerivative_zero (scalar : Spatial → ℝ) :
    scalarDerivative (0, 0) scalar = scalar := rfl

theorem scalarDerivative_smooth (index : ℕ × ℕ) (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) :
    ContDiff ℝ ∞ (scalarDerivative index scalar) := by
  rw [scalarDerivative, ← Grad.WeakTesting.Commutation.listDerivative_ofFn _ _ _ smoothness]
  exact Grad.WeakTesting.Commutation.listDerivative_contDiff _ _ smoothness

structure BoundedScalar (domain : Set Spatial) where
  toFun : Spatial → ℝ
  smooth : ContDiff ℝ ∞ toFun
  bound : NNReal
  bound_on : ∀ point ∈ domain, |toFun point| ≤ bound

structure Symbol (order : ℕ) (domain : Set Spatial) where
  toFun : Spatial → ℝ
  smooth : ContDiff ℝ ∞ toFun
  bound : JetIndex order → NNReal
  derivative_bound : ∀ (index : JetIndex order) (point : Spatial), point ∈ domain →
    |scalarDerivative index.val toFun point| ≤ bound index

def derivativeScalar {order : ℕ} {domain : Set Spatial}
    (symbol : Symbol order domain) (index : JetIndex order) : BoundedScalar domain where
  toFun := scalarDerivative index.val symbol.toFun
  smooth := scalarDerivative_smooth index.val symbol.toFun symbol.smooth
  bound := symbol.bound index
  bound_on := symbol.derivative_bound index

def scalarCoefficient (dimension : ℕ) (scalar : Spatial → ℝ) (point : Spatial) :
    CellValues dimension →L[ℂ] CellValues dimension :=
  (scalar point : ℂ) • ContinuousLinearMap.id ℂ (CellValues dimension)

theorem scalarCoefficient_measurable (dimension : ℕ) (domain : Set Spatial)
    (scalar : BoundedScalar domain) :
    AEStronglyMeasurable (scalarCoefficient dimension scalar.toFun) (volume.restrict domain) := by
  exact ((Complex.continuous_ofReal.comp scalar.smooth.continuous).smul
    continuous_const).aestronglyMeasurable

theorem scalarCoefficient_bound (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : BoundedScalar domain) :
    ∀ᵐ point ∂volume.restrict domain,
      ‖scalarCoefficient dimension scalar.toFun point‖ ≤ scalar.bound := by
  filter_upwards [ae_restrict_mem openDomain.measurableSet] with point membership
  calc
    ‖scalarCoefficient dimension scalar.toFun point‖ ≤ |scalar.toFun point| * 1 := by
      rw [scalarCoefficient, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
    _ ≤ scalar.bound := by simpa only [mul_one] using scalar.bound_on point membership

def fieldMultiplier (dimension : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : BoundedScalar domain) : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain :=
  Grad.MatrixMultiplier.matrixMultiplier (volume.restrict domain)
    (scalarCoefficient dimension scalar.toFun) scalar.bound
    (scalarCoefficient_measurable dimension domain scalar)
    (scalarCoefficient_bound dimension domain openDomain scalar)

def multiplyTest {domain : Set Spatial} (scalar : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ scalar) (test : TestFunction domain) : TestFunction domain where
  toFun := fun point => scalar point * test.toFun point
  smooth := smoothness.mul test.smooth
  compact := test.compact.mul_left
  supported := tsupport_mul_subset_right.trans test.supported

def indexLE {order : ℕ} (lower upper : JetIndex order) : Prop :=
  lower.val.1 ≤ upper.val.1 ∧ lower.val.2 ≤ upper.val.2

def below {order : ℕ} (index : JetIndex order) : Finset (JetIndex order) := by
  classical
  exact Finset.univ.filter (fun lower => indexLE lower index)

def difference {order : ℕ} (upper lower : JetIndex order) : JetIndex order :=
  ⟨(upper.val.1 - lower.val.1, upper.val.2 - lower.val.2),
    (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _)).trans upper.property⟩

def binomial {order : ℕ} (upper lower : JetIndex order) : ℕ :=
  upper.val.1.choose lower.val.1 * upper.val.2.choose lower.val.2

def ExponentAntitone {order : ℕ} (exponent : JetIndex order → ℕ) : Prop :=
  ∀ lower upper, indexLE lower upper → exponent upper ≤ exponent lower

def coordinateMultiplier (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain)
    (exponent : JetIndex order → ℕ) (upper : JetIndex order) :
    JetTuple dimension order domain →L[ℂ] FieldL2 dimension domain :=
  ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
    (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))).comp
      ((Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper)).comp
        (coordinate dimension order domain lower))

def tupleMultiplier (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain)
    (exponent : JetIndex order → ℕ) :
    JetTuple dimension order domain →L[ℂ] JetTuple dimension order domain :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : JetIndex order => FieldL2 dimension domain)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (coordinateMultiplier dimension order domain openDomain symbol exponent))

def unweightedCoordinate (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain)
    (exponent : JetIndex order → ℕ) (upper : JetIndex order) :
    WJet dimension order domain exponent →L[ℂ] FieldL2 dimension domain :=
  ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
    (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))).comp
      (Realization.recoveredDerivative dimension order domain exponent lower)

def matrixEntry {order : ℕ} {domain : Set Spatial} (symbol : Symbol order domain)
    (upper lower : JetIndex order) : ℝ := by
  classical
  exact if indexLE lower upper then
    (binomial upper lower : ℝ) * symbol.bound (difference upper lower) else 0

def rowBound {order : ℕ} {domain : Set Spatial} (symbol : Symbol order domain)
    (upper : JetIndex order) : ℝ :=
  ∑ lower, matrixEntry symbol upper lower

def matrixBound {order : ℕ} {domain : Set Spatial} (symbol : Symbol order domain) : ℝ :=
  Real.sqrt (∑ upper, (rowBound symbol upper) ^ 2)

def FieldGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : BoundedScalar domain),
    ‖fieldMultiplier dimension domain openDomain scalar‖ ≤ scalar.bound ∧
    (∀ field : FieldL2 dimension domain,
      ‖fieldMultiplier dimension domain openDomain scalar field‖ ≤ scalar.bound * ‖field‖ ∧
      (∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
        fieldMultiplier dimension domain openDomain scalar field point cell =
          (scalar.toFun point : ℂ) • field point cell)) ∧
    (∀ (field : FieldL2 dimension domain) (cell : ℤ) (vector : PhysicalValue dimension)
      (test : TestFunction domain),
      testPairing dimension domain cell vector test
          (fieldMultiplier dimension domain openDomain scalar field) =
        testPairing dimension domain cell vector (multiplyTest scalar.toFun scalar.smooth test) field) ∧
    (∀ weight : ℕ,
      (fieldMultiplier dimension domain openDomain scalar).comp
          (Grad.CellWeights.inverseFieldCLM dimension domain weight) =
        (Grad.CellWeights.inverseFieldCLM dimension domain weight).comp
          (fieldMultiplier dimension domain openDomain scalar))

open Classical in
def ScalarLeibnizGoal : Prop :=
  (∀ (first second : ℕ × ℕ) (scalar : Spatial → ℝ), ContDiff ℝ ∞ scalar →
    scalarDerivative first (scalarDerivative second scalar) =
      scalarDerivative (first.1 + second.1, first.2 + second.2) scalar) ∧
  (∀ (order : ℕ) (upper : JetIndex order) (first second : Spatial → ℝ),
    ContDiff ℝ ∞ first → ContDiff ℝ ∞ second → ∀ point : Spatial,
      scalarDerivative upper.val (fun point => first point * second point) point =
        ∑ lower ∈ below upper, (binomial upper lower : ℝ) *
          scalarDerivative (difference upper lower).val first point *
          scalarDerivative lower.val second point) ∧
  (∀ (order : ℕ) (upper retained : JetIndex order),
    (∑ lower ∈ below upper, if indexLE retained lower then
      (-1 : ℝ) ^ degree lower * binomial upper lower * binomial lower retained else 0) =
        if retained = upper then (-1 : ℝ) ^ degree upper else 0) ∧
  (∀ (order : ℕ) (upper : JetIndex order) (scalar test : Spatial → ℝ),
    ContDiff ℝ ∞ scalar → ContDiff ℝ ∞ test → ∀ point : Spatial,
      (∑ lower ∈ below upper, (-1 : ℝ) ^ degree lower * binomial upper lower *
        scalarDerivative lower.val
          (fun point => scalarDerivative (difference upper lower).val scalar point * test point) point) =
      (-1 : ℝ) ^ degree upper * scalar point * scalarDerivative upper.val test point)

def WeakLeibnizGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (upper : JetIndex order) (jet : WJet dimension order domain exponent),
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain (degree upper)
      (derivativeWord upper)
      (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
        (base dimension order domain exponent jet))
      (unweightedCoordinate dimension order domain openDomain symbol exponent upper jet) ∧
    (∀ (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
      (∫ point in domain, test.toFun point • inner ℂ vector
        (unweightedCoordinate dimension order domain openDomain symbol exponent upper jet point cell)) =
      (-1 : ℂ) ^ degree upper * ∫ point in domain,
        scalarDerivative upper.val test.toFun point • inner ℂ vector
          (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
            (base dimension order domain exponent jet) point cell))

def TupleGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ),
    (∀ (tuple : JetTuple dimension order domain) (upper : JetIndex order),
      tupleMultiplier dimension order domain openDomain symbol exponent tuple upper =
        ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
          fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
            (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper)
              (tuple lower))) ∧
    (∀ tuple : JetTuple dimension order domain,
      ‖tupleMultiplier dimension order domain openDomain symbol exponent tuple‖ ^ 2 =
        ∑ upper, ‖coordinateMultiplier dimension order domain openDomain symbol exponent upper tuple‖ ^ 2) ∧
    (∀ upper lower : JetIndex order, 0 ≤ matrixEntry symbol upper lower) ∧
    (∀ (tuple : JetTuple dimension order domain) (upper : JetIndex order),
      ‖coordinateMultiplier dimension order domain openDomain symbol exponent upper tuple‖ ≤
        rowBound symbol upper * ‖tuple‖) ∧
    ‖tupleMultiplier dimension order domain openDomain symbol exponent‖ ≤ matrixBound symbol

def GraphGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ),
    ExponentAntitone exponent → ∀ jet : WJet dimension order domain exponent,
      tupleMultiplier dimension order domain openDomain symbol exponent jet.val ∈
        jetGraph dimension order domain exponent ∧
      (∀ upper : JetIndex order,
        Grad.CellWeights.inverseFieldCLM dimension domain (exponent upper)
          (tupleMultiplier dimension order domain openDomain symbol exponent jet.val upper) =
        unweightedCoordinate dimension order domain openDomain symbol exponent upper jet)

def JetMultiplierLaws (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (operator : WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent) : Prop :=
  ((jetGraph dimension order domain exponent).subtypeL.comp operator =
    (tupleMultiplier dimension order domain openDomain symbol exponent).comp
      (jetGraph dimension order domain exponent).subtypeL) ∧
  ‖operator‖ ≤ matrixBound symbol ∧
  (base dimension order domain exponent).comp operator =
    (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))).comp
      (base dimension order domain exponent) ∧
  (∀ jet : WJet dimension order domain exponent,
    ‖operator jet‖ ^ 2 =
      ∑ upper, ‖coordinateMultiplier dimension order domain openDomain symbol exponent upper jet.val‖ ^ 2) ∧
  (∀ (jet : WJet dimension order domain exponent) (upper : JetIndex order),
    Realization.recoveredDerivative dimension order domain exponent upper (operator jet) =
      unweightedCoordinate dimension order domain openDomain symbol exponent upper jet ∧
    (∀ (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
      testPairing dimension domain cell vector test
          (Realization.recoveredDerivative dimension order domain exponent upper (operator jet)) =
        (-1 : ℂ) ^ degree upper * derivativeTestPairing dimension order domain upper cell vector test
          (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
            (base dimension order domain exponent jet)))) ∧
  (∀ jet : WJet dimension order domain exponent,
    ∀ᵐ point ∂volume.restrict domain, ∀ (upper : JetIndex order) (cell : ℤ),
      (operator jet).val upper point cell =
        ∑ lower ∈ below upper, ((binomial upper lower : ℂ) *
          (scalarDerivative (difference upper lower).val symbol.toFun point : ℂ) *
          Grad.CellWeights.inverseFactor (exponent lower - exponent upper) cell) •
          jet.val lower point cell)

def JetGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ), ExponentAntitone exponent →
    ∃ operator : WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent,
      JetMultiplierLaws dimension order domain openDomain symbol exponent operator

def GradeGoal : Prop :=
  (∀ (dimension order weight : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain),
    ∃ operator : GraphGrade dimension order weight domain →L[ℂ] GraphGrade dimension order weight domain,
      JetMultiplierLaws dimension order domain openDomain symbol (fun _ => weight) operator) ∧
  (∀ (dimension grade : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol grade domain),
    ∃ operator : Mixed dimension grade domain →L[ℂ] Mixed dimension grade domain,
      JetMultiplierLaws dimension grade domain openDomain symbol (fun index => grade - degree index) operator)

def CompactGoal : Prop :=
  ∀ (order : ℕ) (domain : Set Spatial) (scalar : Spatial → ℝ),
    ContDiff ℝ ∞ scalar → HasCompactSupport scalar →
      ∃ symbol : Symbol order domain, symbol.toFun = scalar ∧
        (∀ (dimension : ℕ) (openDomain : IsOpen domain) (exponent : JetIndex order → ℕ),
          ExponentAntitone exponent →
          ∃ operator : WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent,
            JetMultiplierLaws dimension order domain openDomain symbol exponent operator)

def BlockGoal : Prop :=
  FieldGoal ∧ ScalarLeibnizGoal ∧ WeakLeibnizGoal ∧ TupleGoal ∧ GraphGoal ∧
    JetGoal ∧ GradeGoal ∧ CompactGoal

end Grad.WeightedJets.SpatialMultiplier
