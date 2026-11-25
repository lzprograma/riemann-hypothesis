module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec chernPoly)
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.CxForm

section Point

variable {n m : ℕ}

abbrev Alt (n : ℕ) : Type := ExteriorAlgebra ℂ (Fin n ⊕ Fin n → ℂ)

abbrev Ev (n : ℕ) : Type := Subalgebra.center ℂ (Alt n)

def dz (a : Fin n) : Alt n := ExteriorAlgebra.ι ℂ (Pi.single (.inl a) 1)

def dzb (a : Fin n) : Alt n := ExteriorAlgebra.ι ℂ (Pi.single (.inr a) 1)

def bas (n : ℕ) : Module.Basis (Finset (Fin (n + n))) ℂ (Alt n) :=
  ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv).ExteriorAlgebra

def swap : Alt n →ₐ[ℂ] Alt n := ExteriorAlgebra.map (LinearMap.funLeft ℂ ℂ Sum.swap)

def pull (L : V n →L[ℂ] V m) : Alt m →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (fromBlocks (of fun b a => L (coordVec b) a) 0 0
    (of fun b a => conj (L (coordVec b) a))))

theorem ι_mul_ι_mem_center (u w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w ∈ Subalgebra.center ℂ (Alt n) := by
  refine Subalgebra.mem_center_iff.2 fun b => ?_
  induction b using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commutes _ _
  | ι x =>
    rw [← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x u), neg_mul, mul_assoc,
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x w), mul_neg, neg_neg, mul_assoc]
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

def sym (x : Fin n × Fin n) : Ev n := ⟨dz x.1 * dzb x.2, ι_mul_ι_mem_center _ _⟩

def ofValues (α : V n → V n → ℂ) : Ev n := ∑ a, ∑ b, α (coordVec a) (coordVec b) • sym (a, b)

def vol (n : ℕ) : Ev n := ∏ a, (Complex.I / 2) • sym (a, a)

def dens (α : Alt n) : ℂ := (bas n).repr α Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ

def coefwise (T : (V n → ℂ) → ℂ) (α : V n → Alt n) : Alt n :=
  ∑ S, T (fun x => (bas n).repr (α x) S) • bas n S

def delAt (α : V n → Alt n) (v : V n) : Alt n := ∑ a, dz a * coefwise (fun f => del f v (coordVec a)) α

def dbarAt (α : V n → Alt n) (v : V n) : Alt n := ∑ a, dzb a * coefwise (fun f => dbar f v (coordVec a)) α

def chernAt {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) (j : ℕ) : Ev n :=
  kappa ^ j • MvPolynomial.aeval sym (chernPoly G v j)

theorem swap_dz (a : Fin n) : swap (dz a) = dzb a ∧ swap (dzb a) = dz a := by
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    simp [LinearMap.funLeft_apply, Pi.single_apply]

theorem pull_dz (L : V n →L[ℂ] V m) (a : Fin m) : pull L (dz a) = ∑ b, L (coordVec b) a • dz b ∧
    pull L (dzb a) = ∑ b, conj (L (coordVec b) a) • dzb b := by

  simp only [dz, dzb, ← map_smul, ← map_sum]
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    simp [Pi.single_apply, Finset.sum_apply]

theorem bas_singleton (i : Fin n ⊕ Fin n) :
    bas n {finSumFinEquiv i} = ExteriorAlgebra.ι ℂ (Pi.single i 1) := by
  rw [bas, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv, Set.powersetCard.ofCard]

theorem bas_empty : bas n ∅ = 1 := by
  rw [bas, ExteriorAlgebra.basis_apply_ofCard _ Finset.card_empty, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_zero_apply]

theorem bas_mul {S T : Finset (Fin (n + n))} (h : Disjoint S T) : ∃ ε : ℤˣ, bas n S * bas n T = ε • bas n (S ∪ T) := by
  have := ExteriorAlgebra.basis_mul_of_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
    (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
  exact ⟨_, this.trans (by congr 2; ext; simp [Set.powersetCard.disjUnion])⟩

theorem vol_eq (n : ℕ) : ∃ c : ℂ, c ≠ 0 ∧ (vol n : Alt n) = c • bas n Finset.univ := by
  have key (s : Finset (Fin n)) : ∃ c : ℂ, c ≠ 0 ∧ ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev n) : Alt n) =
      c • bas n (Finset.univ.filter fun i => (finSumFinEquiv.symm i).elim id id ∈ s) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp [bas_empty]⟩
    | insert a s ha ih =>
      obtain ⟨c, hc, e⟩ := ih
      obtain ⟨ε, h₁⟩ := bas_mul (S := {finSumFinEquiv (.inl a)}) (T := {finSumFinEquiv (.inr a)})
        (Finset.disjoint_singleton.2 (finSumFinEquiv.injective.ne Sum.inl_ne_inr))
      obtain ⟨ε', h₂⟩ := bas_mul (S := {finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr a)})
        (T := Finset.univ.filter fun i => (finSumFinEquiv.symm i).elim id id ∈ s) (by simp [ha, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right])
      refine ⟨Complex.I / 2 * c * ((ε : ℤ) * (ε' : ℤ)), by simp [hc], ?_⟩
      rw [Finset.prod_insert ha, Subalgebra.coe_mul, e, Subalgebra.coe_smul,
        show (sym (a, a) : Alt n) = dz a * dzb a from rfl, dz, dzb, ← bas_singleton,
        ← bas_singleton, h₁, smul_mul_smul_comm, smul_mul_assoc, h₂, Units.smul_def, Units.smul_def,
        ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, smul_smul, mul_assoc _ (_ : ℂ) (_ : ℂ)]
      congr 2
      ext i
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  simpa [vol] using key Finset.univ

theorem dens_vol (n : ℕ) : dens (vol n : Alt n) = 1 := by
  obtain ⟨c, hc, e⟩ := vol_eq n
  exact div_self (by simpa [e] using hc)

theorem coefwise_smul {T : (V n → ℂ) → ℂ} (hT : T (fun _ => 0) = 0) (u : V n → ℂ) (S : Finset (Fin (n + n))) :
    coefwise T (fun x => u x • bas n S) = T u • bas n S := by
  rw [coefwise, Finset.sum_eq_single S (fun S' _ h => by simp [Finsupp.single_apply, h.symm, hT]) (by simp)]
  simp

end Point

structure HolAtlas (M : Type) [TopologicalSpace M] (n : ℕ) where

  ι : Type

  e : ι → OpenPartialHomeomorph M (V n)

  cover : ∀ y, ∃ i, y ∈ (e i).source

  holo : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)

namespace HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

def std (n : ℕ) : HolAtlas (V n) n :=
  ⟨Unit, fun _ => .refl _, fun _ => ⟨(), trivial⟩, fun _ _ => differentiableOn_id⟩

def Pt : Type := {x : A.ι × M // x.2 ∈ (A.e x.1).source}


variable {A} in
abbrev Pt.pt (x : A.Pt) : M := x.1.2


variable {A} in
abbrev Pt.ch (x : A.Pt) : OpenPartialHomeomorph M (V n) := A.e x.1.1


variable {A} in
abbrev Pt.crd (x : A.Pt) : V n := x.ch x.pt

abbrev Fld : Type := A.Pt → Alt n


open Classical in
def loc (α : A.Fld) (i : A.ι) (v : V n) : Alt n :=
  if h : v ∈ (A.e i).target then α ⟨(i, (A.e i).symm v), (A.e i).map_target h⟩ else 0

def HolOn (U : Set M) (g : M → ℂ) : Prop :=
  ∀ i, DifferentiableOn ℂ (g ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' U)

def SmoothOn (U : Set M) (g : M → ℂ) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (g ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' U)

def IsHolo (f : M' → M) : Prop :=
  Continuous f ∧ ∀ j i, DifferentiableOn ℂ (A.e i ∘ f ∘ (A'.e j).symm)
    ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source))

structure IsForm (α : A.Fld) : Prop where

  smooth : ∀ i S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (A.loc α i v) S) (A.e i).target

  compat : ∀ x x' : A.Pt, x.pt = x'.pt → α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x')

def fn (u : M → ℝ) : A.Fld := fun x => algebraMap ℂ _ (u x.pt)

def del (α : A.Fld) : A.Fld := fun x => delAt (A.loc α x.1.1) x.crd

def dbar (α : A.Fld) : A.Fld := fun x => dbarAt (A.loc α x.1.1) x.crd

def pullback (f : M' → M) (α : A.Fld) : A'.Fld := fun x =>
  pull (fderiv ℂ (A.e (A.cover (f x.pt)).choose ∘ f ∘ x.ch.symm) x.crd) (α ⟨(_, f x.pt), (A.cover (f x.pt)).choose_spec⟩)

def chern {r : Type} [Fintype r] [DecidableEq r] (G : M → Matrix r r ℂ) (j : ℕ) (x : A.Pt) : Ev n :=
  chernAt (fun v => G (x.ch.symm v)) x.crd j

def part [MeasurableSpace M] (α : A.Fld) (ε : ℤˣ) : Measure M :=
  ChartGlue.glueMeas A.e fun i y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i (A.e i y))).re)

def integral [MeasurableSpace M] (α : A.Fld) : ℝ := (A.part α 1).real univ - (A.part α (-1)).real univ

theorem loc_crd (α : A.Fld) (x : A.Pt) : A.loc α x.1.1 x.crd = α x := by
  rw [loc, dite_eq_left (x.ch.map_source x.2)]
  exact congrArg α (Subtype.ext (Prod.ext rfl (x.ch.left_inv x.2)))

theorem isForm_fn {u : M → ℝ} (hu : A.SmoothOn univ fun y => u y) : A.IsForm (A.fn u) := by
  refine ⟨fun i S => ?_, fun x x' h => by rw [fn, fn, AlgHom.commutes, h]⟩
  refine (((hu i).mono fun v hv => ⟨hv, trivial⟩).mul (contDiffOn_const (c := (bas n).repr 1 S))).congr fun v hv => ?_
  simp [loc, hv, fn, Algebra.algebraMap_eq_smul_one, -Complex.coe_smul]

end HolAtlas

end GlobalTheory.CxForm
