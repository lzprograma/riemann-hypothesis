module

public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem dualMap_epsMul (φ : S →+* T) (a : S) {Y : Scheme.{0}} (v : Sp (DualNumber S) ⟶ Y) :
    spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}


variable (c x w χ) in
def FramesSeparate : Prop :=
  ∀ r s : S, (∀ (k : Type) [Field k] (φ : S →+* k) (f : c.F →+* k), IsFrame t f (spMap φ ≫ x) (w.bc φ) →
    (∀ σ a, f (embK c σ a) = φ (χ σ a)) → φ r = φ s) → r = s

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}


theorem frame_at (hw : IntFrame Z hU w) {j : Z.i.c.V W →+* Γ(Z.X, U)} (hj : spMap j = hU.fromSpec ≫ Z.s)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) (ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) :
    ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (spMap φ ≫ hU.fromSpec ≫ Z.π) (w.bc φ) ∧
      ∀ σ a, f (embK Z.i.c σ a) = φ (j (embV Z.i.c W σ a)) := by
  obtain ⟨a, ψ, hx, hf, -⟩ := hw.2 k φ ho
  rw [Category.assoc] at hf
  refine ⟨_, hf, fun σ r => ?_⟩
  have e : spMap (ψ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = spMap (φ.comp j) := by
    rw [← spMap_comp_spMap _ ψ, ← spMap_comp_spMap _ φ, hj, ← Z.alg_s a, ← Category.assoc, hx, Category.assoc]
  exact congrArg (fun q => q.hom (embV Z.i.c W σ r)) (Spec.map_injective e)

end Model

end GlobalTheory.TotalFrame
