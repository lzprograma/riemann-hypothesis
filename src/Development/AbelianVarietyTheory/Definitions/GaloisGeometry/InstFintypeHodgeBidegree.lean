module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.PiTensorProduct

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullTotMemBTot, Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective, Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective, Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullTotMemBTot =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullTotMemBTot", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u v' u' v'' u''

section Complex

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def OmF (q : ℕ) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (Om R (F.obj T) q)
  map φ := ModuleCat.ofHom (pOm F q φ)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_id F x)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_comp F φ ψ x)

def dOmNat (q : ℕ) : OmF F q ⟶ OmF F (q + 1) where
  app T := ModuleCat.ofHom (dOm R (F.obj T) q)
  naturality _ _ φ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ (pOm_dOm F φ x).symm)

abbrev Term (a q : ℕ) : Type (max u v) := CatH.Cn (OmF F q) a

abbrev dH (a q : ℕ) : Term F a q →ₗ[R] Term F (a + 1) q := CatH.d (OmF F q) a

def dV (a q : ℕ) : Term F a q →ₗ[R] Term F a (q + 1) :=
  (CatH.Mor.ofNatTrans (dOmNat F q)).pullC a

theorem dV_apply {a q : ℕ} (c : Term F a q) (s : ComposableArrows C a) :
    dV F a q c s = dOm R (F.obj (s.obj (Fin.last a))) q (c s) := rfl

abbrev Bidegree (n : ℕ) : Type := {p : ℕ × ℕ // p.1 + p.2 = n}

abbrev Tot (n : ℕ) : Type (max u v) := ∀ p : Bidegree n, Term F p.1.1 p.1.2

def totH (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, q), h⟩ => dH F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n)

def totV (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, q + 1), h⟩ => (-1 : ℤ) ^ a • (dV F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n))

def dTot (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) := totH F n + totV F n

section
variable {F} {n : ℕ} (c : Tot F n)

@[simp] theorem totH_zero {q : ℕ} (h : 0 + q = n + 1) : totH F n c ⟨(0, q), h⟩ = 0 := rfl

@[simp] theorem totH_succ {a q : ℕ} (h : a + 1 + q = n + 1) :
    totH F n c ⟨(a + 1, q), h⟩ = dH F a q (c ⟨(a, q), by omega⟩) := rfl

@[simp] theorem totV_succ {a q : ℕ} (h : a + (q + 1) = n + 1) :
    totV F n c ⟨(a, q + 1), h⟩ = (-1 : ℤ) ^ a • dV F a q (c ⟨(a, q), by omega⟩) := rfl

theorem dTot_apply (p : Bidegree (n + 1)) : dTot F n c p = totH F n c p + totV F n c p := rfl

end

def ZTot (n : ℕ) : Submodule R (Tot F n) := LinearMap.ker (dTot F n)

def BTot : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dTot F n)

def Hyp (n : ℕ) : Type (max u v) := ZTot F n ⧸ (BTot F n).submoduleOf (ZTot F n)

instance (n : ℕ) : AddCommGroup (Hyp F n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (n : ℕ) : Module R (Hyp F n) := inferInstanceAs (Module R (_ ⧸ _))

def Hyp.mk (n : ℕ) : ZTot F n →ₗ[R] Hyp F n := Submodule.mkQ _

theorem Hyp.mk_surjective (n : ℕ) : Function.Surjective (Hyp.mk F n) := Submodule.mkQ_surjective _


variable {F} in
theorem Hyp.mk_eq_zero {n : ℕ} {c : ZTot F n} : Hyp.mk F n c = 0 ↔ c.1 ∈ BTot F n :=
  Submodule.Quotient.mk_eq_zero _

def TotF (p n : ℕ) : Submodule R (Tot F n) where
  carrier := {c | ∀ b : Bidegree n, b.1.2 < p → c b = 0}
  add_mem' hc hc' b hb := by rw [Pi.add_apply, hc b hb, hc' b hb, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r c hc b hb := by rw [Pi.smul_apply, hc b hb, smul_zero]

def ZF (p n : ℕ) : Submodule R (Tot F n) := TotF F p n ⊓ ZTot F n

def BF (p : ℕ) : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => (TotF F p n).map (dTot F n)

def HypF (p n : ℕ) : Type (max u v) := ZF F p n ⧸ (BF F p n).submoduleOf (ZF F p n)

instance (p n : ℕ) : AddCommGroup (HypF F p n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (p n : ℕ) : Module R (HypF F p n) := inferInstanceAs (Module R (_ ⧸ _))

def HypF.mk (p n : ℕ) : ZF F p n →ₗ[R] HypF F p n := Submodule.mkQ _

theorem HypF.mk_surjective (p n : ℕ) : Function.Surjective (HypF.mk F p n) :=
  Submodule.mkQ_surjective _


variable {F} in
theorem HypF.mk_eq_zero {p n : ℕ} {c : ZF F p n} : HypF.mk F p n c = 0 ↔ c.1 ∈ BF F p n :=
  Submodule.Quotient.mk_eq_zero _


end Complex

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

end Pull

end GlobalTheory.HodgeCoh
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullTotMemBTot =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullTotMemBTot\npublic import Mathlib.RingTheory.WittVector.IsPoly\npublic import Mathlib.Tactic.ReduceModChar\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

theorem zsmul_add_cancel {A : Type*} [AddCommGroup A] (x : A) : (1 : ℤ) • x + (-1 : ℤ) • x = 0 := by
  rw [one_smul, neg_one_smul, add_neg_cancel]

section Zero

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

variable (F : C ⥤ CommAlgCat.{0} R)

variable {F}

end Zero

section Cone

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

def coneTerm (q : ℕ) : Om R B q →ₗ[R] Term F 0 q :=
  LinearMap.pi fun s ↦ (SemiHom.of_algHom (e (s.obj (Fin.last 0)))).mOm q


variable {T₀ : C} (hb : Function.Bijective (e T₀))




end Cone

end GlobalTheory.HodgeCoh
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

variable {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k''] {X X' X'' : Scheme.{0}}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := Spec.map_comp _ _

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

structure AffPt (s : X ⟶ Sp k) : Type 1 where

  B : CommAlgCat.{0} k

  x : Sp B ⟶ X

  w : x ≫ s = spMap (algebraMap k B)

namespace AffPt

variable {s : X ⟶ Sp k}

instance : Category.{0} (AffPt s) where
  Hom T T' := {φ : T.B ⟶ T'.B // spMap (φ.hom : T.B →+* T'.B) ≫ T.x = T'.x}
  id T := ⟨𝟙 _, by
    rw [show spMap ((𝟙 T.B : T.B ⟶ T.B).hom : T.B →+* T.B) = 𝟙 _ from spMap_id' _, Category.id_comp]⟩
  comp {T T' T''} φ ψ := ⟨φ.1 ≫ ψ.1, by
    have e : ((φ.1 ≫ ψ.1).hom : T.B →+* T''.B) =
        (ψ.1.hom : T'.B →+* T''.B).comp (φ.1.hom : T.B →+* T'.B) := rfl
    rw [e, spMap_comp', Category.assoc, φ.2, ψ.2]⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

theorem hom_ext {T T' : AffPt s} {φ ψ : T ⟶ T'} (h : φ.1 = ψ.1) : φ = ψ :=
  Subtype.ext h

end AffPt

def OPt (s : X ⟶ Sp k) : AffPt s ⥤ CommAlgCat.{0} k where
  obj T := T.B
  map φ := φ.1
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev HdR (s : X ⟶ Sp k) (n : ℕ) : Type 1 := Hyp (OPt s) n

section Fil

variable (s : X ⟶ Sp k)

end Fil

section Affine

variable (k) (B : Type) [CommRing B] [Algebra k B]

variable {k B}





end Affine

end GlobalTheory.HodgeCoh
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CatH

universe v u v' u'

section Wedge

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def wedgeOm {q q' Q : ℕ} (h : q + q' = Q) : Om R B q →ₗ[R] Om R B q' →ₗ[R] Om R B Q :=
  LinearMap.mk₂ R (fun x y ↦ ⟨x.1 * y.1, h ▸ mul_mem x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

variable {R B}

@[simp] theorem coe_wedgeOm {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    (wedgeOm R B h x y : DR R B) = x * y := rfl

theorem dOm_wedgeOm {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    dOm R B Q (wedgeOm R B h x y) = wedgeOm R B (show q + 1 + q' = Q + 1 by omega) (dOm R B q x) y +
      (-1 : ℤ) ^ q • wedgeOm R B (show q + (q' + 1) = Q + 1 by omega) x (dOm R B q' y) := by
  refine Subtype.ext ?_
  change dDR R B (x.1 * y.1) = dDR R B x.1 * y.1 + (-1 : ℤ) ^ q • (x.1 * dDR R B y.1)
  rw [dDR_mul, sgn_of_mem x.2, add_comm, zsmul_eq_mul, mul_assoc]
  simp

theorem mOm_wedgeOm {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {σ : R →+* R'}
    {α : B →+* B'} (e : SemiHom σ α) {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    e.mOm Q (wedgeOm R B h x y) = wedgeOm R' B' h (e.mOm q x) (e.mOm q' y) :=
  Subtype.ext (map_mul e.mDR x.1 y.1)


variable (R B) in
def oneOm : Om R B 0 := ⟨1, by
  change _ ∈ LinearMap.range _ ^ 0
  rw [pow_zero]; exact Submodule.one_le.1 le_rfl⟩

theorem dOm_oneOm : dOm R B 0 (oneOm R B) = 0 := Subtype.ext (by
  change dDR R B 1 = 0
  rw [← map_one (algebraMap B (DR R B)), dDR_algebraMap, Derivation.map_one_eq_zero, map_zero])

end Wedge

section Terms

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def cupTerm {a a' A q q' Q : ℕ} (ha : a + a' = A) (hq : q + q' = Q) :
    Term F a q →ₗ[R] Term F a' q' →ₗ[R] Term F A Q :=
  LinearMap.mk₂ R (fun f g s ↦ wedgeOm R (F.obj (s.obj (Fin.last A))) hq
      (ev (F := OmF F q) s (fr a A (by omega)) (fr_mono _ _ _) (Fin.last A) (Fin.le_last _) f)
      (ev (F := OmF F q') s (bk a a' A ha.le) (bk_mono _ _ _ _) (Fin.last A) (Fin.le_last _) g))
    (fun f f' g ↦ funext fun s ↦ by rw [map_add (f := _)]; exact LinearMap.map_add₂ _ _ _ _)
    (fun r f g ↦ funext fun s ↦ by rw [map_smul]; exact LinearMap.map_smul₂ _ _ _ _)
    (fun f g g' ↦ funext fun s ↦ by rw [map_add (f := _)]; exact LinearMap.map_add _ _ _)
    (fun r f g ↦ funext fun s ↦ by rw [map_smul]; exact LinearMap.map_smul _ _ _)

variable {F}

abbrev wedgeF (F : C ⥤ CommAlgCat.{0} R) {q q' Q : ℕ} (hq : q + q' = Q) (T : C) :
    (OmF F q).obj T →ₗ[R] (OmF F q').obj T →ₗ[R] (OmF F Q).obj T := wedgeOm R (F.obj T) hq

theorem cupTerm_apply {a a' A q q' Q : ℕ} (ha : a + a' = A) (hq : q + q' = Q) (f : Term F a q)
    (g : Term F a' q') (s : ComposableArrows C A) :
    cupTerm F ha hq f g s = wedgeF F hq _
      (ev (F := OmF F q) s (fr a A (by omega)) (fr_mono _ _ _) (Fin.last A) (Fin.le_last _) f)
      (ev (F := OmF F q') s (bk a a' A ha.le) (bk_mono _ _ _ _) (Fin.last A) (Fin.le_last _) g) := rfl

theorem ev_cupTerm {a a' A q q' Q K : ℕ} (ha : a + a' = A) (hq : q + q' = Q) (f : Term F a q)
    (g : Term F a' q') (s : ComposableArrows C K)
    (p : Fin (A + 1) → Fin (K + 1)) (hp : Monotone p) (j : Fin (K + 1)) (hj : p (Fin.last A) ≤ j) :
    ev (F := OmF F Q) s p hp j hj (cupTerm F ha hq f g) = wedgeF F hq _
      (ev s (p ∘ fr a A (by omega)) (hp.comp (fr_mono _ _ _)) j ((hp (Fin.le_last _)).trans hj) f)
      (ev s (p ∘ bk a a' A ha.le) (hp.comp (bk_mono _ _ _ _)) j ((hp (Fin.le_last _)).trans hj) g) := by
  refine (mOm_wedgeOm (semiHom_mp F (s.map (homOfLE hj))) hq _ _).trans ?_
  exact congrArg₂ (fun x y ↦ wedgeF F hq _ x y)
    (map_ev s (p ∘ fr a A (by omega)) (hp.comp (fr_mono _ _ _)) (hp (Fin.le_last _)) hj f)
    (map_ev s (p ∘ bk a a' A ha.le) (hp.comp (bk_mono _ _ _ _)) (hp (Fin.le_last _)) hj g)

theorem wedgeF_ev_congr {m n k q q' Q : ℕ} (hq : q + q' = Q) (s : ComposableArrows C k) (j : Fin (k + 1))
    (f : Term F m q) (g : Term F n q')
    {p p' : Fin (m + 1) → Fin (k + 1)} {hp : Monotone p} {hp' : Monotone p'}
    {r r' : Fin (n + 1) → Fin (k + 1)} {hr : Monotone r} {hr' : Monotone r'} {h1 h1' h2 h2'}
    (e1 : ∀ a, (p a : ℕ) = p' a) (e2 : ∀ b, (r b : ℕ) = r' b) :
    wedgeF F hq _ (ev s p hp j h1 f) (ev s r hr j h2 g) =
      wedgeF F hq _ (ev s p' hp' j h1' f) (ev s r' hr' j h2' g) := by
  rw [ev_congr s p p' hp hp' e1, ev_congr s r r' hr hr' e2]

local macro "fin_index_simp" : tactic => `(tactic|
  (simp only [Function.comp_apply, fr, bk, Fin.succAboveOrderEmb_apply, Fin.succAbove,
    Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_castLE, Fin.val_castAdd,
    Fin.val_natAdd, finCongr_apply_coe, Fin.val_last, Fin.val_zero]
   split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.val_castLE,
    Fin.val_castAdd, Fin.val_natAdd, finCongr_apply_coe, Fin.val_last, Fin.val_zero] <;> omega))

theorem dH_cupTerm {m n k q q' Q : ℕ} (h : m + n = k) (hq : q + q' = Q) (f : Term F m q)
    (g : Term F n q') :
    dH F k Q (cupTerm F h hq f g) = cupTerm F (show m + 1 + n = k + 1 by omega) hq (dH F m q f) g +
      ((-1 : ℤ) ^ m) • cupTerm F (show m + (n + 1) = k + 1 by omega) hq f (dH F n q' g) := by
  subst h
  funext s
  rw [Pi.add_apply, Pi.smul_apply, cupTerm_apply, cupTerm_apply, ev_d, ev_d, d_apply_ev]
  refine (Finset.sum_congr rfl fun (i : Fin (m + n + 2)) _ ↦ congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z)
    (ev_cupTerm rfl hq f g s _ (Fin.succAboveOrderEmb i).monotone _ (Fin.le_last _))).trans ?_

  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply]
  rw [← (finCongr (show m + 1 + (n + 1) = m + n + 1 + 1 by omega)).sum_comp, Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := m + 1), Fin.sum_univ_succ (n := n + 1), smul_add, Finset.smul_sum]
  refine add_rearrange_of_cancel_middle (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun j _ ↦ ?_) ?_
  · have := i.isLt
    refine congrArg₂ (· • ·) rfl (wedgeF_ev_congr hq s _ f g (fun a ↦ ?_) (fun b ↦ ?_))
    · have := a.isLt
      rcases lt_or_ge (a : ℕ) i with h1 | h1 <;> fin_index_simp
    · have := b.isLt
      fin_index_simp
  · have := j.isLt
    rw [smul_smul, ← pow_add]
    refine congrArg₂ (· • ·) (congrArg _ (by simp [Fin.val_succ]; omega))
      (wedgeF_ev_congr hq s _ f g (fun a ↦ ?_) (fun b ↦ ?_))
    · have := a.isLt
      fin_index_simp
    · have := b.isLt
      rcases lt_or_ge (b : ℕ) (j + 1) with h1 | h1 <;> fin_index_simp
  · rw [Fin.val_last, Fin.val_zero]
    refine neg_one_pow_boundary_terms_cancel m (wedgeF_ev_congr hq s _ f g (fun a ↦ ?_) (fun b ↦ ?_))
    · have := a.isLt
      fin_index_simp
    · have := b.isLt
      fin_index_simp

theorem dOm_ev {n k q : ℕ} (s : ComposableArrows C k) (p : Fin (n + 1) → Fin (k + 1)) (hp : Monotone p)
    (j : Fin (k + 1)) (h : p (Fin.last n) ≤ j) (f : Term F n q) :
    dOm R (F.obj (s.obj j)) q (ev s p hp j h f) = ev s p hp j h (dV F n q f) :=
  (pOm_dOm F (s.map (homOfLE h)) _).symm

theorem dV_cupTerm {m n k q q' Q : ℕ} (h : m + n = k) (hq : q + q' = Q) (f : Term F m q)
    (g : Term F n q') :
    dV F k Q (cupTerm F h hq f g) = cupTerm F h (show q + 1 + q' = Q + 1 by omega) (dV F m q f) g +
      ((-1 : ℤ) ^ q) • cupTerm F h (show q + (q' + 1) = Q + 1 by omega) f (dV F n q' g) := by
  funext s
  rw [dV_apply, cupTerm_apply]
  refine (dOm_wedgeOm hq _ _).trans ?_
  exact congrArg₂ (· + ·) (congrArg (fun z ↦ wedgeF F _ _ z _) (dOm_ev s _ _ _ _ f))
    (congrArg (fun z ↦ (-1 : ℤ) ^ q • wedgeF F _ _ _ z) (dOm_ev s _ _ _ _ g))


variable (F) in
def oneTerm : Term F 0 0 := fun s ↦ oneOm R (F.obj (s.obj (Fin.last 0)))

theorem coe_ev_oneTerm {k : ℕ} (s : ComposableArrows C k) (p : Fin 1 → Fin (k + 1)) (hp : Monotone p)
    (j : Fin (k + 1)) (h : p (Fin.last 0) ≤ j) :
    (ev s p hp j h (oneTerm F) : (OmF F 0).obj _).1 = 1 :=
  map_one (semiHom_mp F (s.map (homOfLE h))).mDR

end Terms

section Total

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

instance instFintypeHodgeBidegree (n : ℕ) : Fintype (Bidegree n) :=
  Fintype.subtype (Finset.HasAntidiagonal.antidiagonal n) fun _ ↦
    Finset.HasAntidiagonal.mem_antidiagonal

def Tot.sg {a q n : ℕ} (h : a + q = n) : Term F a q →ₗ[R] Tot F n :=
  LinearMap.single R (fun b : Bidegree n ↦ Term F b.1.1 b.1.2) ⟨(a, q), h⟩

variable {F}

theorem Tot.sg_same {a q n : ℕ} (h : a + q = n) (c : Term F a q) : Tot.sg F h c ⟨(a, q), h⟩ = c :=
  Pi.single_eq_same (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2) _ _

theorem Tot.sg_of_ne {a q n : ℕ} (h : a + q = n) (c : Term F a q) (b : Bidegree n) (hb : b.1.2 ≠ q) :
    Tot.sg F h c b = 0 :=
  Pi.single_eq_of_ne (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2) (fun e ↦ hb (by rw [e])) _

theorem Tot.sum_sg {n : ℕ} (c : Tot F n) : ∑ b : Bidegree n, Tot.sg F b.2 (c b) = c :=
  Finset.univ_sum_single c

theorem Tot.induction {n : ℕ} {P : Tot F n → Prop} (h0 : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (a q : ℕ) (h : a + q = n) (c : Term F a q), P (Tot.sg F h c)) (c : Tot F n) : P c := by
  rw [← Tot.sum_sg c]
  exact Finset.sum_induction _ P ha h0 fun b _ ↦ hs _ _ b.2 _

theorem dTot_sg {a q n : ℕ} (h : a + q = n) (c : Term F a q) :
    dTot F n (Tot.sg F h c) = Tot.sg F (show a + 1 + q = n + 1 by omega) (dH F a q c) +
      (-1 : ℤ) ^ a • Tot.sg F (show a + (q + 1) = n + 1 by omega) (dV F a q c) := by
  funext ⟨(A, Q), hb⟩
  dsimp only at hb
  rw [dTot_apply, Pi.add_apply, Pi.smul_apply]
  congr 1
  · by_cases hQ : Q = q
    · subst hQ
      obtain rfl : A = a + 1 := by omega
      rw [totH_succ, Tot.sg_same, Tot.sg_same]
    · rw [Tot.sg_of_ne _ _ _ hQ]
      rcases A with _ | A
      · rfl
      · rw [totH_succ, Tot.sg_of_ne _ _ _ hQ, map_zero]
  · by_cases hQ : Q = q + 1
    · subst hQ
      obtain rfl : A = a := by omega
      rw [totV_succ, Tot.sg_same, Tot.sg_same]
    · rw [Tot.sg_of_ne _ _ _ hQ, smul_zero]
      rcases Q with _ | Q
      · rfl
      · rw [totV_succ, Tot.sg_of_ne _ _ _ (fun e ↦ hQ (congrArg (· + 1) e)), map_zero, smul_zero]


variable (F) in
def Tot.cup {m n N : ℕ} (h : m + n = N) : Tot F m →ₗ[R] Tot F n →ₗ[R] Tot F N :=
  ∑ b : Bidegree m, ∑ b' : Bidegree n, (-1 : ℤ) ^ (b.1.2 * b'.1.1) •
    ((cupTerm F rfl rfl).compl₁₂ (LinearMap.proj b) (LinearMap.proj b')).compr₂
      (Tot.sg F (show b.1.1 + b'.1.1 + (b.1.2 + b'.1.2) = N by have := b.2; have := b'.2; omega))

theorem Tot.cup_apply {m n N : ℕ} (h : m + n = N) (x : Tot F m) (y : Tot F n) :
    Tot.cup F h x y = ∑ b : Bidegree m, ∑ b' : Bidegree n, (-1 : ℤ) ^ (b.1.2 * b'.1.1) •
      Tot.sg F (show b.1.1 + b'.1.1 + (b.1.2 + b'.1.2) = N by have := b.2; have := b'.2; omega)
        (cupTerm F rfl rfl (x b) (y b')) := by
  simp only [Tot.cup, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem Tot.cup_sg {m n N a q a' q' A Q : ℕ} (h : m + n = N) (h₁ : a + q = m) (h₂ : a' + q' = n)
    (ha : a + a' = A) (hq : q + q' = Q) (h₃ : A + Q = N) (f : Term F a q) (g : Term F a' q') :
    Tot.cup F h (Tot.sg F h₁ f) (Tot.sg F h₂ g) =
      (-1 : ℤ) ^ (q * a') • Tot.sg F h₃ (cupTerm F ha hq f g) := by
  subst ha hq
  rw [Tot.cup_apply, Finset.sum_eq_single (⟨(a, q), h₁⟩ : Bidegree m),
    Finset.sum_eq_single (⟨(a', q'), h₂⟩ : Bidegree n), Tot.sg_same, Tot.sg_same]
  · intro b _ hb
    rw [Tot.sg_of_ne h₂ g b (fun e ↦ hb (Subtype.ext (Prod.ext (by have := b.2; dsimp only; omega) e))),
      map_zero, map_zero, smul_zero]
  · exact fun e ↦ absurd (Finset.mem_univ _) e
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ ↦ ?_
    rw [Tot.sg_of_ne h₁ f b (fun e ↦ hb (Subtype.ext (Prod.ext (by have := b.2; dsimp only; omega) e))),
      map_zero, LinearMap.zero_apply, map_zero, smul_zero]
  · exact fun e ↦ absurd (Finset.mem_univ _) e

theorem dTot_cup {m n N : ℕ} (h : m + n = N) (x : Tot F m) (y : Tot F n) :
    dTot F N (Tot.cup F h x y) = Tot.cup F (show m + 1 + n = N + 1 by omega) (dTot F m x) y +
      (-1 : ℤ) ^ m • Tot.cup F (show m + (n + 1) = N + 1 by omega) x (dTot F n y) := by
  induction x using Tot.induction with
  | h0 => simp
  | ha x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx', smul_add]; abel
  | hs a q h₁ f =>
  induction y using Tot.induction with
  | h0 => simp
  | ha y y' hy hy' => simp only [map_add (f := _), hy, hy', smul_add]; abel
  | hs a' q' h₂ g =>
  have e₁ : a + a' + 1 + (q + q') = N + 1 := by omega
  have e₂ : a + a' + (q + q' + 1) = N + 1 := by omega
  rw [Tot.cup_sg h h₁ h₂ rfl rfl (by omega), map_zsmul, dTot_sg, dTot_sg, dTot_sg, dH_cupTerm, dV_cupTerm]
  simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [Tot.cup_sg _ _ h₂ (show a + 1 + a' = a + a' + 1 by omega) rfl e₁,
    Tot.cup_sg _ _ h₂ rfl (show q + 1 + q' = q + q' + 1 by omega) e₂,
    Tot.cup_sg _ h₁ _ (show a + (a' + 1) = a + a' + 1 by omega) rfl e₁,
    Tot.cup_sg _ h₁ _ rfl (show q + (q' + 1) = q + q' + 1 by omega) e₂]
  rw [show (-1 : ℤ) ^ m = (-1) ^ (a + q) by rw [h₁]]
  have hq : ((-1 : ℤ) ^ q) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  simp only [pow_add, add_mul, mul_add, one_mul, mul_one]
  match_scalars
  · ring
  · linear_combination (-(-1 : ℤ) ^ (q * a') * (-1) ^ a) * hq
  · ring
  · ring


variable (F) in
def Tot.one : Tot F 0 := Tot.sg F rfl (oneTerm F)

theorem Tot.one_mem : Tot.one F ∈ ZTot F 0 := by
  have h1 : dH F 0 0 (oneTerm F) = 0 := by
    funext s
    rw [d_apply_ev, Fin.sum_univ_two]
    have e : ∀ i : Fin 2, ev s (Fin.succAboveOrderEmb i) (Fin.succAboveOrderEmb i).monotone (Fin.last _)
        (Fin.le_last _) (oneTerm F) = (oneOm R (F.obj (s.obj (Fin.last 1))) : (OmF F 0).obj _) :=
      fun i ↦ Subtype.ext (coe_ev_oneTerm s _ _ _ _)
    rw [e, e]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    exact zsmul_add_cancel _
  have h2 : dV F 0 0 (oneTerm F) = 0 := funext fun _ ↦ dOm_oneOm
  change dTot F 0 _ = 0
  rw [Tot.one, dTot_sg, h1, h2, map_zero, map_zero, smul_zero, add_zero]

theorem Tot.cup_mem_ZTot {m n N : ℕ} (h : m + n = N) {x : Tot F m} {y : Tot F n}
    (hx : x ∈ ZTot F m) (hy : y ∈ ZTot F n) : Tot.cup F h x y ∈ ZTot F N := by
  change dTot F N _ = 0
  rw [dTot_cup, show dTot F m x = 0 from hx, show dTot F n y = 0 from hy, map_zero,
    LinearMap.zero_apply, map_zero, smul_zero, add_zero]

theorem Tot.cup_mem_BTot_left {m n N : ℕ} (h : m + n = N) {x : Tot F m} {y : Tot F n}
    (hx : x ∈ BTot F m) (hy : y ∈ ZTot F n) : Tot.cup F h x y ∈ BTot F N := by
  cases m with
  | zero => rw [show x = 0 from hx, map_zero, LinearMap.zero_apply]; exact zero_mem _
  | succ m =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    refine ⟨Tot.cup F (show m + n = N by omega) x y, ?_⟩
    rw [dTot_cup, show dTot F n y = 0 from hy, map_zero, smul_zero, add_zero]

theorem Tot.cup_mem_BTot_right {m n N : ℕ} (h : m + n = N) {x : Tot F m} {y : Tot F n}
    (hx : x ∈ ZTot F m) (hy : y ∈ BTot F n) : Tot.cup F h x y ∈ BTot F N := by
  cases n with
  | zero => rw [show y = 0 from hy, map_zero]; exact zero_mem _
  | succ n =>
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    refine ⟨(-1 : ℤ) ^ m • Tot.cup F (show m + n = N by omega) x y, ?_⟩
    rw [map_zsmul, dTot_cup, show dTot F m x = 0 from hx, map_zero, LinearMap.zero_apply, zero_add,
      smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]


variable (F) in
def ZTot.cup {m n N : ℕ} (h : m + n = N) : ZTot F m →ₗ[R] ZTot F n →ₗ[R] ZTot F N :=
  LinearMap.mk₂ R (fun x y ↦ ⟨Tot.cup F h x.1 y.1, Tot.cup_mem_ZTot h x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_add _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_smul _ _ _))


variable (F) in
def Hyp.cup {m n N : ℕ} (h : m + n = N) : Hyp F m →ₗ[R] Hyp F n →ₗ[R] Hyp F N :=
  LinearMap.liftQ₂ _ _ ((ZTot.cup F h).compr₂ (Hyp.mk F N))
    (fun x hx ↦ LinearMap.ext fun y ↦ Hyp.mk_eq_zero.2 (Tot.cup_mem_BTot_left h hx y.2))
    (fun y hy ↦ LinearMap.ext fun x ↦ Hyp.mk_eq_zero.2 (Tot.cup_mem_BTot_right h x.2 hy))


variable (F) in
def Hyp.one : Hyp F 0 := Hyp.mk F 0 ⟨Tot.one F, Tot.one_mem⟩

end Total

section Pull

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'}
  [Category.{v'} C'] {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  (μ : CoefMap σ F F')

end Pull

section Cone

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

end Cone

section Scheme

variable {k k' : Type} [CommRing k] [CommRing k'] {X X' : Scheme.{0}}

def HdR.cup (s : X ⟶ Sp k) {a b n : ℕ} (h : a + b = n) : HdR s a →ₗ[k] HdR s b →ₗ[k] HdR s n :=
  Hyp.cup (OPt s) h

def HdR.one (s : X ⟶ Sp k) : HdR s 0 := Hyp.one (OPt s)

variable {s : X ⟶ Sp k} {a b n : ℕ}

end Scheme

end GlobalTheory.HodgeCoh
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree =====
