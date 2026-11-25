module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair\nimport Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt\npublic import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

section Lin

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

theorem lin_comp {u u' : Fin m → V} (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0)
    (hu : ∀ j, u' j = ∑ i, A j i • u i) (d : Fin m → k) (j : Fin m) (hd : ∀ i, j < i → d i = 0) :
    ∃ e : Fin m → k, (∀ i, j < i → e i = 0) ∧ e j = d j * A j j ∧ ∑ i, d i • u' i = ∑ i, e i • u i := by
  refine ⟨fun i => ∑ l, d l * A l i, fun i hi => Finset.sum_eq_zero fun l _ => ?_, ?_, ?_⟩
  · rcases lt_or_ge j l with h | h
    · rw [hd l h, zero_mul]
    · rw [hA l i (h.trans_lt hi), mul_zero]
  · refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA l j h, mul_zero]
    · rw [hd l h, zero_mul]
  · simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

theorem lin_symm {u u' : Fin m → V} (hi : ∀ c c' : Fin m → k, ∑ i, c i • u' i = ∑ i, c' i • u' i → c = c')
    (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0) (hu : ∀ j, u' j = ∑ i, A j i • u i) :
    ∃ B : Fin m → Fin m → k, (∀ j i, j < i → B j i = 0) ∧ (∀ j, u j = ∑ i, B j i • u' i) ∧ ∀ j, A j j * B j j = 1 := by
  classical
  let M : Matrix (Fin m) (Fin m) k := Matrix.of A
  have key : ∀ d : Fin m → k, ∑ i, d i • u' i = ∑ i, Matrix.vecMul d M i • u i := fun d => by
    simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul, Matrix.vecMul, dotProduct, M, Matrix.of_apply]
    exact Finset.sum_comm
  have hM : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 fun d d' h => hi _ _ (by
    rw [key, key]; exact congrArg (fun c : Fin m → k => ∑ i, c i • u i) h)
  obtain ⟨I⟩ := hM.nonempty_invertible
  have ht : M.BlockTriangular OrderDual.toDual := fun j i h => hA j i h
  have hB : ∀ j i, j < i → M⁻¹ j i = 0 := fun j i h => Matrix.blockTriangular_inv_of_blockTriangular ht h
  have h2 : ∀ j, u j = ∑ i, M⁻¹ j i • u' i := fun j => by
    rw [key, show Matrix.vecMul (M⁻¹ j) M = (M⁻¹ * M) j from rfl, Matrix.inv_mul_of_invertible]
    simp [Matrix.one_apply]
  refine ⟨fun j i => M⁻¹ j i, hB, h2, fun j => ?_⟩
  obtain ⟨e, -, he, h⟩ := lin_comp (fun j i => M⁻¹ j i) hB h2 (A j) j (hA j)
  have := hi e (Pi.single j 1) (by rw [← h, ← hu]; simp [Pi.single_apply])
  rw [← he, this, Pi.single_eq_same]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

def Ind (u : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def Tri (u u' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  ∀ j, ∃ cf : Fin m → k, (∀ i, j < i → cf i = 0) ∧ IsCombAtG t x u cf (u' j)

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

theorem comb_iff (U : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (U i)).left) a w ↔ w = (tv (∑ i, a i • U i)).left := by
  have h := (GlobalTheory.LieMet.isComb_iff U a _).2 rfl
  refine ⟨fun h' => ?_, fun e => e ▸ h⟩
  exact ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h').symm.trans
    ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h)

theorem exists_tan (h : ∀ i, IsTanAtG t x (u i)) : ∃ U : Fin m → TanM x t.G, u = fun i => (tv (U i)).left :=
  ⟨fun i => tanOf (h i), rfl⟩

theorem Tri.comp (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u') {d : Fin m → k}
    {j : Fin m} (hd : ∀ i, j < i → d i = 0) {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsCombAtG t x u' d w) :
    ∃ c e : Fin m → k, IsCombAtG t x u c (u' j) ∧ (∀ i, j < i → e i = 0) ∧ e j = d j * c j ∧ IsCombAtG t x u e w := by
  obtain ⟨U, rfl⟩ := exists_tan hu
  obtain ⟨U', rfl⟩ := exists_tan hu'
  choose A hA hc using h
  obtain ⟨e, h1, h2, h3⟩ := lin_comp A hA (fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)) d j hd
  exact ⟨A j, e, hc j, h1, h2, (comb_iff _ _ _).2 (h3 ▸ (comb_iff _ _ _).1 hw)⟩

theorem Tri.trans (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u')
    (h' : Tri t x u' u'') : Tri t x u u'' := fun j => by
  obtain ⟨d, hd, hw⟩ := h' j
  obtain ⟨-, e, -, h1, -, h2⟩ := h.comp hu hu' hd hw
  exact ⟨e, h1, h2⟩

theorem Tri.symm (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') : Tri t x u' u ∧
    ∀ j c d, IsCombAtG t x u c (u' j) → IsCombAtG t x u' d (u j) → c j * d j = 1 := by
  obtain ⟨U, rfl⟩ := exists_tan hu.1
  obtain ⟨U', rfl⟩ := exists_tan hu'.1
  choose A hA hc using h
  obtain ⟨B, h1, h2, h3⟩ := lin_symm (u := U) (u' := U') (fun c c' e => hu'.2 c c' _ ((GlobalTheory.LieMet.isComb_iff _ _ _).2 rfl)
    ((GlobalTheory.LieMet.isComb_iff _ _ _).2 e)) A hA fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)
  refine ⟨fun j => ⟨B j, h1 j, (GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)⟩, fun j c d hc' hd => ?_⟩
  rw [hu.2 _ _ _ hc' (hc j), hu'.2 _ _ _ hd ((GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)), h3]

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}


end Norm

end GlobalTheory.ShFam.Pad.Pull
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\npublic import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair\nimport Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

section Val

variable {F : Type} [Field F] {X Y : Scheme.{0}}

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}

theorem eig_iff {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : TanM x t.G) (a : 𝓞 E) (s : R) :
    (tv v).left ≫ (t.act.act a).left = spMap (epsMul s) ≫ (tv v).left ↔ actR t.act a v = s • v :=
  ⟨fun h => tan_ext h, fun h => congrArg (fun z => (tv z).left) h⟩

variable {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

theorem comb_push {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hu : ∀ i, IsTanAtG t' x' (u i))
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (cf : Fin m → R) :
    IsCombAtG t x (fun i => u i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x' u cf w := by
  refine (GlobalTheory.LieMet.isComb_iff (fun i => pushE mu x' hx (tanOf (hu i))) cf (pushE mu x' hx (tanOf hw))).trans
    (Iff.trans ?_ (GlobalTheory.LieMet.isComb_iff (fun i => tanOf (hu i)) cf (tanOf hw)).symm)

  simp only [← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

end Frames

section Steps

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l} {p : ℕ}

end Steps

section Models

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)

include hf hT

end Models

section Bundle

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

end Bundle

section Main

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

variable (hf : IsMap Z' Z f) {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)
  (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) (M : LineModel Z b st x)

include hf hT hty



end Main

end GlobalTheory.ShFam.Pad.Pull
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap =====
