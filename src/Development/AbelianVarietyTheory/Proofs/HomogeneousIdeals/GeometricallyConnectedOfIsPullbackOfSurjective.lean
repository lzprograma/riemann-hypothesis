module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem GlobalTheory.geometricallyConnected_of_isPullback_of_surjective {X Y X' Y' : Scheme.{0}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] [GeometricallyConnected p] : GeometricallyConnected q := by
  refine ⟨fun K _ t Z fst snd hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd s t).surjective (Nonempty.some inferInstance)
  let e := (pullback s t).fromSpecResidueField z
  let u := e ≫ pullback.fst s t
  let v := e ≫ pullback.snd s t
  have huv : v ≫ t = u ≫ s := by simp only [u, v, Category.assoc, pullback.condition]
  have hbig : IsPullback (pullback.fst snd v ≫ fst) (pullback.snd snd v) q (u ≫ s) :=
    huv ▸ (IsPullback.of_hasPullback snd v).paste_horiz hZ
  have hsmall := IsPullback.of_right
    (h₁₁ := h.lift (pullback.fst snd v ≫ fst) (pullback.snd snd v ≫ u)
      (by simpa only [Category.assoc] using hbig.w))
    (by simpa using hbig) (by simp) h
  have hc : ConnectedSpace ↥(pullback snd v) :=
    GeometricallyConnected.geometrically_connectedSpace u _ _ hsmall
  have hv : Surjective v := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst snd v).surjective.connectedSpace (pullback.fst snd v).continuous

theorem GlobalTheory.torusExtension_smooth_geometricallyConnected {K : Type} [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] (E : TorusExtension G) : Smooth E.q.left ∧ GeometricallyConnected E.q.left ∧ Smooth G.hom ∧ GeometricallyConnected G.hom ∧ IsSeparated G.hom := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_flat
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI : Smooth E.B.hom := E.isAbelian.smooth
  haveI : GeometricallyConnected E.B.hom := E.isAbelian.geomConnected
  haveI : IsProper E.B.hom := E.isAbelian.proper
  have hTc : GeometricallyConnected (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    ((GlobalTheory.splitTorus_properties (Spec (CommRingCat.of K))).1 E.X).2.2.2.2.2.2.2.1
  have hiq : E.i ≫ E.q = 1 := E.isKernel.w
  have key : ∀ {W : Over (Spec (CommRingCat.of K))} (a b : W ⟶ G), a ≫ E.q = b ≫ E.q →
      (a⁻¹ * b) ≫ E.q = toUnit W ≫ (η : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.B) := by
    intro W a b hab
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, _root_.inv_mul_cancel]
    try exact rfl
  let m : G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X ⟶ G := fst _ _ * (snd _ _ ≫ E.i)
  have hm : ∀ {W : Over (Spec (CommRingCat.of K))} (l : W ⟶ G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X),
      l ≫ m = (l ≫ fst _ _) * ((l ≫ snd _ _) ≫ E.i) := by
    intro W l
    simp only [m, MonObj.comp_mul, Category.assoc]
  have hw : fst _ _ ≫ E.q = m ≫ E.q := by
    simp only [m, MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  have hsq : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)) m E.q E.q :=
    IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
      (fun c => lift c.fst (E.isKernel.lift (c.fst⁻¹ * c.snd) (toUnit _) (key _ _ c.condition)))
      (fun c => by rw [lift_fst])
      (fun c => by rw [hm, lift_fst, lift_snd, IsPullback.lift_fst, mul_inv_cancel_left])
      (fun c l h1 h2 => by
        refine CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, h1]) ?_
        rw [lift_snd]
        refine E.isKernel.hom_ext ?_ (toUnit_unique _ _)
        rw [IsPullback.lift_fst]
        rw [hm, h1] at h2
        exact eq_inv_mul_of_mul_eq h2))
  have hsqS : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left m.left
      E.q.left E.q.left := hsq.map (Over.forget _)
  have hprod : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left
      (snd G (splitTorus (Spec (CommRingCat.of K)) E.X)).left G.hom
      (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    IsPullback.of_hasPullback _ _
  have hfs : Smooth (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hprod.flip inferInstance
  have hfc : GeometricallyConnected (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprod.flip hTc
  have hqs : Smooth E.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsqS
      ⟨⟨E.q_surjective, E.q_flat⟩, E.q_quasiCompact⟩ hfs
  have hqc : GeometricallyConnected E.q.left :=
    GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hsqS.flip
  have hqa : IsAffineHom E.q.left :=
    GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel _ G E.B _ E.q E.i E.q_hom E.i_hom
      E.q_flat E.q_surjective E.q_quasiCompact E.isKernel inferInstance
  rw [← Over.w E.q]
  refine ⟨hqs, hqc, inferInstance, GeometricallyConnected.comp _ _, inferInstance⟩
