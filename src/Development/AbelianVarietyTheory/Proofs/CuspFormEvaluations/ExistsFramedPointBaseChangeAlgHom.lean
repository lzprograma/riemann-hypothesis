module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChange, Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChange =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChange", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals\npublic import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule\npublic import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso\npublic import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

namespace GenBaseChange

open VVRank EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isGenSec_pullS (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T)
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (pullS P.A 1 h th) :=
  EmbPull.isGenSec_pullS_of_baseChangeAt P (hS S P 1 le_rfl) h H

theorem gs_eq_zero {Y : Scheme.{0}} (f a : Γ(Y, ⊤)) (n : ℕ) (h : (Y.basicOpen f).ι.appTop.hom (a * f ^ n) = 0)
    (p : Y) (hp : p ∈ Y.basicOpen f) : gs (𝟙 Y) p ⊤ a = 0 := by
  let z : (Y.basicOpen f).toScheme := ⟨p, hp⟩
  have q := (gs_pull (𝟙 _) (Y.basicOpen f).ι z ⊤ trivial (a * f ^ n)).symm.trans
    ((congrArg (gs (𝟙 _) z _) h).trans (LBGerm.gs_zero _ z _ trivial))
  rw [Category.id_comp] at q
  replace q := (gs_stalkMap (Y.basicOpen f).ι z ⊤ trivial _).symm.trans q
  have q' : gs (𝟙 Y) p ⊤ (a * f ^ n) = 0 := PushInv.stalk_inj (Y.basicOpen f).ι z (q.trans (map_zero _).symm)
  rw [gs_mul _ p ⊤ trivial, LBGerm.gs_pow _ p ⊤ trivial] at q'
  have hu : IsUnit (gs (𝟙 Y) p ⊤ f) := by
    rw [gs_eq _ p ⊤ trivial]
    exact (Scheme.mem_basicOpen_top _ _ _).1 hp
  exact (hu.pow n).mul_left_eq_zero.1 q'

theorem basis_smul_eq_zero {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (c : Module.Basis κ R M) (i : κ)
    (x : R) (h : x • c i = 0) : x = 0 := by
  simpa using congrArg (fun q => c.repr q i) h

theorem eq_zero_of_smul (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) (a : Γ(T.left, ⊤))
    (ha : a • (SecM.ofSec P.A th : SecM P.A P.L 1 T) = 0) : a = 0 := by
  refine fn_ext fun p _ => Eq.trans ?_ (LBGerm.gs_zero _ p ⊤ trivial).symm
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
  have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have h0 : a • u = 0 := by rw [hr', smul_comm, ha, smul_zero]
  have e := congrArg (pullM P.A P.L 1 (overResι W)) h0
  rw [LinearMap.map_smulₛₗ, map_zero, hu, ← mul_smul, ← map_mul] at e
  have e' : (overResι W).left.appTop.hom (a * f ^ n) • c hq.default = 0 := by
    rw [hc]; exact e
  have e₂ := basis_smul_eq_zero c _ _ e'
  exact gs_eq_zero f a n e₂ p hp

theorem existsUnique_of_isPullSec (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left]
    (h : T' ⟶ T) {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) {th' : LB.Sec (LPow P.A P.L 1 T')}
    (hp : IsPullSec P.A P.L 1 (h ▷ P.A) (whiskerRight_snd _ _) th th') (s : LB.Sec (LPow P.A P.L 1 T')) :
    ∃! r : Γ(T'.left, ⊤), ∀ j, s.f j = liftFun P.A _ r * th'.f j := by
  have H' : IsGenSec P.A P.L 1 th' := fun s => by
    obtain ⟨r, hr⟩ := isGenSec_pullS P hS h H s
    exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (hp j).symm)⟩
  obtain ⟨r, hr⟩ := H' s
  refine ⟨r, hr, fun r' hr' => sub_eq_zero.1 (eq_zero_of_smul P hS H' _ ?_)⟩
  rw [sub_smul, sub_eq_zero]
  exact Subtype.ext (funext fun j => (hr' j).symm.trans (hr j))

theorem toΓ_bijective (R : Type) [CommRing R] : Function.Bijective (toΓ R) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

end GenBaseChange

theorem framedPoint_generator_baseChange :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] (ψ : S →+* T) (y : FrPt Xo c S) (h : ptO Xo (spMap ψ ≫ y.x) ⟶ ptO Xo y.x), h.left = spMap ψ → ∀ s' : LB.Sec (PPx (spMap ψ ≫ y.x)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s s' → ∀ s'' : LB.Sec (PPx (spMap ψ ≫ y.x)), ∃! a : T, ∀ i, s''.f i = scal (spMap ψ ≫ y.x) a i * s'.f i := by
  intro hL E _ _ _ H Dw l Xo c S T _ _ _ ψ y h _ s' hs' s''
  have := UnivPol.isLocallyNoetherian Xo
  have : IsAffine (ptO Xo y.x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (ptO Xo (spMap ψ ≫ y.x)).left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨r, hr, hu⟩ := GenBaseChange.existsUnique_of_isPullSec (UnivPol.pol Xo) hL.secBaseChange h
    (th := y.s) (fun s => by
      obtain ⟨a, ha, -⟩ := y.gen s
      exact ⟨toΓ S a, ha⟩) (th' := s') hs' s''
  obtain ⟨a, rfl⟩ := (GenBaseChange.toΓ_bijective T).2 r
  exact ⟨a, hr, fun a' ha' => (GenBaseChange.toΓ_bijective T).1 (hu _ ha')⟩

end GlobalTheory
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChange =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom", "h": "module\n\npublic import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed\npublic import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasis\npublic import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule\npublic import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChange\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

alias spMap_spMap := _root_.GlobalTheory.FrameBaseChange.spMap_spMap

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isTanAt_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_spMap, dualMap_comp_algebraMap, ← spMap_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_spMap, fstHom_comp_dualMap, ← spMap_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
        (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem isEigAt_pull {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap ψ y z := by
  intro hLaws E _ _ _ H Dw l Xo c S T _ _ _ _ ψ y
  let h : ptO Xo (spMap ψ.toRingHom ≫ y.x) ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) rfl
  obtain ⟨s', hs'⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G)
    (whiskerRight_snd _ _) y.s
  refine ⟨
    { x := spMap ψ.toRingHom ≫ y.x
      x_over := by
        rw [Category.assoc, y.x_over]
        unfold sOf
        rw [spMap_spMap, ← RingHom.comp_assoc]
        congr 2
        ext r
        simp
      u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i
      tan := fun τ i => isTanAt_pull ψ.toRingHom (y.tan τ i)
      eig := fun τ i => isEigAt_pull ψ τ (y.eig τ i)
      basis := fun τ w hw he => _root_.GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S T ψ y τ w hw he
      s := s'
      gen := _root_.GlobalTheory.framedPoint_generator_baseChange hLaws E H Dw l Xo c S T ψ.toRingHom y h rfl s' hs' },
    rfl, fun _ _ => rfl, (h ▷ Xo.univ.t.G).left, ?_, ?_, fun i hi => ?_⟩
  · rw [← Over.comp_left, whiskerRight_snd]
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    rfl
  · exact (hs' i).symm

end GlobalTheory.FramedBaseChange
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom =====
