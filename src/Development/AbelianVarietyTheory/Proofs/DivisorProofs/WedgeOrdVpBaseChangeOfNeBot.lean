module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section


noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

variable {R R' : Type} [CommRing R] [CommRing R']

theorem tanVal_baseChange {σ : R →+* R'} {A : Over (Sp R)} {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) σ φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (e : v'.left ≫ φ = spMap (dualMap σ) ≫ v.left) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = σ (tanVal v f) := by
  let E := SqExt.dual R
  let E' := SqExt.dual R'
  have hy := pt_w v
  have hy' := pt_w v'
  have hc : ∀ r : R, dualMap σ (algebraMap R (DualNumber R) r) = algebraMap R' (DualNumber R') (σ r) := fun r => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have e₀ : spMap σ ≫ spMap (E.π : E.C →+* E.B) ≫ v.left = (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Category.assoc, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    ext a <;> simp [dualMap, E, E', TrivSqZeroExt.algebraMap_eq_inl]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { dualMap σ with commutes' := hc }
      φ₀ := σ
      comm := fun b => by
        change σ b.fst = (dualMap σ b).fst
        simp [dualMap]
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => by
        have ha' : a.fst = 0 := ha
        change (dualMap σ a).fst = 0
        simp [dualMap, ha']
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { dualMap σ with commutes' := hc } e.symm
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { σ with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => (hc c).symm
  have k : E'.val v'.left hy' (m.pullForm f).1 = dualMap σ (E.val v.left hy f.1) :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      ((add_sub_add_right_eq_sub (G := E'.C) _ _ _).trans (map_sub (dualMap σ) _ _).symm)
  rw [tanVal_apply, tanVal_apply]
  refine (congrArg (TrivSqZeroExt.snd (R := R')) k).trans ?_
  exact zero_add _

section

variable [Algebra R R'] {A : Over (Sp R)} [GrpObj A] {B : Over (Sp R')} [GrpObj B] {φ : B.left ⟶ A.left}
  {hφ : IsGrpPullback B A (spMap (algebraMap R R')) φ}

theorem mem_Fil_of_corr (hF : PrimitiveSubmodule B = Submodule.span R' ((bcMor hφ).pull '' (PrimitiveSubmodule A))) {h : HdR A}
    {h' : HdR B} (e : (bcMor hφ).Corr h h') (hh : h ∈ Fil A) : h' ∈ Fil B := by
  rw [Fil, hF, Submodule.mem_dualAnnihilator]
  intro c hc
  refine (Submodule.span_le (p := LinearMap.ker h')).2 (fun c hc => ?_) hc
  obtain ⟨c, hc, rfl⟩ := hc
  exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hh c hc, map_zero])

theorem IsLieImage.baseChange (hF : PrimitiveSubmodule B = Submodule.span R' ((bcMor hφ).pull '' (PrimitiveSubmodule A)))
    (hL : LieExact B) {h : HdR A} {h' : HdR B} (e : (bcMor hφ).Corr h h') {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (ev : v'.left ≫ φ = spMap (dualMap (algebraMap R R')) ≫ v.left) (hv : IsLieImage h v) : IsLieImage h' v' := open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in open scoped CategoryTheory.Obj in by
  have ht : IsTangent v' := ArcQ.NormalForm.isTangent_baseChange hφ ev hv.1
  obtain ⟨k, hk⟩ := hL.2 v' ht
  have : h' - k ∈ Fil B := by
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker (h' - k))).2 (fun c hc => ?_) hc
    obtain ⟨⟨c, hc'⟩, hc, rfl⟩ := hc
    change c ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨f, rfl⟩ := hc
    change h' _ - k _ = 0
    rw [e, hv.2 f hc', ← tanVal_baseChange (bcMor hφ).isMor ev f, sub_eq_zero]
    exact (hk.2 _ ((bcMor hφ).pullback_mem_primitive hc')).symm
  refine ⟨ht, fun f hf => ?_⟩
  rw [← hk.2 f hf, ← sub_eq_zero]
  exact mem_Fil.1 this f hf



theorem IsKSValue.baseChange (P : AbelianDeRham) {A' : Over (Sp (DualNumber R))} [GrpObj A']
    {B' : Over (Sp (DualNumber R'))} [GrpObj B'] {g : ℕ} (hA : IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {i : A.left ⟶ A'.left} {j : B.left ⟶ B'.left}
    {h : IsGrpPullback A A' (epsRed R) i} (h' : IsGrpPullback B B' (epsRed R') j) {φ' : B'.left ⟶ A'.left}
    (hφ' : IsGrpPullback B' A' (spMap (dualMap (algebraMap R R'))) φ') (sq : j ≫ φ' = φ ≫ i)
    {f : HdR A} {f' : HdR B} (e : (bcMor hφ).Corr f f') {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (ev : v'.left ≫ φ = spMap (dualMap (algebraMap R R')) ≫ v.left) (hv : IsKSValue h f v) :
    IsKSValue h' f' v' := by
  obtain ⟨-, PH, PB, PR, -⟩ := P
  have st : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
      {q : G'.left ⟶ G.left}, IsGrpPullback G' G b q → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom →
      IsAbelianScheme G' ∧ SmoothOfRelativeDimension g G'.hom := fun k l =>
    ⟨PolPull.isAbelianScheme_of_isGrpPullback l.1 k,
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback k.1 l.2⟩
  have a₀ := st h ⟨hA, hg⟩
  have b₁ := st hφ' ⟨hA, hg⟩
  have b₀ := st hφ a₀
  let : Algebra (DualNumber R) (DualNumber R') := (dualMap (algebraMap R R')).toAlgebra
  obtain ⟨bc₀, hF₀⟩ := PB R A g a₀.1 a₀.2 R' B φ hφ
  obtain ⟨bc₁, hF₁⟩ := PB _ A' g hA hg _ B' φ' hφ'
  have su : ∀ (S : Type) [CommRing S], Function.Surjective (TrivSqZeroExt.fstHom S S S).toRingHom :=
    fun S _ r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := PR _ A' g hA hg _ (epsDP R) (isDPNilpotent_squareZero _) R _ (su R) rfl A i h
  have rB := PR.crysToDR_bijective b₁.1 b₁.2 (κ := epsDP R') (isDPNilpotent_squareZero _) (su R') rfl h'
  obtain ⟨k, ⟨d, hd, ed⟩, hk⟩ := hv
  obtain ⟨k', ek⟩ := bc₀.exists k
  obtain ⟨x', ex⟩ := bc₁.exists (crysToDR (epsDP R) h d)
  obtain ⟨d', rfl⟩ := rB.2 x'
  have m : GrpMor (epsDP R) (epsRed R) A (epsDP R') (epsRed R') B (dualMap (algebraMap R R'))
      (spMap (algebraMap R R')) φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_sqDP _ _ _ fun a ha => by
      have ha' : a.fst = 0 := ha
      change (dualMap (algebraMap R R') a).fst = 0
      simp [dualMap, ha']) (by
      rw [← Cris.spMap_comp, ← Cris.spMap_comp]
      congr 1
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]) hφ
  have em : m.Corr d d' := fun c => by
    obtain ⟨c, rfl⟩ := rA.2 c
    have n := (liftMor (epsDP R) h).comp m
    rw [GrpMor.pull_pull (liftMor (epsDP R) h) m n (fun _ => rfl) rfl c,
      ← GrpMor.pull_pull (bcMor hφ') (liftMor (epsDP R') h') n (fun _ => rfl) sq c]
    exact ex c
  refine ⟨k', ⟨d', (mem_Fil_of_corr (hφ := hφ') hF₁ ex hd :), fun c => ?_⟩,
    hk.baseChange (hφ := hφ) hF₀ (PH R' B g b₀.1 b₀.2).1 ek ev⟩
  obtain ⟨z, rfl⟩ := bc₀.2 c
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero, LinearMap.map_zero, LinearMap.map_zero]
    simp
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy]
    ext <;> simp
  | tmul r c =>
    have n := (constMor A).comp m
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, map_smul,
      GrpMor.pull_pull (bcMor hφ) (constMor B) n (fun _ => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c,
      ← GrpMor.pull_pull (constMor A) m n (fun _ => rfl) rfl c, em, ed, e, ek]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def, mul_comm]

end

theorem IsPolForm.pull_comp {A : Over (Sp R)} [GrpObj A] {B : Over (Sp R')} [GrpObj B] {σ : R →+* R'}
    {b : Sp R' ⟶ Sp R} {φ : B.left ⟶ A.left} (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) B σ b φ)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {π : A.left ⟶ X} {ψ : LinearMap.BilinForm R (HdR A)}
    (h : IsPolForm (dp0 R) (𝟙 _) A (L.pull π) ψ) :
    ∃ ψ', IsPolForm (dp0 R') (𝟙 _) B (L.pull (φ ≫ π)) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hc, e⟩, h'⟩ := h.pull m
  refine ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (pull_isLB hL _) _)
    (pull_isLB hL _) ?_ _ hc, e⟩, h'⟩
  exact LBIso.chartPull (Geo.Tor.chartPullPull (L.pull π) φ φ rfl) (chartPullSame L _ _ _ φ fun _ => rfl)
    (ChernExists.lbIso_refl (pull_isLB hL π))

end GlobalTheory.DeRham

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Field

variable {K K' : Type} [Field K] [Algebra c.F K] [Field K'] [Algebra c.F K'] {K₀ : Type} [CommRing K₀]
  [Algebra c.F K₀] {ι : Type} [Fintype ι] {Φ : Finset (E →+* ℂ)} {ψ : K →ₐ[c.F] K'} {y : FrPt Xo c K}
  {y' : FrPt Xo c K'}


open scoped CategoryTheory.Obj in
theorem exists_isGrpPullback {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    ∃ (G' : Over S') (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ :=
  ⟨_, inferInstance, _, isGrpPullback_pullback G f⟩

end Field

section Norm

variable {T T' : CDVR} {io : c.F →+* T.Fr} {io' : c.F →+* T'.Fr} {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]
  {ι : Type} [Fintype ι] {Φ : Finset (E →+* ℂ)}

variable (P : AbelianDeRham) (ψ : letI := io.toAlgebra; CoefHom c io' T.Fr) {r : ℕ} (hr : 0 < r)
  (hψ : ∀ x, vV T'.V (ψ x) = (r : ℤ) * vV T.V x) {φ : CoefHom c io K₀} {φ' : CoefHom c io' K₀}
  (hφ : ∀ a, ψ (φ a) = φ' a) {y : IntFr Xo c T io} {y' : IntFr Xo c T' io'}
  (h : letI := io.toAlgebra; letI := io'.toAlgebra; FrMap ψ y.1 y'.1) {e : Ix Dw → ℤ} {s₀ : RulK Xo c K₀}
  (h₀ : s₀ ∈ secK Xo c K₀ e) {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e)



variable (k : letI := io.toAlgebra; KSIso Φ y.1) (k' : letI := io'.toAlgebra; KSIso Φ y'.1)

end Norm

end GlobalTheory.FlagTan
