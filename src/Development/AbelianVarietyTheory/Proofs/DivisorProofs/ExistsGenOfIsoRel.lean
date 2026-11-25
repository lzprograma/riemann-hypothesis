module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpBundleFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSecOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef

section Tools

variable {X X₂ Y : Scheme.{0}}

def isoV {A C : LB Y} (u : LB.Iso A C) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : C.ι) (a : A.ι) :
    (Z.presheaf.stalk z)ˣ := gm r z (C.U c ⊓ A.U a) (u.s (c, a))

def flatChart (L : LB X₂) {I K : Type} [Fintype I] [Fintype K] (π : I → (X ⟶ X₂)) (e : I → ℤ) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : ChartPull (LB.LinComb L (fun p : K × I => φ p.1 ≫ π p.2) (fun p => ε p.1 * e p.2))
      (LB.LinComb (LB.LinComb L π e) φ ε) (𝟙 Y) :=
  have le : ∀ j : K × I → L.ι, LB.wchart L (fun p : K × I => φ p.1 ≫ π p.2) j ≤
      LB.wchart (LB.LinComb L π e) φ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  { idx := fun j k i => j (k, i)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_
        (gm_linComb (LB.LinComb L π e) φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun k _ => Eq.symm ?_
      refine (congrArg (· ^ ε k) (gm_linComb L π e (𝟙 Y ≫ φ k) y (fun i => j (k, i)) (fun i => j' (k, i))
        (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k))).trans ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_mul, mul_comm (e i), Category.assoc] }

theorem isoV_isoPull {A' C' A C : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull C' C (𝟙 Y)) (u : LB.Iso A C)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : C'.ι) (i : A'.ι) (hc : r z ∈ C'.U c) (hi : r z ∈ A'.U i) :
    isoV (TautFrom.isoPull a b u) r z c i = isoV u r z (b.idx c) (a.idx i) :=
  (TautFrom.gm_isoPull a b u r z (c, i) ⟨hc, hi⟩).trans (by rw [Category.comp_id]; rfl)

theorem isoV_linComb {A C : LB X} (u : LB.Iso A C) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : K → C.ι) (a : K → A.ι) (hc : r z ∈ LB.wchart C φ c)
    (ha : r z ∈ LB.wchart A φ a) :
    isoV (LB.linCombIso u φ ε) r z c a = ∏ k, isoV u (r ≫ φ k) z (c k) (a k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart C φ c ⊓ LB.wchart A φ a from ⟨hc, ha⟩) _).trans
    (gm_pull r (φ k) z (C.U (c k) ⊓ A.U (a k)) ⟨Set.mem_iInter.1 hc k, Set.mem_iInter.1 ha k⟩ _)

variable {L : LB X} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (X ⟶ X₂)} {e : I → ℤ}

def om (u : LB.Iso L (LB.LinComb L₂ π e)) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J₂ : (Z ⟶ X₂) → L₂.ι)
    (x : Z ⟶ X) : (Z.presheaf.stalk z)ˣ := isoV u x z (fun i => J₂ (x ≫ π i)) (J x)

theorem exists_transport (u : LB.Iso L (LB.LinComb L₂ π e)) (hu : u.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : ∃ U : LB.Iso (LB.LinComb L φ ε)
      (LB.LinComb L₂ (fun p : K × I => φ p.1 ≫ π p.2) (fun p => ε p.1 * e p.2)), U.IsGen ∧
      ∀ (s : LB.Sec (LB.LinComb L φ ε)) s', DVR.FlatBC.IsoRel U s s' →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J₂, Good L z J → Good L₂ z J₂ →
          sval s' r z J₂ = (∏ k, om u z J J₂ (r ≫ φ k) ^ ε k).val * sval s r z J := by
  refine ⟨TautFrom.isoPull (chartPullId _) (flatChart L₂ π e φ ε) (LB.linCombIso u φ ε),
    TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen u hu φ ε), fun s s' hs Z r z J J₂ hJ hJ₂ => ?_⟩
  refine (gs_isoRel_at hs _ _ r z (hJ₂.mem _ r) (hJ.mem φ r)).trans (congrArg (fun t => Units.val t * _) ?_)
  refine (isoV_isoPull _ _ _ r z _ _ (hJ₂.mem _ r) (hJ.mem φ r)).trans ?_
  refine (isoV_linComb u φ ε r z _ _ ((flatChart L₂ π e φ ε).le _ (hJ₂.mem _ r)) (hJ.mem φ r)).trans ?_
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  simp only [om, Category.assoc]
  rfl

end Tools

section Galois

variable {V₁ W₀ K : Type} [CommRing V₁] [CommRing W₀] [Field K] {A : Over (Sp V₁)} [GrpObj A] {B₀ : Over (Sp W₀)}
  [GrpObj B₀] (f : W₀ →+* V₁) (q : Fin 8 → (A.left ⟶ B₀.left))

def PowPts : Prop := ∀ (T : Over (Sp V₁)) (g : T.left ⟶ Sp W₀), T.hom ≫ spMap f = g →
  ∃ Φ : (T ⟶ A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)), ∀ x a, (Φ x a).left = x.left ≫ q a

variable (ev : V₁ →+* K) (k₀ : Subfield K)

def IsConj (σ : K ≃+* K) (σt : (Over.mk (spMap ev) ⊗ A).left ⟶ (Over.mk (spMap ev) ⊗ A).left) : Prop :=
  σt ≫ (fst (Over.mk (spMap ev)) A).left = (fst (Over.mk (spMap ev)) A).left ≫ spMap σ.toRingHom ∧
    ∀ a, σt ≫ (snd (Over.mk (spMap ev)) A).left ≫ q a = (snd (Over.mk (spMap ev)) A).left ≫ q a

def RatM (ψ : (Over.mk (spMap ev) ⊗ A).left ⟶ A.left) : Prop :=
  ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ σt, IsConj q ev σ σt → ∀ a, σt ≫ ψ ≫ q a = ψ ≫ q a

def RatP (x : Sp K ⟶ A.left) : Prop := ∀ a, DefOver k₀ (x ≫ q a)

variable {f q ev k₀}

theorem ratM_const (x : Over.mk (spMap ev) ⟶ A) (hx : RatP q k₀ x.left) :
    RatM q ev k₀ (fst (Over.mk (spMap ev)) A ≫ x).left := fun σ hσ σt h a => by
  obtain ⟨P₀, hP₀⟩ := hx a
  show σt ≫ ((fst (Over.mk (spMap ev)) A).left ≫ x.left) ≫ q a = ((fst (Over.mk (spMap ev)) A).left ≫ x.left) ≫ q a
  simp only [Category.assoc]
  rw [reassoc_of% h.1]
  erw [← hP₀]
  congr 1
  rw [← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]

theorem ratM_one (h1 : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ A).left) :
    RatM q ev k₀ (1 : Over.mk (spMap ev) ⊗ A ⟶ A).left := by
  have := ratM_const 1 h1
  rwa [MonObj.comp_one] at this

variable {L : LB A.left} {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (A.left ⟶ X₂)} {e : I → ℤ}

end Galois

section Normalised

open GlobalTheory.UT

variable {V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Fin 8 → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}

structure Desc (f : W₀ →+* V₁) (q : Fin 8 → (D.P.A.left ⟶ B₀.left)) (ev : V₁ →+* K) (k₀ : Subfield K)
    (u : LB.Iso D.P.L (LB.LinComb L₂ π e)) : Prop where
  hk₀ : IsAlgClosed k₀
  hP : PowPts f q
  hk : ∀ a, ev (f a) ∈ k₀
  hL₂ : L₂.IsLB
  hu : u.IsGen
  hπ : ∀ (Z : Scheme.{0}) (x y : Z ⟶ D.P.A.left), (∀ a, x ≫ q a = y ≫ q a) → ∀ i, x ≫ π i = y ≫ π i
  one : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left

variable {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

end Normalised

section Omega

open GlobalTheory.UT GlobalTheory.UT.SymFrame

variable {V V₁ W₀ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W₀]
  (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
  (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀]
  (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)

abbrev piB (p : (Fin 8 × Fin 8) × PUnit × ULift.{0} (Finset (Fin 2))) : D.P.A.left ⟶ B₀.left :=
  sharpPair ρ Q D pr p.1.1 p.1.2 ≫ β₂ ≫ (psum B₀ (x2 B₀) p.2.2.down).left

abbrev exB (p : (Fin 8 × Fin 8) × PUnit × ULift.{0} (Finset (Fin 2))) : ℤ :=
  W p.1.1 p.1.2 * (1 * (-1) ^ (2 - p.2.2.down.card))

end Omega

end GlobalTheory.Poinc.Sep.Coef
