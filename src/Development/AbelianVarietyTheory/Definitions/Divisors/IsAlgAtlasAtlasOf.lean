module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}


instance compactSpace_pts (σ : F →+* ℂ) : CompactSpace (Pts Y σ) := CxPts.compactSpace σ Y.isProjOver




section Norms

variable {σ : F →+* ℂ} {Δ : Y.Dv}

abbrev genAt (Δ : Y.Dv) (x : Y.X) : Y.Fn := ((eqn Δ x)⁻¹ : Y.Fnˣ)


def lnN (m : C.Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ) : ℝ := Real.log (C.pn Y σ Δ m (C.cx Y σ f) y) / 2

def lnRatio (m m' : C.Met Y σ Δ) (y : Pts Y σ) : ℝ :=
  lnN m (genAt Δ (under y)) y - lnN m' (genAt Δ (under y)) y

end Norms

structure Cover (Y : Var F) : Type 1 where

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  G : Scheme.{0}
  [intG : IsIntegral G]

  j : G ⟶ X

  π : G ⟶ Y.X

  pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))
  [fin : IsFinite π]
  [surj : Surjective π]

  φ : Y.Fn →+* G.functionField

  φ_spec : G.fromSpecStalk (genericPoint G) ≫ π = spMap φ ≫ Y.X.fromSpecStalk (genericPoint Y.X)

attribute [instance] Cover.int Cover.intG Cover.fin Cover.surj

namespace Cover

variable (V : Cover Y)

def deg : ℕ := V.π.residueDegree (genericPoint V.G)

theorem deg_pos : 0 < V.deg := by
  let := (V.π.residueFieldMap (genericPoint V.G)).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π (genericPoint V.G))) (V.G.residueField (genericPoint V.G)) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

def ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : Cover Y where
  X := M.X
  int := M.ar.isIntegral
  p := M.p
  ar := M.ar
  normal := h
  G := Y.X
  j := M.j
  π := 𝟙 _
  pb := by simpa using M.pb
  φ := RingHom.id _
  φ_spec := (Category.comp_id _).trans ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm

def Induces (A : Adl C Y) (L : HermLB V.p) (k : ℕ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) ^ k * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (V.φ (genAt A.D (under y)) ^ k * (r i : V.G.functionField)) z‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      k * A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r i : V.G.functionField))))

end Cover

end GlobalTheory.Mean4O
