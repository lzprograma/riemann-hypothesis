module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat

noncomputable section

namespace GlobalTheory.Heat.Adjust

theorem valR_const {K R : Type} [CommRing K] [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp K) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

theorem eq_zero_of_valR_points {X : Scheme.{0}} (U : X.Opens) (s : Γ(X, U))
    (h : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valR g U s = 0) : s = 0 := by
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W : X.affineOpens // W.1 ≤ U}) (fun W => W.1.1) (fun W => W.2) ?_ s 0 ?_
  · intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · rintro ⟨⟨W, hW⟩, hWU⟩
    have hW' : IsAffineOpen W := hW
    have hle : ⊤ ≤ hW'.fromSpec ⁻¹ᵁ W := hW'.fromSpec_preimage_self.ge
    have e := h Γ(X, W) hW'.fromSpec (hle.trans (hW'.fromSpec.preimage_mono hWU))
    rw [← HolHom.valR_res (A := Γ(X, W)) hW'.fromSpec hWU s hle, HolHom.valR_eq _ _ hle, HolHom.evalHom] at e
    rw [GlobalTheory.KS.rsT_zero, GlobalTheory.KS.rsT_of_le hWU]
    have e2 : hW'.fromSpec.appLE W ⊤ hle = (Scheme.ΓSpecIso Γ(X, W)).inv := by
      rw [Scheme.Hom.appLE, hW'.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
    erw [e2] at e
    erw [Iso.inv_hom_id] at e
    exact e

theorem inv_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    (dd : Fld G.left) (hinv : IsInv G v dd) (V : G.left.Opens) (r : R) : dd V (constFn G.hom V r) = 0 := by
  apply _root_.GlobalTheory.Heat.isInv_constFn <;> assumption

theorem isField_add_comb {Z : Scheme.{0}} {n : ℕ} {U : Z.Opens} (d₀ : Fld Z) (dd : Fin n → Fld Z)
    (y : Fin n → Γ(Z, U)) (h₀ : IsField U d₀) (h : ∀ a, IsField ⊤ (dd a)) :
    IsField U (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hWW hW f => ?_⟩
  · simp only [h₀.1 W hW, fun a => (h a).1 W le_top, mul_add, Finset.sum_add_distrib]
    ring
  · simp only [h₀.2.1 W hW, fun a => (h a).2.1 W le_top, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have e : ∀ (g : Γ(Z, W)) (u : Fin n → Γ(Z, W)), ∑ a, rsT (y a) W * (g * u a) = ∑ a, g * (rsT (y a) W * u a) :=
      fun g u => Finset.sum_congr rfl fun a _ => by ring
    rw [e, e]
    ring

  · simp only [h₀.2.2 W W' hWW hW, fun a => (h a).2.2 W W' hWW le_top, map_add (f := _), map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← GlobalTheory.KS.rsT_of_le hWW (rsT (y a) W), GlobalTheory.KS.rsT_rsT hW hWW]

theorem isWt_rsT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {α : Q.X} {V V' : Y.H.left.Opens} (h : V' ≤ V) {f : Γ(Y.H.left, V)}
    (hf : IsWt Y α V f) : IsWt Y α V' (rsT f V') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.KS.rsT_of_le h]
  refine (HolHom.valR_res a' h f hV').trans (Eq.trans ?_ (congrArg _ (HolHom.valR_res a h f hV)).symm)
  exact hf S φ x x' c a a' ha ha' (hV.trans (a.preimage_mono h)) (hV'.trans (a'.preimage_mono h)) hq hc

theorem isLift_add_invComb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (V : Dd.toPre.P.A.left.Opens) (d₀ : Fld Y.H.left) (y : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d₀ → (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d₀ _ f)) → (∀ a, IsWt Y 0 _ (y a)) → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) ∧ (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') ((fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D V d₀ y hd hw hy
  refine ⟨⟨isField_add_comb d₀ dd y hd.1 fun a => (hinv a).1, fun W hW r => ?_⟩, fun α V' hV' f hf => ?_⟩
  · simp only [hd.2 W hW r, fun a => inv_constFn Y.H (v a) (dd a) (hinv a) W r, mul_zero, Finset.sum_const_zero,
      add_zero]
  · exact WtAlg.isWt_add (hw α V' hV' f hf) (WtAlg.isWt_sum _ _ fun a _ =>
      WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (isWt_rsT Y hV' (hy a)) (IsInv.isWt Y (v a) (dd a) (hinv a) α _ f hf))

end GlobalTheory.Heat.Adjust
