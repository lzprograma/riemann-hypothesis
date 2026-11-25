module

public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GaugeR

def IsScaled {Y : Scheme.{0}} {M : LB Y} (u : Γ(Y, ⊤)ˣ) (t t' : LB.Gen M) : Prop :=
  ∀ j, t'.s j = res le_top u * t.s j

def pullUnit {Y Z : Scheme.{0}} (h : Z ⟶ Y) (u : Γ(Y, ⊤)ˣ) : Γ(Z, ⊤)ˣ :=
  pullU h ⊤ u

variable {X Y Z : Scheme.{0}} (L : LB X)

theorem ratio_of_gen (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t t' : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ u, IsScaled u t t' := by
  exact gen_ratio (LB.LinComb L φ ε) (wchart_cover L hL φ) t' t ht' ht

theorem scaled_one {M : LB Y} (t : LB.Gen M) : IsScaled 1 t t := by
  intro j
  rw [map_one, one_mul]

theorem scaled_mul {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) {u v : Γ(Y, ⊤)ˣ} {t t' : LB.Gen (LB.LinComb L φ ε)}
    {s s' : LB.Gen (LB.LinComb L φ' ε')} (h1 : IsScaled u t t') (h2 : IsScaled v s s') :
    IsScaled (u * v) (LB.mulGen L φ ε φ' ε' t s) (LB.mulGen L φ ε φ' ε' t' s') := by
  intro (j : K ⊕ K' → L.ι)
  let tj : Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ := t.s (j ∘ Sum.inl)
  let tj' : Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ := t'.s (j ∘ Sum.inl)
  let sj : Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ := s.s (j ∘ Sum.inr)
  let sj' : Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ := s'.s (j ∘ Sum.inr)
  have h1j : tj' = res (le_top : LB.wchart L φ (j ∘ Sum.inl) ≤ ⊤) u * tj := h1 (j ∘ Sum.inl)
  have h2j : sj' = res (le_top : LB.wchart L φ' (j ∘ Sum.inr) ≤ ⊤) v * sj := h2 (j ∘ Sum.inr)
  have hl : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) := fun _ hx =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
  have hr : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) := fun _ hx =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
  change res hl tj' * res hr sj' =
    res (le_top : LB.wchart L (Sum.elim φ φ') j ≤ ⊤) (u * v) * (res hl tj * res hr sj)
  rw [h1j, h2j, map_mul, map_mul, map_mul, res_res, res_res, mul_mul_mul_comm]

theorem pullUnit_res (h : Z ⟶ Y) {V : Y.Opens} {W : Z.Opens} (hWV : W ≤ h ⁻¹ᵁ V) (u : Γ(Y, ⊤)ˣ) :
    res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) = res le_top (pullUnit h u) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, res_res]
  rfl

theorem scaled_pull {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (hs : IsScaled u t t') :
    IsScaled (pullUnit h u) (LB.pullGen L φ ε t h) (LB.pullGen L φ ε t' h) := by
  intro (j : K → L.ι)
  let tj : Γ(Y, LB.wchart L φ j)ˣ := t.s j
  let tj' : Γ(Y, LB.wchart L φ j)ˣ := t'.s j
  have hsj : tj' = res (le_top : LB.wchart L φ j ≤ ⊤) u * tj := hs j
  have hp : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hx =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  change res hp (pullU h (LB.wchart L φ j) tj') =
    res (le_top : LB.wchart L (fun k => h ≫ φ k) j ≤ ⊤) (pullUnit h u) *
      res hp (pullU h (LB.wchart L φ j) tj)
  rw [hsj, map_mul, map_mul, pullUnit_res]

theorem corr_scaled (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t₁ t₁' : LB.Gen (LB.LinComb L φ ε))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U₁ U₂ : Γ(Y, ⊤)ˣ) (h₁ : IsScaled U₁ t₁ t₁')
    (h₂ : IsScaled U₂ t₂ t₂') (c : LB.Gen.Corr L φ ε φ' ε' t₁ t₂) (c' : LB.Gen.Corr L φ ε φ' ε' t₁' t₂') :
    U₁ = U₂ := by
  classical
  have hch : ∀ (ψ : Y ⟶ X) (y : Y), ∃ i, ψ y ∈ L.U i := by
    intro ψ y
    have hy := wchart_cover L hL (fun _ : Fin 1 => ψ) (show y ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨j 0, Set.mem_iInter.1 hj 0⟩
  apply Units.ext
  have hcov : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₁ : Γ(Y, ⊤)) =
        (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₂ : Γ(Y, ⊤)) := by
    intro y
    choose ch hc using fun ψ => hch ψ y
    let j : K → L.ι := fun k => ch (φ k)
    let j' : K' → L.ι := fun k => ch (φ' k)
    have hj : LB.Coh L φ j := fun k1 k2 e => show ch (φ k1) = ch (φ k2) by rw [e]
    have hj' : LB.Coh L φ' j' := fun k1 k2 e => show ch (φ' k1) = ch (φ' k2) by rw [e]
    have hjj : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' e => show ch (φ k) = ch (φ' k') by rw [e]
    have hyW : y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' :=
      ⟨Set.mem_iInter.2 fun k => hc (φ k), Set.mem_iInter.2 fun k => hc (φ' k)⟩
    let s1 : Γ(Y, LB.wchart L φ j)ˣ := t₁.s j
    let s1' : Γ(Y, LB.wchart L φ j)ˣ := t₁'.s j
    let s2 : Γ(Y, LB.wchart L φ' j')ˣ := t₂.s j'
    let s2' : Γ(Y, LB.wchart L φ' j')ˣ := t₂'.s j'
    have E : res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) s1 =
        res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) s2 :=
      c j j' hj hj' hjj
    have E' : res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) s1' =
        res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) s2' :=
      c' j j' hj hj' hjj
    have h₁j : s1' = res (le_top : LB.wchart L φ j ≤ ⊤) U₁ * s1 := h₁ j
    have h₂j : s2' = res (le_top : LB.wchart L φ' j' ≤ ⊤) U₂ * s2 := h₂ j'
    rw [h₁j, h₂j, map_mul, map_mul, res_res, res_res, E] at E'
    have E2 := mul_right_cancel E'
    exact ⟨_, hyW, congrArg Units.val E2⟩
  choose W hyW hW using hcov
  exact TopCat.Sheaf.eq_of_locally_eq' Y.sheaf W ⊤ (fun y => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩) _ _ hW

theorem corr_scaled_left (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type} [Fintype K'] (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (τ τ' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U : Γ(Y, ⊤)ˣ) (h₂ : IsScaled U t₂ t₂')
    (c : LB.Gen.Corr L _ _ _ _ τ t₂) (c' : LB.Gen.Corr L _ _ _ _ τ' t₂') : IsScaled U τ τ' := by
  let τ'' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a) :=
    ⟨fun j => res le_top U * τ.s j⟩
  have hc'' : LB.Gen.Corr L _ _ _ _ τ'' t₂' := by
    intro j j' hj hj' hm
    let τj : Γ(Y, LB.wchart L (fun _ : Fin 1 => ψ) j)ˣ := τ.s j
    let s2 : Γ(Y, LB.wchart L φ' j')ˣ := t₂.s j'
    let s2' : Γ(Y, LB.wchart L φ' j')ˣ := t₂'.s j'
    have hcj : res (inf_le_left : LB.wchart L (fun _ : Fin 1 => ψ) j ⊓ LB.wchart L φ' j' ≤ _) τj =
        res (inf_le_right : LB.wchart L (fun _ : Fin 1 => ψ) j ⊓ LB.wchart L φ' j' ≤ _) s2 :=
      c j j' hj hj' hm
    have h₂j' : s2' = res (le_top : LB.wchart L φ' j' ≤ ⊤) U * s2 := h₂ j'
    change res (inf_le_left : LB.wchart L (fun _ : Fin 1 => ψ) j ⊓ LB.wchart L φ' j' ≤ _)
        (res (le_top : LB.wchart L (fun _ : Fin 1 => ψ) j ≤ ⊤) U * τj) =
      res (inf_le_right : LB.wchart L (fun _ : Fin 1 => ψ) j ⊓ LB.wchart L φ' j' ≤ _) s2'
    rw [h₂j', map_mul, map_mul, hcj, res_res, res_res]
  have he := GermFun.gen_eq_of_corr L hL ψ a φ' ε' τ'' τ' t₂' hc'' c'
  intro j
  rw [← he]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
