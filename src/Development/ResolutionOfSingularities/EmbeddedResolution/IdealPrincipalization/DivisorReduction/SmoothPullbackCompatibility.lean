module

import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem get_eq_get_of_take_succ_eq {α : Type*} (l₁ l₂ : List α) (j : ℕ)
    (htake : List.take (j + 1) l₁ = List.take (j + 1) l₂)
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) :
    l₁.get ⟨j, h₁⟩ = l₂.get ⟨j, h₂⟩ := by
  have h := congrArg (·[j]?) htake
  rw [List.getElem?_take_of_succ, List.getElem?_take_of_succ,
    List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at h
  exact Option.some.inj h

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {E E' : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (E.map fun D => D.comap f) (E'.map fun D => D.comap f) :=
  h.map (fun D => D.comap f) (Scheme.IdealSheafData.comap_top f)

private theorem nontrivialPart_cons_congr {X : Scheme.{u}} {a : X.IdealSheafData}
    {s t : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.nontrivialPart s = MarkedIdealWithBoundary.nontrivialPart t) :
    MarkedIdealWithBoundary.nontrivialPart (a :: s) = MarkedIdealWithBoundary.nontrivialPart (a :: t) := by
  simp only [MarkedIdealWithBoundary.nontrivialPart] at h
  simp only [MarkedIdealWithBoundary.nontrivialPart]
  rw [List.filter_cons, List.filter_cons, h]

private theorem nontrivialPart_eq_of_cons_eq {X : Scheme.{u}} {a : X.IdealSheafData}
    {s t : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.nontrivialPart (a :: s) = MarkedIdealWithBoundary.nontrivialPart (a :: t)) :
    MarkedIdealWithBoundary.nontrivialPart s = MarkedIdealWithBoundary.nontrivialPart t := by
  simp only [MarkedIdealWithBoundary.nontrivialPart] at h
  simp only [MarkedIdealWithBoundary.nontrivialPart]
  rw [List.filter_cons, List.filter_cons] at h
  split_ifs at h with hp
  · simpa using h
  · exact h

private theorem nontrivialPart_eraseIdx_eq_of_take_succ_eq {X : Scheme.{u}} (j : ℕ) :
    ∀ E E' : List X.IdealSheafData,
      MarkedIdealWithBoundary.nontrivialPart E = MarkedIdealWithBoundary.nontrivialPart E' →
      List.take (j + 1) E = List.take (j + 1) E' →
      MarkedIdealWithBoundary.nontrivialPart (E.eraseIdx j) = MarkedIdealWithBoundary.nontrivialPart (E'.eraseIdx j) := by
  induction j with
  | zero =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [List.take_succ_cons, List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨hab, -⟩ := htake
        subst hab
        exact nontrivialPart_eq_of_cons_eq h
  | succ j ih =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [List.take_succ_cons, List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨hab, htl⟩ := htake
        subst hab
        exact nontrivialPart_cons_congr (ih s t (nontrivialPart_eq_of_cons_eq h) htl)

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.eraseIdx {X : Scheme.{u}} {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') (j : ℕ)
    (htake : List.take (j + 1) E = List.take (j + 1) E') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (E.eraseIdx j) (E'.eraseIdx j) :=
  (MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).2
    (nontrivialPart_eraseIdx_eq_of_take_succ_eq j E E' ((MarkedIdealWithBoundary.sameNontrivialBoundary_iff _ _).1 h) htake)

namespace DivisorReduction

def subschemeMapOfComap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData) (D' : Y.IdealSheafData)
    (hD : D' = D.comap h) : D'.subscheme ⟶ D.subscheme :=
  D'.subschemeMap D h (hD ▸ D.le_map_comap h)

theorem subschemeMapOfComap_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
  D'.subschemeMap_subschemeι ..

theorem comap_subschemeMapOfComap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) (I₀ : X.IdealSheafData) :
    (I₀.comap D.subschemeι).comap (subschemeMapOfComap h D D' hD) = (I₀.comap h).comap D'.subschemeι := by
  rw [← Scheme.IdealSheafData.comap_comp, subschemeMapOfComap_comp, Scheme.IdealSheafData.comap_comp]

theorem sameNontrivialBoundary_comap_subschemeι {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) (M : List X.IdealSheafData)
    (M' : List Y.IdealSheafData)
    (hM : MarkedIdealWithBoundary.SameNontrivialBoundary M' (M.map fun I => I.comap h)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (M'.map fun I => I.comap D'.subschemeι)
      ((M.map fun I => I.comap D.subschemeι).map fun I => I.comap (subschemeMapOfComap h D D' hD)) := by
  have hmap : ((M.map fun I => I.comap h).map fun I => I.comap D'.subschemeι) =
      (M.map fun I => I.comap D.subschemeι).map fun I =>
        I.comap (subschemeMapOfComap h D D' hD) := by
    simp only [List.map_map, Function.comp_def, comap_subschemeMapOfComap]
  rw [← hmap]
  exact hM.comap D'.subschemeι

/-- The preliminary center depends only on the marked ideal and the chosen boundary divisor. -/
theorem containedComponentsIdeal_congr (T : MarkedIdealWithBoundary.{u}) (I J : T.scheme.IdealSheafData)
    (E F : List T.scheme.IdealSheafData) (j k : ℕ) (hj : j < E.length) (hk : k < F.length)
    (hI : I = J) (hD : E.get ⟨j, hj⟩ = F.get ⟨k, hk⟩) :
    containedComponentsIdeal (T.withSchemeIdealBoundary T.scheme T.structMap I E) j hj =
      containedComponentsIdeal (T.withSchemeIdealBoundary T.scheme T.structMap J F) k hk := by
  let center (K D : T.scheme.IdealSheafData) := containedComponentsIdeal
    (T.withSchemeIdealBoundary T.scheme T.structMap K [D]) 0 (Nat.zero_lt_succ 0)
  change center I (E.get ⟨j, hj⟩) = center J (F.get ⟨k, hk⟩)
  rw [hI, hD]

theorem isPullback_subschemeMapOfComap (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h :=
  (isPullback_of_isClosedImmersion D'.subschemeι D.subschemeι (subschemeMapOfComap h D D' hD) h
    (subschemeMapOfComap_comp h D D' hD).symm
    (by simp [Scheme.IdealSheafData.ker_subschemeι, hD])).flip

theorem isAdmissible_of_withBoundary_isAdmissible (S : MarkedIdealWithBoundary.{u})
    (E : List S.scheme.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary E)
    (hV : (S.withBoundary E).IsAdmissible) : S.IsAdmissible := by
  have hv : (S.withBoundary S.boundary).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary (S.withBoundary E) S.boundary hV hBE.symm
  rwa [MarkedIdealWithBoundary.withBoundary_self] at hv

private theorem lowerBoundary_erase (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    ((lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1) =
      (T.boundary.eraseIdx j).map (Blowup.strictTransform (𝟙 _) (containedComponentsIdeal T j hj)) := by
  simp only [lowerBoundaryAfterBlowup, Scheme.IdealSheafData.comap_id, List.map_id_fun', id_eq]
  rw [List.eraseIdx_append_of_lt_length (by simpa using hj), List.eraseIdx_map]
  have hlen := List.length_eraseIdx_of_lt hj
  rw [← hlen, ← List.length_map (f := Blowup.strictTransform (𝟙 _) (containedComponentsIdeal T j hj))
    (as := T.boundary.eraseIdx j), List.take_left]

private theorem lowerBoundary_erase_untwisted (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    ((lowerBoundaryWithoutBlowup T).eraseIdx j).take (T.boundary.length - 1) = T.boundary.eraseIdx j := by
  rw [lowerBoundaryWithoutBlowup_eq, ← List.length_eraseIdx_of_lt hj, List.take_length]

private theorem residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A F : X.IdealSheafData) (F' : Y.IdealSheafData) (m : ℕ) (hF' : F' = F.comap g)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor F') (hex : ∃ B : X.IdealSheafData, F ^ m * B = A) :
    residualByPow (A.comap g) F' m = (residualByPow A F m).comap g := by
  have hdown : F ^ m * residualByPow A F m = A := pow_mul_residualByPow A F m hex
  have hup : F' ^ m * (residualByPow A F m).comap g = A.comap g := by
    rw [hF', ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hdown]
  have hup2 : F' ^ m * residualByPow (A.comap g) F' m = A.comap g :=
    pow_mul_residualByPow (A.comap g) F' m ⟨_, hup⟩
  exact (hcart.pow m).eq_of_mul_eq_mul (hup2.trans hup.symm)

theorem lowerIdeal_comap (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T.base))
    (h : Y ⟶ T.scheme) (E : List Y.IdealSheafData) (k : ℕ) (hk : k < E.length)
    (hV : ((T.pullbackAlong Y q h).withBoundary E).IsAdmissible)
    (hZ : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E) k hk =
      (containedComponentsIdeal T j hj).comap h) :
    lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E) k hk =
      (lowerIdealAfterBlowup T j hj).comap h := by
  let S := (T.pullbackAlong Y q h).withBoundary E
  have hcart := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal
    (isBlowupAlongIdealSheaf_id_containedComponentsIdeal S hV k hk)
  rw [exceptionalIdeal_id] at hcart
  obtain ⟨B, hB⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hT j hj
  simp only [lowerIdealAfterBlowup, exceptionalIdeal_id, Scheme.IdealSheafData.comap_id]
  exact residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor h T.ideal _ _ T.mult hZ hcart ⟨B, hB⟩

theorem lowerIdeal_eq_of_top (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (hZ : containedComponentsIdeal T j hj = ⊤) :
    lowerIdealAfterBlowup T j hj = lowerIdealWithoutBlowup T := by
  simp only [lowerIdealAfterBlowup, lowerIdealWithoutBlowup, exceptionalIdeal_id, Scheme.IdealSheafData.comap_id, hZ]
  simpa only [← Scheme.IdealSheafData.one_eq_top, one_pow, one_mul] using
    (pow_mul_residualByPow T.ideal ⊤ T.mult ⟨T.ideal, by rw [← Scheme.IdealSheafData.one_eq_top, one_pow, one_mul]⟩)

theorem lowerBoundary_erase_of_top (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (hZ : containedComponentsIdeal T j hj = ⊤) :
    ((lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1) =
      ((lowerBoundaryWithoutBlowup T).eraseIdx j).take (T.boundary.length - 1) := by
  rw [lowerBoundary_erase T j hj, lowerBoundary_erase_untwisted T j hj]
  have := hT.isNoetherian
  have hst (D : T.scheme.IdealSheafData) :
      Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj) D = D := by
    simpa using strictTransform_comap_of_comap_center_eq_top (𝟙 T.scheme) (containedComponentsIdeal T j hj)
      D (𝟙 T.scheme) (by simp [hZ])
  simpa only [List.map_id] using List.map_congr_left (g := id) (fun D _ => hst D)

theorem lowerBoundary_comap (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T.base))
    (h : Y ⟶ T.scheme) [Flat h] (E : List Y.IdealSheafData) (k : ℕ) (hk : k < E.length)
    (hV : ((T.pullbackAlong Y q h).withBoundary E).IsAdmissible)
    (hZ : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E) k hk =
      (containedComponentsIdeal T j hj).comap h)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (E.eraseIdx k) ((T.boundary.eraseIdx j).map fun D => D.comap h)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E) k hk).eraseIdx k).take (E.length - 1))
      ((((lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1)).map fun D => D.comap h) := by
  let Z := containedComponentsIdeal T j hj
  have hNY : IsNoetherian Y := hV.isNoetherian
  have hNX := hT.isNoetherian
  have comm (D : T.scheme.IdealSheafData) :
      (Blowup.strictTransform (𝟙 _) Z D).comap h = Blowup.strictTransform (𝟙 _) (Z.comap h) (D.comap h) :=
    comap_strictTransform_of_flat_of_isLocallyNoetherian (𝟙 _) h (𝟙 _) h (IsPullback.id_vert h) Z D
      (isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hT j hj)
  rw [lowerBoundary_erase T j hj]
  change MarkedIdealWithBoundary.SameNontrivialBoundary
    (((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E) k hk).eraseIdx k).take
      (((T.pullbackAlong Y q h).withBoundary E).boundary.length - 1)) _
  rw [lowerBoundary_erase _ k hk, hZ]
  change MarkedIdealWithBoundary.SameNontrivialBoundary
    ((E.eraseIdx k).map (Blowup.strictTransform (𝟙 Y) (Z.comap h)))
    (((T.boundary.eraseIdx j).map (Blowup.strictTransform (𝟙 _) Z)).map fun D => D.comap h)
  simpa only [List.map_map, Function.comp_def, ← comm] using
    hE.map (Blowup.strictTransform (𝟙 Y) (Z.comap h)) (strictTransform_top ..)

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
