import Mathlib
/-- A *Coxeter matrix* is a symmetric matrix of natural numbers whose diagonal entries are equal to
1 and whose off-diagonal entries are not equal to 1. -/
@[ext]
structure ArtinTitsMatrix (α : Type*) where
  M : Matrix α α ℕ
  isSymm : M.IsSymm := by decide
  diagonal i : M i i = 0 := by decide
  off_diagonal i i' : i ≠ i' → M i i' ≠ 1 := by decide

namespace ArtinTitsMatrix

variable {α : Type*}

/-- An Artin-Tits matrix can be coerced to a matrix. -/
instance : CoeFun (ArtinTitsMatrix α) fun _ ↦ (Matrix α α ℕ) := ⟨M⟩

variable {β : Type*} (e : α ≃ β) (M : ArtinTitsMatrix α)

attribute [simp] diagonal

theorem symmetric (i i' : α) : M i i' = M i' i := M.isSymm.apply i' i

/-- The Coxeter matrix formed by reindexing via the bijection `e : B ≃ B'`. -/
protected def reindex : ArtinTitsMatrix β where
  M := Matrix.reindex e e M
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal (e.symm i)
  off_diagonal i i' h := M.off_diagonal (e.symm i) (e.symm i') (e.symm.injective.ne h)

theorem reindex_apply (i i' : β) : M.reindex e i i' = M (e.symm i) (e.symm i') := rfl

variable (n : ℕ)

/-- The Artin-Tits matrix for Artin's braid group on n strands -/
def BraidMatrixFin : ArtinTitsMatrix (Fin n) where
  M := Matrix.of fun i j : Fin n ↦
    if i = j then 0
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

/-- The Artin-Tits matrix for Artin's infinite braid group -/
def BraidMatrixInf : ArtinTitsMatrix ℕ where
  M := Matrix.of fun i j : ℕ ↦
    if i = j then 0
      else (if i.dist j = 1 then 3 else 2)
  isSymm := by
    unfold Matrix.IsSymm Matrix.transpose
    simp only [Matrix.of_apply, EmbeddingLike.apply_eq_iff_eq]
    ext
    rw [Nat.dist_comm]
    aesop
  diagonal := by simp
  off_diagonal := by aesop

section
variable {B B' : Type*} (M : ArtinTitsMatrix B) (e : B ≃ B')

/-- The Artin-Tits relation associated to an Artin-Tits matrix $M$ and two indices $i, i' \in B$,
considered as an element of the free group on $\{s_i\}_{i \in B}$.
If $M_{i, i'} = 0$, then this is the identity, indicating that there is no relation between
$s_i$ and $s_{i'}$. -/
def relation (i i' : B) : FreeGroup B := (FreeGroup.of i * FreeGroup.of i') ^ M i i'

/-- The set of all Artin-Tits relations associated to the Artin-Tits matrix $M$. -/
def relationsSet : Set (FreeGroup B) := .range <| Function.uncurry M.relation

/-- The Artin-Tits group associated to am Artin-Tits matrix $M$ -/
protected def Group : Type _ := PresentedGroup M.relationsSet

instance : Group M.Group := QuotientGroup.Quotient.group _

/-- The simple crossing of the Artin-Tits group `M.Group` at the index `i`. -/
def simple (i : B) : M.Group := PresentedGroup.of i

theorem reindex_relationsSet :
    (M.reindex e).relationsSet =
    FreeGroup.freeGroupCongr e '' M.relationsSet := let M' := M.reindex e; calc
  Set.range (Function.uncurry M'.relation)
  _ = Set.range (Function.uncurry M'.relation ∘ Prod.map e e) := by simp [Set.range_comp]
  _ = Set.range (FreeGroup.freeGroupCongr e ∘ Function.uncurry M.relation) := by
      apply congrArg Set.range
      ext ⟨i, i'⟩
      simp [relation, reindex_apply, M']
  _ = _ := by simp [Set.range_comp, relationsSet]

/-- The isomorphism between the Artin-Tits group associated to the reindexed matrix `M.reindex e` and
the Artin-Tits group associated to `M`. -/
def reindexGroupEquiv : (M.reindex e).Group ≃* M.Group :=
  .symm <| QuotientGroup.congr
    (Subgroup.normalClosure M.relationsSet)
    (Subgroup.normalClosure (M.reindex e).relationsSet)
    (FreeGroup.freeGroupCongr e)
    (by
      rw [reindex_relationsSet,
        Subgroup.map_normalClosure _ _ (by simpa using (FreeGroup.freeGroupCongr e).surjective),
        MonoidHom.coe_coe])

theorem reindexGroupEquiv_apply_simple (i : B') :
    (M.reindexGroupEquiv e) ((M.reindex e).simple i) = M.simple (e.symm i) := rfl

theorem reindexGroupEquiv_symm_apply_simple (i : B) :
    (M.reindexGroupEquiv e).symm (M.simple i) = (M.reindex e).simple (e i) := rfl
end
end ArtinTitsMatrix

section

variable {B : Type*} (M : ArtinTitsMatrix B)

/-- An Artin-Tits system `CoxeterSystem M W` is a structure recording the isomorphism between
a group `W` and the Coxeter group associated to an Artin-Tits matrix `M`. -/
@[ext]
structure ArtinTitsSystem (W : Type*) [Group W] where
  /-- The isomorphism between `W` and the Artin-Tits group associated to `M`. -/
  mulEquiv : W ≃* M.Group

/-- A group is an Artin-Tits group if it admits an Artin-Tits system for some Artin-Tits matrix `M`. -/
class IsArtinTitsGroup.{u} (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ B : Type u, ∃ M : ArtinTitsMatrix B, Nonempty (ArtinTitsSystem M W)

/-- The canonical Artin-Tits system on the Artin-Tits group associated to `M`. -/
def ArtinTitsMatrix.toArtinTitsSystem : ArtinTitsSystem M M.Group := ⟨.refl _⟩

end
namespace ArtinTitsSystem

open ArtinTitsMatrix

variable {B B' : Type*} (e : B ≃ B')
variable {W H : Type*} [Group W] [Group H]
variable {M : ArtinTitsMatrix B} (cs : ArtinTitsSystem M W)

/-- Reindex a Artin-Tits system through a bijection of the indexing sets. -/
@[simps]
protected def reindex (e : B ≃ B') : ArtinTitsSystem (M.reindex e) W :=
  ⟨cs.mulEquiv.trans (M.reindexGroupEquiv e).symm⟩

/-- Push a Artin-Tits system through a group isomorphism. -/
@[simps]
protected def map (e : W ≃* H) : ArtinTitsSystem M H := ⟨e.symm.trans cs.mulEquiv⟩

/-! ### Simple reflections -/

/-- The simple crossing of `W` at the index `i`. -/
def simple (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)

@[simp]
theorem _root_.ArtinTitsMatrix.toArtinTitsSystem_simple (M : ArtinTitsMatrix B) :
    M.toArtinTitsSystem.simple = M.simple := rfl

@[simp] theorem reindex_simple (i' : B') : (cs.reindex e).simple i' = cs.simple (e.symm i') := rfl

@[simp] theorem map_simple (e : W ≃* H) (i : B) : (cs.map e).simple i = e (cs.simple i) := rfl

local prefix:100 "s" => cs.simple


/-- The simple crossings of `W` generate `W` as a group. -/
theorem subgroup_closure_range_simple : Subgroup.closure (.range cs.simple) = ⊤ := by
  have : cs.simple = cs.mulEquiv.symm ∘ PresentedGroup.of := rfl
  rw [this, Set.range_comp, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure,
    PresentedGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (MulEquiv.surjective _)


/-- The simple crossings of `W` generate `W` as a monoid. -/
theorem submonoid_closure_range_simple : Submonoid.closure (.range cs.simple) = ⊤ := by
  have : cs.simple = cs.mulEquiv.symm ∘ PresentedGroup.of := rfl
  have H : Function.Surjective ⇑cs.mulEquiv.symm.toMonoidHom := by
    apply MulEquiv.surjective
  rw [this, Set.range_comp, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_mclosure]
  apply MonoidHom.mrange_eq_top.mpr at H
  rw [MonoidHom.mrange_eq_map] at H
  rw [← H]
  congr
  rw [Submonoid.closure_eq_mrange]
  refine MonoidHom.mrange_eq_top.mpr ?_
  intro y
  rcases Quot.exists_rep y with ⟨w, hw⟩
  rcases Quot.exists_rep w with ⟨t, ht⟩
  rw [← hw, ← ht]
  use FreeMonoid.of ⟨PresentedGroup.of t, sorry⟩




  --refine (Submonoid.eq_top_iff' (Submonoid.closure (Set.range cs.simple))).mpr ?_
  sorry
  --rw [← Subgroup.closure_toSubmonoid, subgroup_closure_range_simple, Subgroup.top_toSubmonoid]

/-! ### Induction principles for Coxeter systems -/

/-- If `p : W → Prop` holds for all simple reflections, it holds for the identity, and it is
preserved under multiplication, then it holds for all elements of `W`. -/
theorem simple_induction {p : W → Prop} (w : W) (simple : ∀ i : B, p (s i)) (one : p 1)
    (mul : ∀ w w' : W, p w → p w' → p (w * w')) : p w := by
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  exact Submonoid.closure_induction (fun x ⟨i, hi⟩ ↦ hi ▸ simple i) one (fun _ _ _ _ ↦ mul _ _)
    this

/-- If `p : W → Prop` holds for the identity and it is preserved under multiplying on the left
by a simple reflection, then it holds for all elements of `W`. -/
theorem simple_induction_left {p : W → Prop} (w : W) (one : p 1)
    (mul_simple_left : ∀ (w : W) (i : B), p w → p (s i * w)) : p w := by
  let p' : (w : W) → w ∈ Submonoid.closure (Set.range cs.simple) → Prop :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  induction this using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left i mi y my ih =>
    rw [Set.mem_range] at mi
    exact mi.choose_spec ▸ mul_simple_left _ _ ih

/-- If `p : W → Prop` holds for the identity and it is preserved under multiplying on the right
by a simple reflection, then it holds for all elements of `W`. -/
theorem simple_induction_right {p : W → Prop} (w : W) (one : p 1)
    (mul_simple_right : ∀ (w : W) (i : B), p w → p (w * s i)) : p w := by
  let p' : ((w : W) → w ∈ Submonoid.closure (Set.range cs.simple) → Prop) :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  induction this using Submonoid.closure_induction_right with
  | one => exact one
  | mul_right y my i mi ih =>
    rw [Set.mem_range] at mi
    exact mi.choose_spec ▸ mul_simple_right _ _ ih

/-! ### Homomorphisms from a Coxeter group -/

/-- If two homomorphisms with domain `W` agree on all simple reflections, then they are equal. -/
theorem ext_simple {G : Type*} [MulOneClass G] {φ₁ φ₂ : W →* G} (h : ∀ i : B, φ₁ (s i) = φ₂ (s i)) :
    φ₁ = φ₂ :=
  MonoidHom.eq_of_eqOn_denseM cs.submonoid_closure_range_simple (fun _ ⟨i, hi⟩ ↦ hi ▸ h i)

/-- The proposition that the values of the function `f : B → G` satisfy the Coxeter relations
corresponding to the matrix `M`. -/
def _root_.ArtinTitsMatrix.IsLiftable {G : Type*} [Monoid G] (M : ArtinTitsMatrix B) (f : B → G) :
    Prop := ∀ i i', (f i * f i') ^ M i i' = 1

private theorem relations_liftable {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f)
    (r : FreeGroup B) (hr : r ∈ M.relationsSet) : (FreeGroup.lift f) r = 1 := by
  rcases hr with ⟨⟨i, i'⟩, rfl⟩
  rw [uncurry, relation, map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  exact hf i i'

set_option backward.privateInPublic true in
private def groupLift {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  (PresentedGroup.toGroup (relations_liftable hf)).comp cs.mulEquiv.toMonoidHom

set_option backward.privateInPublic true in
private def restrictUnit {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    Gˣ where
  val := f i
  inv := f i
  val_inv := pow_one (f i * f i) ▸ M.diagonal i ▸ hf i i
  inv_val := pow_one (f i * f i) ▸ M.diagonal i ▸ hf i i

private theorem toMonoidHom_apply_symm_apply (a : PresentedGroup (M.relationsSet)) :
    (MulEquiv.toMonoidHom cs.mulEquiv : W →* PresentedGroup (M.relationsSet))
    ((MulEquiv.symm cs.mulEquiv) a) = a := calc
  _ = cs.mulEquiv ((MulEquiv.symm cs.mulEquiv) a) := by rfl
  _ = _ := by rw [MulEquiv.apply_symm_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The universal mapping property of Coxeter systems. For any monoid `G`,
functions `f : B → G` whose values satisfy the Coxeter relations are equivalent to
monoid homomorphisms `f' : W → G`. -/
def lift {G : Type*} [Monoid G] : {f : B → G // IsLiftable M f} ≃ (W →* G) where
  toFun f := MonoidHom.comp (Units.coeHom G) (cs.groupLift
    (show ∀ i i', ((restrictUnit f.property) i * (restrictUnit f.property) i') ^ M i i' = 1 from
      fun i i' ↦ Units.ext (f.property i i')))
  invFun ι := ⟨ι ∘ cs.simple, fun i i' ↦ by
    rw [comp_apply, comp_apply, ← map_mul, ← map_pow, simple_mul_simple_pow, map_one]⟩
  left_inv f := by
    ext i
    simp only [MonoidHom.comp_apply, comp_apply, groupLift, simple]
    rw [← MonoidHom.toFun_eq_coe, toMonoidHom_apply_symm_apply, PresentedGroup.toGroup.of,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Units.coeHom_apply, restrictUnit]
  right_inv ι := by
    apply cs.ext_simple
    intro i
    dsimp only
    rw [groupLift, simple, MonoidHom.comp_apply, MonoidHom.comp_apply, toMonoidHom_apply_symm_apply,
      PresentedGroup.toGroup.of, CoxeterSystem.restrictUnit, Units.coeHom_apply]
    simp only [comp_apply, simple]

@[simp]
theorem lift_apply_simple {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    cs.lift ⟨f, hf⟩ (s i) = f i := congrFun (congrArg Subtype.val (cs.lift.left_inv ⟨f, hf⟩)) i

/-- If two Coxeter systems on the same group `W` have the same Coxeter matrix `M : Matrix B B ℕ`
and the same simple reflection map `B → W`, then they are identical. -/
theorem simple_determines_coxeterSystem :
    Injective (simple : CoxeterSystem M W → B → W) := by
  intro cs1 cs2 h
  apply CoxeterSystem.ext
  apply MulEquiv.toMonoidHom_injective
  apply cs1.ext_simple
  nth_rw 2 [h]
  simp [simple]

/-! ### Words -/

/-- The product of the simple reflections of `W` corresponding to the indices in `ω`. -/
def wordProd (ω : List B) : W := prod (map cs.simple ω)

local prefix:100 "π " => cs.wordProd

@[simp] theorem wordProd_nil : π [] = 1 := by simp [wordProd]

theorem wordProd_cons (i : B) (ω : List B) : π (i :: ω) = s i * π ω := by simp [wordProd]

@[simp] theorem wordProd_singleton (i : B) : π ([i]) = s i := by simp [wordProd]

theorem wordProd_concat (i : B) (ω : List B) : π (ω.concat i) = π ω * s i := by simp [wordProd]

theorem wordProd_append (ω ω' : List B) : π (ω ++ ω') = π ω * π ω' := by simp [wordProd]

@[simp] theorem wordProd_reverse (ω : List B) : π (reverse ω) = (π ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons x ω' ih => simpa [wordProd_cons, wordProd_append] using ih

theorem wordProd_surjective : Surjective cs.wordProd := by
  intro w
  apply cs.simple_induction_left w
  · use []
    rw [wordProd_nil]
  · rintro _ i ⟨ω, rfl⟩
    use i :: ω
    rw [wordProd_cons]

/-- The word of length `m` that alternates between `i` and `i'`, ending with `i'`. -/
def alternatingWord (i i' : B) (m : ℕ) : List B :=
  match m with
  | 0 => []
  | m + 1 => (alternatingWord i' i m).concat i'

/-- The word of length `M i i'` that alternates between `i` and `i'`, ending with `i'`. -/
abbrev braidWord (M : ArtinTitsMatrix B) (i i' : B) : List B := alternatingWord i i' (M i i')

theorem alternatingWord_succ (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (alternatingWord i' i m).concat i' := rfl

theorem alternatingWord_succ' (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (if Even m then i' else i) :: alternatingWord i i' m := by
  induction m generalizing i i' with
  | zero => simp [alternatingWord]
  | succ m ih =>
    rw [alternatingWord]
    nth_rw 1 [ih i' i]
    rw [alternatingWord]
    simp [Nat.even_add_one, -Nat.not_even_iff_odd]

@[simp]
theorem length_alternatingWord (i i' : B) (m : ℕ) :
    List.length (alternatingWord i i' m) = m := by
  induction m generalizing i i' with
  | zero => dsimp [alternatingWord]
  | succ m ih => simpa [alternatingWord] using ih i' i

lemma getElem_alternatingWord (i j : B) (p k : ℕ) (hk : k < p) :
    (alternatingWord i j p)[k]'(by simp [hk]) = (if Even (p + k) then i else j) := by
  revert k
  induction p with
  | zero => grind [not_lt_zero']
  | succ n h => grind [CoxeterSystem.alternatingWord_succ']

lemma getElem_alternatingWord_swapIndices (i j : B) (p k : ℕ) (h : k + 1 < p) :
     (alternatingWord i j p)[k + 1]'(by simp [h]) =
     (alternatingWord j i p)[k]'(by simp; lia) := by
  rw [getElem_alternatingWord i j p (k + 1) (by lia),
    getElem_alternatingWord j i p k (by lia)]
  by_cases h_even : Even (p + k)
  · rw [if_pos h_even, ← add_assoc]
    simp only [ite_eq_right_iff, isEmpty_Prop, Nat.not_even_iff_odd, Even.add_one h_even,
      IsEmpty.forall_iff]
  · rw [if_neg h_even, ← add_assoc]
    simp [Odd.add_one (Nat.not_even_iff_odd.mp h_even)]

lemma listTake_alternatingWord (i j : B) (p k : ℕ) (h : k < 2 * p) :
    List.take k (alternatingWord i j (2 * p)) =
    if Even k then alternatingWord i j k else alternatingWord j i k := by
  induction k with
    | zero =>
      simp only [take_zero, Even.zero, ↓reduceIte, alternatingWord]
    | succ k h' =>
      have hk : k < 2 * p := by lia
      apply h' at hk
      by_cases h_even : Even k
      · simp only [h_even, ↓reduceIte] at hk
        simp only [Nat.not_even_iff_odd.mpr (Even.add_one h_even), ↓reduceIte]
        rw [← List.take_concat_get (by simp; lia), alternatingWord_succ, ← hk]
        apply congr_arg
        rw [getElem_alternatingWord i j (2 * p) k (by lia)]
        simp [(by apply Nat.even_add.mpr; simp [h_even] : Even (2 * p + k))]
      · simp only [h_even, ↓reduceIte] at hk
        simp only [Odd.add_one (by simpa using h_even), ↓reduceIte]
        rw [← List.take_concat_get (by simp; lia), alternatingWord_succ, hk]
        apply congr_arg
        rw [getElem_alternatingWord i j (2 * p) k (by lia)]
        simp [(by apply Nat.odd_add.mpr; simp [h_even] : Odd (2 * p + k))]

lemma listTake_succ_alternatingWord (i j : B) (p : ℕ) (k : ℕ) (h : k + 1 < 2 * p) :
    List.take (k + 1) (alternatingWord i j (2 * p)) =
    i :: (List.take k (alternatingWord j i (2 * p))) := by
  rw [listTake_alternatingWord j i p k (by lia), listTake_alternatingWord i j p (k + 1) h]
  by_cases h_even : Even k
  · simp [Nat.not_even_iff_odd.mpr (Even.add_one h_even), alternatingWord_succ', h_even]
  · simp [(by rw [Nat.not_even_iff_odd] at h_even; exact Odd.add_one h_even : Even (k + 1)),
      alternatingWord_succ', h_even]

theorem prod_alternatingWord_eq_mul_pow (i i' : B) (m : ℕ) :
    π (alternatingWord i i' m) = (if Even m then 1 else s i') * (s i * s i') ^ (m / 2) := by
  induction m with
  | zero => simp [alternatingWord]
  | succ m ih =>
    rw [alternatingWord_succ', wordProd_cons, ih]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
      simp [hm, h₁, h₂]
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
      simp [hm, h₁, h₂, ← pow_succ', ← mul_assoc]

theorem prod_alternatingWord_eq_prod_alternatingWord_sub (i i' : B) (m : ℕ) (hm : m ≤ M i i' * 2) :
    π (alternatingWord i i' m) = π (alternatingWord i' i (M i i' * 2 - m)) := by
  simp_rw [prod_alternatingWord_eq_mul_pow, ← Int.even_coe_nat]
  /- Rewrite everything in terms of an integer m' which is equal to m.
  The resulting equation holds for all integers m'. -/
  simp_rw [← zpow_natCast, Int.natCast_ediv, Int.ofNat_sub hm]
  generalize (m : ℤ) = m'
  clear hm
  push_cast
  rcases Int.even_or_odd' m' with ⟨k, rfl | rfl⟩
  · rw [if_pos (by use k; ring), if_pos (by use -k + (M i i'); ring), mul_comm 2 k, ← sub_mul]
    repeat rw [Int.mul_ediv_cancel _ (by simp)]
    rw [zpow_sub, zpow_natCast, simple_mul_simple_pow' cs i i', ← inv_zpow]
    simp
  · have : ¬Even (2 * k + 1) := Int.not_even_iff_odd.2 ⟨k, rfl⟩
    rw [if_neg this]
    have : ¬Even (↑(M i i') * 2 - (2 * k + 1)) :=
      Int.not_even_iff_odd.2 ⟨↑(M i i') - k - 1, by ring⟩
    rw [if_neg this]
    rw [(by ring : ↑(M i i') * 2 - (2 * k + 1) = -1 + (-k + ↑(M i i')) * 2),
      (by ring : 2 * k + 1 = 1 + k * 2)]
    repeat rw [Int.add_mul_ediv_right _ _ (by simp)]
    norm_num
    rw [zpow_add, zpow_add, zpow_natCast, simple_mul_simple_pow', zpow_neg, ← inv_zpow, zpow_neg,
      ← inv_zpow]
    simp [← mul_assoc]

/-- The two words of length `M i i'` that alternate between `i` and `i'` have the same product.
This is known as the "braid relation" or "Artin-Tits relation". -/
theorem wordProd_braidWord_eq (i i' : B) :
    π (braidWord M i i') = π (braidWord M i' i) := by
  have := cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' (M i i')
    (Nat.le_mul_of_pos_right _ (by simp))
  rw [tsub_eq_of_eq_add (mul_two (M i i'))] at this
  nth_rw 2 [M.symmetric i i'] at this
  exact this

end ArtinTitsSystem
