import BraidProject.CommonMultiplesInf
import BraidProject.BraidMonoidFin
import Mathlib.Data.Fin.Basic
import BraidProject.BraidMonoid

namespace FreeMonoid'

variable {α β : Type*}
def pmap {p : α → Prop} (f : (a : α) → p a → β ) (l : FreeMonoid' (α)):= List.pmap f (toList l)
end FreeMonoid'

theorem fin_castPred_succ {k i : ℕ} {i1_k : i+1<k+2} {i_n : i<k+2} : Fin.mk (i+1) i1_k =
    Fin.succ (Fin.castPred { val := i, isLt := i_n }
    (Fin.exists_castSucc_eq.mp (Exists.intro { val := i, isLt := (Nat.succ_lt_succ_iff.mp i1_k) } rfl))) --(Fin.exists_castSucc_eq.mp (Exists.intro { val := i, isLt := Fin.succ_lt_succ_iff.mp _ } rfl))) :=
    := by
  rw [Fin.castPred_mk i <| Nat.succ_lt_succ_iff.mp i1_k]
  exact rfl

--do i want to make something explicit later?
theorem fin_succ_minus_one {j k : ℕ} (j_ge_one : j >= 1) {H : j-1 < k} {j_n : j<k+1} :
  Fin.mk (j) j_n = (Fin.mk (j-1) H).succ := by
  apply Fin.eq_of_val_eq
  simp only [ge_iff_le, Fin.succ_mk]
  exact Nat.eq_add_of_sub_eq j_ge_one rfl

theorem braid_rel_def_is_good {i j k : ℕ} {i_n : i < k+2} {j_n : j < k+2} (apart : i+2 <= j) :
  @braid_rels_multi (k) [⟨i, i_n⟩, ⟨j, j_n⟩] [⟨j, j_n⟩, ⟨i, i_n⟩] := by
  have i_lt_k : i < k := Nat.add_lt_add_iff_right.mp (Nat.lt_of_le_of_lt apart j_n)
  have i_is : Fin.mk i i_n = (Fin.mk i i_lt_k).castSucc.castSucc := rfl
  rw [i_is]
  have j_ge_2 : 2<=j := le_of_add_le_right apart
  have j_minus_two : j-2 < k := Nat.sub_lt_right_of_lt_add j_ge_2 j_n
  have j_is : Fin.mk j j_n = (Fin.mk (j-2) j_minus_two).succ.succ := by
    have another_isLt : j-1<k+1 := lt_add_of_tsub_lt_right j_minus_two
    rw [fin_succ_minus_one (Nat.one_le_of_lt apart)]
    simp only [ge_iff_le, Fin.succ_mk, Fin.mk.injEq, add_left_inj]
    have H : ∃ x, j=2+x := Exists.intro (j - 2) (Nat.add_sub_of_le j_ge_2).symm
    rcases H with ⟨k', hk⟩
    simp only [hk, Nat.succ_add_sub_one, Fin.succ_mk, add_tsub_cancel_left, Fin.mk.injEq,
        add_left_inj]
    · exact Nat.add_comm _ _
    linarith [j_minus_two]
  rw [j_is]
  exact braid_rels_multi.separated _ _ (Eq.mpr (congrArg (fun _a => _a) (propext Fin.le_iff_val_le_val))
        (Nat.le_sub_of_add_le apart))

def make_fin' (n : ℕ) (a : FreeMonoid' ℕ) (bound : ∀ x ∈ a, x<n.pred) : FreeMonoid' (Fin n.pred) :=
  (FreeMonoid'.pmap (λ i => Fin.mk i ) a) bound

theorem common_right_mul_souped_two {a : ℕ} (u v : FreeMonoid' (Fin a.pred)) (n : ℕ)
  (bound : ∀ x : ℕ, (x∈ FreeMonoid'.map (λ i : Fin a.pred => i.val) (u) ∨ x ∈ (FreeMonoid'.map (λ i : Fin a.pred => i.val) v)) →  x<n) :
    ∃ (u' v' : FreeMonoid' ℕ ), (BraidMonoidInf.mk ((FreeMonoid'.map (λ i : Fin a.pred => i.val) u) * v') = BraidMonoidInf.mk ((FreeMonoid'.map (λ i : Fin a.pred => i.val) v) * u')) ∧
    (∀ x, (x∈ u' ∨ x ∈ v') →  x<n) := by
  let new_u := (FreeMonoid'.map (λ i : Fin a.pred => i.val) u)
  let new_v := (FreeMonoid'.map (λ i : Fin a.pred => i.val) v)
  have u_under := fun x h => bound x (Or.inl h)
  have v_under := fun x h => bound x (Or.inr h)
  have u_length := Nat.le_max_left (FreeMonoid'.length new_u) (FreeMonoid'.length new_v)
  have v_length := Nat.le_max_right (FreeMonoid'.length new_u) (FreeMonoid'.length new_v)
  rcases (multiple_delta_neg new_u (Nat.max (FreeMonoid'.length new_u) (FreeMonoid'.length new_v)) n
    u_length u_under) with ⟨u', hu', u'_bound⟩
  rcases (multiple_delta_neg new_v (Nat.max (FreeMonoid'.length new_u) (FreeMonoid'.length new_v)) n
    v_length v_under) with ⟨v', hv', v'_bound⟩
  use v', u'
  constructor
  · exact hu'.trans hv'.symm
  intro x h
  rcases h
  · next v_prime =>
    exact v'_bound _ v_prime
  next u_prime =>
  exact u'_bound _ u_prime

theorem common_right_mul_souped_three {a : ℕ} (u v : FreeMonoid' (Fin a.pred)) :
    ∃ (u' v' : FreeMonoid' ℕ), (BraidMonoidInf.mk ((FreeMonoid'.map (λ i : Fin a.pred => i.val) u) * v')
    = BraidMonoidInf.mk ((FreeMonoid'.map (λ i : Fin a.pred => i.val) v) * u')) ∧
    (∀ x, (x∈ u' ∨ x ∈ v') →  x<a.pred) := by
  have bounded_helper : ∀ x : ℕ, (x∈ FreeMonoid'.map (λ i : Fin a.pred => i.val) (u) ∨ x ∈ (FreeMonoid'.map (λ i : Fin a.pred => i.val) v)) →  x<a.pred := by
    intro x h
    rcases h
    · next in_u =>
      rcases FreeMonoid'.mem_map.mp in_u with ⟨a', _, bound_a⟩
      rw [← bound_a]
      exact a'.isLt
    next in_v =>
    rcases FreeMonoid'.mem_map.mp in_v with ⟨b', _, bound_b⟩
    rw [← bound_b]
    exact b'.isLt
  exact common_right_mul_souped_two u v a.pred bounded_helper

theorem rid_empty (H : x ∈ FreeMonoid'.of head * (tail  *  1)) : x∈ FreeMonoid'.of head * tail := by
  rw [mul_one] at H
  assumption

theorem bounded_empty : ∀ (x : ℕ), x ∈ (1 : FreeMonoid' ℕ) → x < n :=
  fun _ h => (FreeMonoid'.mem_one_iff.mp h).elim

theorem mk_fin_empty : make_fin' n 1 bounded_empty = 1 := rfl

#check Nat.beq
theorem end_of_FreeMonoid' (length : FreeMonoid'.length b = Nat.succ n) : ∃ b_front b_last, b = b_front  *  FreeMonoid'.of b_last := by
  rcases FreeMonoid'.eq_one_or_has_last_elem b
  · rename_i b_is_one
    rw [b_is_one] at length
    exfalso
    rw [FreeMonoid'.length_one] at length
    exact Nat.succ_ne_zero n length.symm
  assumption

theorem mk_fin_singleton (a : ℕ) (b : FreeMonoid' ℕ) (bounded_a : ∀ x, x ∈ FreeMonoid'.of a → x < n.pred) (bounded_b : ∀ x, x ∈ b → x < n.pred)
  (bounded_ab : ∀ x ∈ FreeMonoid'.of a * b, x < n.pred)
  : make_fin' n (FreeMonoid'.of a * b) bounded_ab = make_fin' n (FreeMonoid'.of a) bounded_a  *  make_fin' n b bounded_b := by
  have H : ∀ t, (FreeMonoid'.length b)=t → make_fin' n (FreeMonoid'.of a * b) bounded_ab = make_fin' n ([a]) bounded_a  *  make_fin' n b bounded_b := by
    intro t
    induction t
    · intro h
      simp only [FreeMonoid'.eq_one_of_length_eq_zero h, mul_one]
      apply congr_arg
      simp only [FreeMonoid'.mem_of, forall_eq]
      exact bounded_a
    intro m
    rename_i h _
    rcases (end_of_FreeMonoid' m) with ⟨b_front, b_last, b_prf⟩
    rw [b_prf] at bounded_ab
    rw [b_prf] at bounded_b
    have replace_b : make_fin' n (FreeMonoid'.of a * (b_front * FreeMonoid'.of b_last)) bounded_ab =
        make_fin' n (FreeMonoid'.of a) bounded_a  *  make_fin' n (b_front  * FreeMonoid'.of b_last) bounded_b := by
      unfold make_fin'
      rfl
    rw [← b_prf] at bounded_ab
    rw [← b_prf] at bounded_b
    simp only [← b_prf] at replace_b
    exact replace_b
  exact H (FreeMonoid'.length b) (Eq.refl (FreeMonoid'.length b))

theorem make_fin_helper (a b : FreeMonoid' ℕ) (bounded_a : ∀ x∈ a, x < n.pred) (bounded_b : ∀ x∈ b, x < n.pred) (bounded_ab : ∀ x∈ a * b, x < n.pred) :
    make_fin' n (a * b) bounded_ab = make_fin' n a bounded_a  *  make_fin' n b bounded_b := by
  have H : ∀ a, ∀ (bounded_a : ∀ x∈ a, x < n.pred) (bounded_ab : ∀ x ∈ a * b, x < n.pred),
        make_fin' n (a * b) bounded_ab = make_fin' n a bounded_a  *  make_fin' n b bounded_b := by
    intro a
    induction a using FreeMonoid'.inductionOn'
    · intro bounded_a bounded_ab
      rw [mk_fin_empty]
      simp only [one_mul]
    rename_i ha ta ihta
    intro bounded_a bounded_ab
    have bounded_ha : ∀ x, x ∈ FreeMonoid'.of ha → x < n.pred :=
      fun t h => bounded_a t (FreeMonoid'.mem_mul.mpr (Or.inl h))
    have bounded_ta : ∀ x, x∈ ta → x <n.pred :=
      fun t h => bounded_a t (FreeMonoid'.mem_mul.mpr (Or.inr h))
    have bounded_tab : ∀ x, x∈ ta * b → x < n.pred := by
      exact fun t h => bounded_ab t
        (Eq.mpr (id (congrArg (fun _a => t ∈ _a) (mul_assoc (FreeMonoid'.of ha) ta b)))
        (Eq.mpr (id (congrArg (fun _a => _a) (propext FreeMonoid'.mem_mul))) (Or.inr h)))
    rw [mk_fin_singleton ha ta bounded_ha bounded_ta]
    specialize ihta bounded_ta bounded_tab
    conv => rhs; rw [mul_assoc]
    rw [← ihta]
    exact rfl
  exact H _ _ _

--move into Nat
namespace Nat

theorem zero_or_one_of_pred_eq_zero : ∀ n, n.pred = 0 → n=0 ∨ n=1 := by
  intro n
  rcases n
  · exact fun _ => Or.inl (Eq.refl zero)
  rename_i m
  rcases m
  · exact fun _ => Or.inr (Eq.refl (succ zero))
  rename_i p
  intro h
  simp only [Nat.pred_succ, add_eq_zero, one_ne_zero, and_false] at h

end Nat

theorem braid_rel_inf_to_fin_helper (n: ℕ) (a b: FreeMonoid' ℕ) (holds_in_inf : braid_rels_m_inf a b)
    (bounded_a: ∀ (x : ℕ), x ∈ a → x < n.pred) (bounded_b: ∀ (x : ℕ), x ∈ b → x < n.pred) :
    braid_rels_m n.pred (make_fin' n a bounded_a) (make_fin' n b bounded_b) := by
  induction holds_in_inf
  · rename_i i
    have H_ub : ∃k, n = Nat.succ (Nat.succ (Nat.succ k)) := by  -- because it's bigger than n+1
      have H_n_1 : i+1 < n.pred :=
        bounded_b (i + 1) (FreeMonoid'.mem_mul.mpr (Or.inr FreeMonoid'.mem_of_self))
      have double : Nat.succ (Nat.succ i) <= n.pred := H_n_1
      use (Nat.pred (Nat.pred (Nat.pred n)))
      rw [Nat.succ_pred, Nat.succ_pred, Nat.succ_pred]
      · intro n_zero
        rw [n_zero] at H_n_1
        simp at H_n_1
      · intro pred_zero
        rw [pred_zero] at H_n_1
        simp only [not_lt_zero'] at H_n_1
      intro h
      rcases Nat.zero_or_one_of_pred_eq_zero _ h
      · next is_zero =>
        rw [is_zero] at double
        simp only [Nat.pred_zero, nonpos_iff_eq_zero, Nat.succ_ne_zero] at double
      next is_one =>
      rw [is_one] at double
      linarith [double]
    rcases H_ub with ⟨k, hk⟩
    subst hk
    simp only [Nat.pred_succ]
    simp only [Nat.pred_succ] at bounded_a
    simp only [Nat.pred_succ] at bounded_b
    unfold braid_rels_m
    have i_n : i< k + 2 :=
      bounded_a i (FreeMonoid'.mem_mul.mpr (Or.inr (FreeMonoid'.mem_of.mpr (Eq.refl i))))
    have i1_k : i+1 < k + 2 :=
      bounded_a (i + 1) (FreeMonoid'.mem_mul.mpr (Or.inl (FreeMonoid'.mem_mul.mpr
      (Or.inr (FreeMonoid'.mem_of.mpr (Eq.refl (i + 1)))))))
    have mkfin_fwd : (make_fin' (Nat.succ (Nat.succ (Nat.succ k))) (FreeMonoid'.of i * FreeMonoid'.of (i + 1) * FreeMonoid'.of i) bounded_a) =
          (FreeMonoid'.of (Fin.mk i i_n) * FreeMonoid'.of (Fin.mk (i+1) i1_k) * FreeMonoid'.of (Fin.mk i i_n)) := by
      unfold make_fin'
      rfl
    have mkfin_bwd : (make_fin' (Nat.succ (Nat.succ (Nat.succ k))) (FreeMonoid'.of (i+1) * FreeMonoid'.of i * FreeMonoid'.of (i + 1)) bounded_b) =
          (FreeMonoid'.of (Fin.mk (i+1) i1_k) * FreeMonoid'.of (Fin.mk i i_n) * FreeMonoid'.of (Fin.mk (i+1) i1_k)) := by
      unfold make_fin'
      rfl
    rw [mkfin_fwd, mkfin_bwd]
    have h123 : ⟨i, i_n⟩ ≠ Fin.last (k + 1) := by
      have h456 : ⟨i, i_n⟩ < Fin.last (k + 1) := Fin.succ_lt_succ_iff.mp i1_k
      exact Fin.ne_last_of_lt h456
    have hi : Fin.mk i i_n = (Fin.castPred (Fin.mk i i_n) h123).castSucc := by
      rw [Fin.castSucc_castPred]
    rw [hi, fin_castPred_succ]
    exact braid_rels_multi.adjacent (Fin.castPred { val := i, isLt := i_n } _)
  rename_i i j apart
  have H_ub : ∃k, n = Nat.succ (Nat.succ (Nat.succ k)) := by  -- because it's bigger than n+1
    have h_j : j < n.pred :=
      bounded_a j (FreeMonoid'.mem_mul.mpr (Or.inr FreeMonoid'.mem_of_self))
    use (Nat.pred (Nat.pred (Nat.pred n)))
    rw [Nat.succ_pred, Nat.succ_pred, Nat.succ_pred]
    · intro n_is
      rw [n_is] at h_j
      simp only [Nat.pred_zero, not_lt_zero'] at h_j
    · intro pred_is
      rw [pred_is] at h_j
      simp only [not_lt_zero'] at h_j
    intro h
    exfalso
    rcases Nat.zero_or_one_of_pred_eq_zero _ h
    · next is_zero =>
      rw [is_zero] at h_j
      linarith [h_j]
    next is_one =>
    rw [is_one] at h_j
    linarith [h_j, apart]
  rcases H_ub with ⟨k, hk⟩
  subst hk
  unfold braid_rels_m
  have i_n : i< k+2 := bounded_a i (FreeMonoid'.mem_mul.mpr (Or.inl FreeMonoid'.mem_of_self))
  have j_n : j< k+2 :=  bounded_a j (FreeMonoid'.mem_mul.mpr (Or.inr FreeMonoid'.mem_of_self))
  have first : make_fin' (k+3) (FreeMonoid'.of i * FreeMonoid'.of j) bounded_a =
    FreeMonoid'.of (Fin.mk i i_n) * FreeMonoid'.of (Fin.mk j j_n) := rfl
  have second : make_fin' (k+3) (FreeMonoid'.of j * FreeMonoid'.of i) bounded_b =
    [Fin.mk j j_n, Fin.mk i i_n] := rfl
  rw [first, second]
  exact braid_rel_def_is_good apart

theorem braid_rel_inf_to_fin (n : ℕ) (a b : FreeMonoid' ℕ) (bounded_a: ∀ x, (x ∈ a) → x<n.pred)
    (bounded_b: ∀ x, x∈ b→ x<n.pred) (h : BraidMonoidInf.mk a = BraidMonoidInf.mk b) :
    BraidMonoid.mk _ (make_fin' n a bounded_a) = BraidMonoid.mk _ (make_fin' n b bounded_b) := by
  apply PresentedMonoid.exact at h
  induction h with
  | of x y old =>
    apply BraidMonoid.sound
    cases old with
    | adjacent i =>
      apply PresentedMonoid.rel_alone
      exact braid_rel_inf_to_fin_helper n _ _ (braid_rels_m_inf.adjacent i) _ _
    | separated i j hij =>
      apply PresentedMonoid.rel_alone
      apply braid_rel_inf_to_fin_helper n
      exact braid_rels_m_inf.separated i j hij
  | refl x => rfl
  | symm _ ih =>
    specialize ih bounded_b bounded_a
    exact ih.symm
  | trans _ _ ih1 ih2 =>
    specialize ih1 bounded_a
    rename_i a b c ab _
    have bounded_d : ∀ x, x∈ b → x < n.pred := by
      intro x hb
      have h_finset := FreeMonoid'.mem_symbols.mpr hb
      have H : x∈ a := by
        have H1 : a.symbols = b.symbols :=
          congrArg BraidMonoidInf.braid_generators (BraidMonoidInf.sound ab)
        have H2 : x ∈ b.symbols := by exact h_finset
        rw [← H1] at H2
        exact FreeMonoid'.mem_symbols.mp H2
      exact bounded_a x H
    specialize ih1 bounded_d
    specialize ih2 bounded_d bounded_b
    exact ih1.trans ih2
  | mul _ _ ih1 ih2 =>
    rename_i c d e f _ _
    have bounded_c : ∀ x ∈ c, x < n.pred :=
      fun x hx ↦ bounded_a x (FreeMonoid'.mem_mul.mpr (Or.inl hx))
    have bounded_d : ∀ x ∈ d, x < n.pred :=
      fun x hx ↦ bounded_b x (FreeMonoid'.mem_mul.mpr (Or.inl hx))
    have bounded_e : ∀ x ∈ e, x < n.pred :=
      fun x hx ↦ bounded_a x (FreeMonoid'.mem_mul.mpr (Or.inr hx))
    have bounded_f : ∀ x ∈ f, x < n.pred :=
      fun x hx ↦ bounded_b x (FreeMonoid'.mem_mul.mpr (Or.inr hx))
    specialize ih1 bounded_c bounded_d
    specialize ih2 bounded_e bounded_f
    rw [make_fin_helper, make_fin_helper]
    exact BraidMonoid.concat_mk ih1 ih2

theorem h_up_down {n : ℕ} : ∀ (u : FreeMonoid' (Fin n.pred)), ∀ (x : ℕ), x ∈ FreeMonoid'.map (fun i => ↑i) u → x < n.pred := by
    intro u t in_thing
    rcases FreeMonoid'.mem_map.mp in_thing with ⟨a, ha⟩
    rw [← ha.2]
    exact a.isLt

theorem fin_flop : ∀ u : FreeMonoid' (Fin n.pred), make_fin' n (FreeMonoid'.map (fun i => i.val) u) (h_up_down u) = u := by
    intro u
    induction u using FreeMonoid'.inductionOn'
    · simp only [map_one]
      rw [mk_fin_empty]
    rename_i h t iht
    have split_map : FreeMonoid'.map (fun i => i.val) (FreeMonoid'.of h * t) = FreeMonoid'.of h.val * FreeMonoid'.map (fun i => i.val) (t) := by exact rfl
    simp only [split_map]
    have bounded_h : ∀ (x : ℕ), x ∈ FreeMonoid'.of h.val → x < n.pred := by
      intro x hyp
      rw [FreeMonoid'.mem_of] at hyp
      rw [hyp]
      exact h.isLt
    rw [mk_fin_singleton h _ bounded_h]
    rw [iht]
    exact rfl

theorem flipit : make_fin' n (FreeMonoid'.map (fun i => i.val) u  *  v') bounded_a = u  *  make_fin' n v' v'_bound := by
    conv =>
    {
      enter [1]
      apply make_fin_helper (FreeMonoid'.map (fun i => i.val) u) v' (h_up_down u) v'_bound
    }
    simp only [mul_left_inj]
    apply fin_flop

theorem flipit' : make_fin' n (FreeMonoid'.map (fun i => i.val) u  *  v') bounded_a = u  *  make_fin' n v' v'_bound := by
    conv =>
    {
      enter [1]
      apply make_fin_helper (FreeMonoid'.map (fun i => i.val) u) v' (h_up_down u) v'_bound
    }
    simp only [mul_left_inj]
    apply fin_flop

theorem flipit2 : make_fin' n (FreeMonoid'.map (fun i => i.val) v  *  u') bounded_b = v  *  make_fin' n u' u'_bound := by
    conv =>
    {
      enter [1]
      apply make_fin_helper (FreeMonoid'.map (fun i => i.val) v) u' (h_up_down v) u'_bound
    }
    simp only [mul_left_inj]
    apply fin_flop
theorem rel_restriction {n : ℕ} (u v : FreeMonoid' (Fin n.pred)) (u' v' : FreeMonoid' ℕ)
    (u'_bound : ∀x, x∈ u' → x < n.pred) (v'_bound : ∀x, x∈ v' → x < n.pred)
    (br_inf_holds : BraidMonoidInf.mk ((FreeMonoid'.map (fun i => i.val) u)  *  v') =
    BraidMonoidInf.mk (FreeMonoid'.map (fun i => i.val) v  *  u'))
    (_ : ∀ (x : ℕ), x ∈ u' ∨ x ∈ v' → x < n.pred) :
    BraidMonoid.mk _ (u  *  make_fin' n v' v'_bound) =
    BraidMonoid.mk _ (v  *  make_fin' n u' u'_bound) := by
  have bounded_a : ∀ (x : ℕ), x ∈ FreeMonoid'.map (fun i => i.val) u  *  v' → x < n.pred := by
    intro x is_in
    simp only [FreeMonoid'.mem_mul, FreeMonoid'.mem_map] at is_in
    rcases is_in
    · next exists_thing =>
      rcases exists_thing with ⟨m, hm⟩
      rw [← hm.2]
      exact m.isLt
    apply v'_bound
    next in_v' =>
    exact in_v'
  have bounded_b : ∀ (x : ℕ), x ∈ FreeMonoid'.map (fun i => i.val) v  *  u' → x < n.pred := by
    intro x is_in
    simp only [FreeMonoid'.mem_mul] at is_in
    rcases is_in
    · next exists_thing =>
      rcases FreeMonoid'.mem_map.mp exists_thing with ⟨a, eq_x⟩
      rw [← eq_x.2]
      exact a.isLt
    apply u'_bound
    next in_u' =>
    exact in_u'
  have H := braid_rel_inf_to_fin n (FreeMonoid'.map (fun i => i.val) u  *  v') (FreeMonoid'.map (fun i => i.val) v  *  u') bounded_a bounded_b br_inf_holds
  rw [← flipit, ← flipit2]
  exact H

theorem common_right_mul_fin {n : ℕ} (u v : FreeMonoid' (Fin n.pred)) :
    ∃ (u' v' : FreeMonoid' (Fin n.pred)), (BraidMonoid.mk _ (u * v') = BraidMonoid.mk _ (v * u')) := by
  rcases common_right_mul_souped_three u v with ⟨u', v', huv'⟩
  use (make_fin' n u' (fun t t_h => huv'.right t (Or.inl t_h)))
  use (make_fin' n v' (fun t t_h => huv'.right t (Or.inr t_h)))
  exact rel_restriction _ _ _ _ _ _ huv'.1 huv'.2
