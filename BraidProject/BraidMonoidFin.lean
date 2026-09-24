import BraidProject.BraidMonoidInf

open PresentedMonoid

namespace Braid

open FreeMonoid in
inductive braid_rels_multi {n : ℕ} : FreeMonoid (Fin n) → FreeMonoid (Fin n) → Prop
  | adjacent (i j : Fin n) (h : i.val + 1 = j.val) :
      braid_rels_multi (FreeMonoid.of i * of j * of i) (FreeMonoid.of j * .of i * of j)
  | separated (i j : Fin n) (h : i.val + 1 < j.val) :
      braid_rels_multi (of i * of j) (of j * of i)

def braid_monoid_rels_fin : (n : ℕ) → FreeMonoid (Fin n.pred) → FreeMonoid (Fin n.pred) → Prop
  | 0  => (λ _ _ => False)
  | n + 1 => @braid_rels_multi n

/-- this is the braid monoid with n strands. those strands are numbered 0 to n-1.
the generators are numbered 0 to n-2 -/
def BraidMonoidFin (n : ℕ) := PresentedMonoid (braid_monoid_rels_fin n)

instance (n : ℕ) : Monoid (BraidMonoidFin n) := by unfold BraidMonoidFin; infer_instance

namespace BraidMonoidFin

def rel (n : ℕ):= PresentedMonoid.rel (braid_monoid_rels_fin n)

protected def of (n : ℕ) := PresentedMonoid.of (braid_monoid_rels_fin n)

protected def mk (n : ℕ) : FreeMonoid (Fin n.pred) →* BraidMonoidFin n := PresentedMonoid.mk (braid_monoid_rels_fin n)

theorem mul_mk {n : ℕ} {a b : FreeMonoid (Fin n.pred)} : BraidMonoidFin.mk n (a * b) =
    BraidMonoidFin.mk n a * BraidMonoidFin.mk n b := rfl

theorem mk_one {n : ℕ} : BraidMonoidFin.mk n 1 = 1 := rfl

instance {n : ℕ} : Monoid (BraidMonoidFin n) := by unfold BraidMonoidFin; infer_instance

theorem sound (h : BraidMonoidFin.rel n a b) : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b :=
  PresentedMonoid.sound h

theorem exact (h : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b ) : BraidMonoidFin.rel n a b :=
  Quotient.exact h

@[simp]
theorem List.map_mul {α β : Type} (f : α → β) (l1 l2 : FreeMonoid α) :
    List.map f (l1 * l2) = List.map f l1 ++ List.map f l2 := by
  rw [← List.map_append]
  congr

@[induction_eliminator]
theorem inductionOn {n : ℕ} {P : BraidMonoidFin n → Prop} (h : ∀ a, P (BraidMonoidFin.mk n a)) (b):
  P b := Quot.ind h b


-- theorem refl : BraidMonoidFin.rel n a a := PresentedMonoid.refl
-- theorem reg : ∀ c d, BraidMonoidFin.rel n a b → BraidMonoidFin.rel n (c * a * d) (c * b * d) :=
--   fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left h)
-- theorem symm : ∀ c d, BraidMonoidFin.rel n a b → BraidMonoidFin.rel n (c * b * d) (c * a * d) :=
--   fun _ _ h => PresentedMonoid.append_right (PresentedMonoid.append_left (PresentedMonoid.symm h))
theorem concat : BraidMonoidFin.rel n a b → BraidMonoidFin.rel n c d →
  BraidMonoidFin.rel n (a * c) (b * d) := PresentedMonoid.mul
-- theorem append_left : BraidMonoidFin.rel n c d →
--   BraidMonoidFin.rel n (a * c) (a * d) := PresentedMonoid.append_left
-- theorem append_right : BraidMonoidFin.rel n a b →
--   BraidMonoidFin.rel n (a * c) (b * c) := PresentedMonoid.append_right

-- theorem refl_mk : BraidMonoidFin.mk n a = BraidMonoidFin.mk n a := BraidMonoidFin.sound (refl)
-- theorem reg_mk : ∀ c d, BraidMonoidFin.mk n a = BraidMonoidFin.mk n b → BraidMonoidFin.mk n (c * a * d) =
--     BraidMonoidFin.mk n (c * b * d) :=
--   fun _ _ h => BraidMonoidFin.sound (reg _ _ (PresentedMonoid.exact h))
-- theorem symm_mk : ∀ c d, BraidMonoidFin.mk n a = BraidMonoidFin.mk n b → BraidMonoidFin.mk n (c * b * d) =
--     BraidMonoidFin.mk n (c * a * d) :=
--   fun _ _ h => BraidMonoidFin.sound (reg _ _ (PresentedMonoid.exact h.symm))
theorem concat_mk : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b →
    BraidMonoidFin.mk n c = BraidMonoidFin.mk n d →
    BraidMonoidFin.mk n (a * c) = BraidMonoidFin.mk n (b * d) :=
  fun h1 h2 => BraidMonoidFin.sound (concat (BraidMonoidFin.exact h1) (BraidMonoidFin.exact h2))
-- theorem append_left_mk : BraidMonoidFin.mk n c = BraidMonoidFin.mk n d →
--     BraidMonoidFin.mk n (a * c) = BraidMonoidFin.mk n (a * d) :=
--   fun h => BraidMonoidFin.sound (append_left (BraidMonoidFin.exact h))
-- theorem append_right_mk : BraidMonoidFin.mk n a = BraidMonoidFin.mk n b →
--     BraidMonoidFin.mk n (a * c) = BraidMonoidFin.mk n (b * c) :=
--   fun h => BraidMonoidFin.sound (append_right (BraidMonoidFin.exact h))

theorem comm {j k : Fin n.pred} (h : 1 <  Nat.dist j.val k.val) :
    BraidMonoidFin.mk n (FreeMonoid.of j * FreeMonoid.of k) = BraidMonoidFin.mk n (FreeMonoid.of k * FreeMonoid.of j) := by
  match n with
  | 0 =>
    simp at j
    have := j.2
    linarith
  | Nat.succ n =>
    apply PresentedMonoid.sound
    rcases Nat.le_dist_iff.mp h with hjk | hjk
    · exact PresentedMonoid.rels_alone <| braid_rels_multi.separated j k hjk
    exact PresentedMonoid.symm_alone <| braid_rels_multi.separated k j hjk

theorem comm_rel {j k : Fin n.pred} (h : 1 <  Nat.dist j.val k.val) :
    BraidMonoidFin.rel n (FreeMonoid.of j * FreeMonoid.of k) (FreeMonoid.of k * FreeMonoid.of j) :=
  PresentedMonoid.exact (comm h)

theorem braid {j k : Fin n.pred} (h : j.val.dist k = 1) :
    BraidMonoidFin.mk n (FreeMonoid.of j * FreeMonoid.of k * FreeMonoid.of j) =
    BraidMonoidFin.mk n (FreeMonoid.of k * FreeMonoid.of j * FreeMonoid.of k) := by
  match n with
  | 0 =>
    simp at j
    have := j.2
    linarith
  | Nat.succ n =>
  apply PresentedMonoid.sound
  rcases Nat.eq_dist_iff.mp h with hjk | hjk
  · exact PresentedMonoid.rels_alone <| braid_rels_multi.adjacent j k hjk
  exact PresentedMonoid.symm_alone <| braid_rels_multi.adjacent k j hjk

theorem braid_rel {j k : Fin n.pred} (h : j.val.dist k = 1) :
    BraidMonoidFin.rel n (FreeMonoid.of j * FreeMonoid.of k * FreeMonoid.of j)
      (FreeMonoid.of k * FreeMonoid.of j * FreeMonoid.of k) :=
  PresentedMonoid.exact (braid h)

open FreeMonoid in
theorem braid_monoid_rels_fin_rec
    {P : ∀ {n : ℕ}, FreeMonoid (Fin n.pred) → FreeMonoid (Fin n.pred) → Prop}
    {n : ℕ} {a b : FreeMonoid (Fin n.pred)}
    (h : braid_monoid_rels_fin n a b)
    (adj : ∀ {k : ℕ} (i j : Fin k) (hij : i.val + 1 = j.val ), P (n := k + 1) (of i * of j * of i)
          (of j * of i * of j))
    (sep : ∀ {k : ℕ} (i j : Fin k) (hij : i.val + 1 < j.val), P (n := k + 1) (of i * of j) (of j * of i)) :
    P a b := by
  cases n with
  | zero => cases h
  | succ n =>
      simp only [braid_monoid_rels_fin] at h
      cases h with
      | adjacent i j h => exact adj i j h
      | separated i j h => apply sep i j h

private theorem reverse_eq_of_rels {n : ℕ} (a b : FreeMonoid (Fin n.pred)) (h : braid_monoid_rels_fin n a b) :
    mk (braid_monoid_rels_fin n) a.reverse = mk (braid_monoid_rels_fin n) b.reverse := by
  apply braid_monoid_rels_fin_rec h
  · exact fun {n} i j h ↦ sound (rels_alone (braid_rels_multi.adjacent i j h))
  exact fun i j hij ↦ Eq.symm (sound (rels_alone (braid_rels_multi.separated i j hij)))


def reverse_braid : BraidMonoidFin n → BraidMonoidFin n :=
  PresentedMonoid.lift_of_mul (fun x => mk (braid_monoid_rels_fin n) <| FreeMonoid.reverse x)
  (fun h1 h2 => by simp [FreeMonoid.reverse_mul, h1, h2]) reverse_eq_of_rels

@[simp]
theorem reverse_braid_one {n : ℕ} : reverse_braid (1 : BraidMonoidFin n) = 1 := rfl

@[simp]
theorem reverse_braid_mk : reverse_braid (BraidMonoidFin.mk n a) =
  BraidMonoidFin.mk n (FreeMonoid.reverse a) := rfl

@[simp]
theorem reverse_braid_mul {a b : BraidMonoidFin n} : reverse_braid (a * b) =
    reverse_braid b * reverse_braid a := by
  induction a with | h a1 =>
  induction b with | h b1 =>
  rw [← BraidMonoidFin.mul_mk]
  grind [reverse_braid_mk, FreeMonoid.reverse_mul]

@[simp]
theorem reverse_reverse : reverse_braid (reverse_braid a) = a := by
  induction a
  rw [reverse_braid_mk, reverse_braid_mk, FreeMonoid.reverse_reverse]

theorem rel_reverse_reverse_iff : PresentedMonoid.rel (braid_monoid_rels_fin n) a1.reverse b1.reverse ↔
  PresentedMonoid.rel (braid_monoid_rels_fin n) a1 b1 := by
  have : ∀ a1 b1, PresentedMonoid.rel (braid_monoid_rels_fin n) a1 b1 →
      PresentedMonoid.rel (braid_monoid_rels_fin n) a1.reverse b1.reverse := by
    intro a1 b1 h
    induction h with
    | of _ _ h =>
      apply braid_monoid_rels_fin_rec h
      · exact fun {k} i j hij ↦ rels_alone (braid_rels_multi.adjacent i j hij)
      exact fun {k} i j hij ↦ symm_alone (braid_rels_multi.separated i j hij)
    | refl _ => exact PresentedMonoid.refl
    | symm _ h => exact ConGen.Rel.symm h
    | trans _ _ h1 h2 => exact h1.trans h2
    | mul _ _ h1 h2 =>
      rw [FreeMonoid.reverse_mul, FreeMonoid.reverse_mul]
      exact PresentedMonoid.mul h2 h1
  grind [FreeMonoid.reverse_reverse]

theorem reverse_eq_reverse_iff : a = b ↔ reverse_braid a = reverse_braid b := by
  constructor
  · intro h
    rw [h]
  intro h
  induction a ; induction b
  simp only [reverse_braid_mk] at h
  exact PresentedMonoid.sound (rel_reverse_reverse_iff.mp (PresentedMonoid.exact h))

open Braid
theorem toBraidGroupFin_helper (n : ℕ) : ∀ (a b : FreeMonoid (Fin n.pred)),
    (Braid.braid_monoid_rels_fin n) a b → ((FreeMonoid.lift fun a => σₙ a) a : BraidGroupFin n)=
    (FreeMonoid.lift fun a => σₙ a) b := by
  intro a b h
  apply braid_monoid_rels_fin_rec h
  · intro _ _ _ hij
    simp only [map_mul, Nat.pred_succ]
    apply BraidGroupFin.braid
    unfold Nat.dist
    grind
  intro _ i j hij
  simp only [map_mul, Nat.pred_succ]
  apply BraidGroupFin.comm
  unfold Nat.dist
  grind

def toBraidGroupFin (n : ℕ) : (BraidMonoidFin n) →* (BraidGroupFin n) := PresentedMonoid.lift _ (toBraidGroupFin_helper _)

@[simp]
theorem toBraidGroupFin_one : toBraidGroupFin n 1 = 1 := rfl

@[simp]
theorem toBraidGroupFin_of : toBraidGroupFin n (BraidMonoidFin.of n i) = σₙ i := rfl

@[simp]
theorem toBraidGroupFin_mk : toBraidGroupFin n (BraidMonoidFin.mk n a) =
  BraidGroupFin.mk n (FreeGroup.mk (List.map (fun x => (x, true)) a)) := by
  induction a with
  | one => rfl
  | of x => rfl
  | mul x y hx hy =>
    rw [map_mul, map_mul, hx, hy, List.map_mul, ← FreeGroup.mul_mk, map_mul]
    rfl

end BraidMonoidFin

open BraidMonoidFin

theorem BraidGroupFin.eq_of_BraidMonoidFin_eq {n : ℕ} {a1 b1 : FreeMonoid (Fin n.pred)}
  (h : BraidMonoidFin.mk n a1 = BraidMonoidFin.mk n b1) :
  BraidGroupFin.mk n (FreeGroup.mk (List.map (fun x => (x, true)) a1)) =
  BraidGroupFin.mk n (FreeGroup.mk (List.map (fun x => (x, true)) b1)) := by
  apply congr_arg (toBraidGroupFin n) at h
  rw [toBraidGroupFin_mk, toBraidGroupFin_mk] at h
  exact h

namespace BraidMonoidFin

theorem toLargerBraidMonoid_helper (n : ℕ) (lt : n.pred < m.pred) :∀ (a b : FreeMonoid (Fin n.pred)),
    braid_monoid_rels_fin n a b →
      ((@FreeMonoid.lift (Fin n.pred) (PresentedMonoid (braid_monoid_rels_fin m)) PresentedMonoid.instMonoid) fun x ↦
            BraidMonoidFin.of m ⟨x.1, Nat.lt_trans x.2 lt⟩)
          a =
        (FreeMonoid.lift fun x ↦ BraidMonoidFin.of m ⟨x.1, Nat.lt_trans x.2 lt⟩) b := by
  intro a b h
  match n with
  | 0 =>
    simp [braid_monoid_rels_fin] at h
  | n + 1 =>
    cases h with
    | adjacent i j h =>
      rw [map_mul, map_mul, map_mul, map_mul]
      apply BraidMonoidFin.braid
      unfold Nat.dist
      grind
    | separated i j h =>
      rw [map_mul, map_mul]
      apply BraidMonoidFin.comm
      unfold Nat.dist
      grind

def toLargerBraidMonoidFin (n : ℕ) (lt : n.pred < m.pred) :
  (BraidMonoidFin n) →* (BraidMonoidFin m) :=
  PresentedMonoid.lift (fun x => BraidMonoidFin.of m ⟨x.1, Nat.lt_trans x.2 lt⟩) (toLargerBraidMonoid_helper _ lt)

@[simp]
theorem toLargerBraidMonoidFin_one {n m : ℕ} (lt : n.pred < m.pred) : toLargerBraidMonoidFin n lt 1 = 1 := rfl

@[simp]
theorem toLargerBraidMonoidFin_of {n m : ℕ}  (lt : n.pred < m.pred) {i : Fin n.pred} :
  toLargerBraidMonoidFin n lt (BraidMonoidFin.of n i) = BraidMonoidFin.of m ⟨i.1, Nat.lt_trans i.2 lt⟩ := rfl

@[simp]
theorem toLargerBraidMonoidFin_mk {n m : ℕ} (lt : n.pred < m.pred) {a : FreeMonoid (Fin n.pred)}:
  toLargerBraidMonoidFin n lt (BraidMonoidFin.mk n a) =
  BraidMonoidFin.mk m (List.map (fun x => ⟨x.1, Nat.lt_trans x.2 lt⟩) a) := by
  induction a with
  | one => rfl
  | of x => rfl
  | mul x y hx hy =>
    rw [map_mul, map_mul, hx, hy, List.map_mul]
    rfl

theorem eq_of_SmallerBraidMonoidFin_eq {n m : ℕ}
    {a1 b1 : FreeMonoid (Fin n.pred)} {lt : n.pred < m.pred}
    (h : BraidMonoidFin.mk n a1 = BraidMonoidFin.mk n b1) :
  BraidMonoidFin.mk m (List.map (fun a => ⟨a.1, Nat.lt_trans a.2 lt⟩) a1) =
  BraidMonoidFin.mk m (List.map (fun a => ⟨a.1, Nat.lt_trans a.2 lt⟩) a1) := by
  apply congr_arg (toLargerBraidMonoidFin _ lt) at h
  rw [toLargerBraidMonoidFin_mk, toLargerBraidMonoidFin_mk] at h

def toBraidMonoidInf (n : ℕ) : (BraidMonoidFin n) →* (BraidMonoidInf) :=
  PresentedMonoid.lift (fun x => BraidMonoidInf.of x.1)
    (fun a b h => by
      apply braid_monoid_rels_fin_rec h
      · intro _ _ _ hij
        simp only [map_mul, Nat.pred_succ]
        apply BraidMonoidInf.braid_mk
        unfold Nat.dist
        grind
      intro _ i j hij
      simp only [map_mul, Nat.pred_succ]
      apply BraidMonoidInf.comm_mk
      unfold Nat.dist
      grind)

theorem toBraidMonoidInf_one {n : ℕ} : toBraidMonoidInf n 1 = 1 := rfl

theorem toBraidMonoidInf_of {n : ℕ} {i : Fin n.pred} :
  toBraidMonoidInf n (BraidMonoidFin.of n i) = BraidMonoidInf.of i := rfl

theorem toBraidMonoidInf_mk {n : ℕ} {a : FreeMonoid (Fin n.pred)}:
  toBraidMonoidInf n (BraidMonoidFin.mk n a) =
  BraidMonoidInf.mk (List.map (fun x => x.1) a) := by
  induction a with
  | one => rfl
  | of x => rfl
  | mul x y hx hy =>
    rw [map_mul, map_mul, hx, hy, List.map_mul]
    rfl

end BraidMonoidFin

theorem BraidMonoidInf.eq_of_BraidMonoidFin_eq {n : ℕ} {a1 b1 : FreeMonoid (Fin n.pred)}
    (h : BraidMonoidFin.mk n a1 = BraidMonoidFin.mk n b1) :
    BraidMonoidInf.mk (List.map (fun x => x.1) a1) = BraidMonoidInf.mk (List.map (fun x => x.1) b1) := by
  apply congr_arg (BraidMonoidFin.toBraidMonoidInf n) at h
  rw [BraidMonoidFin.toBraidMonoidInf_mk, BraidMonoidFin.toBraidMonoidInf_mk] at h
  exact h

theorem BraidGroupInf.eq_of_BraidMonoidFin_eq {n : ℕ} {a1 b1 : FreeMonoid (Fin n.pred)}
    (h : BraidMonoidFin.mk n a1 = BraidMonoidFin.mk n b1) :
    BraidGroupInf.mk (FreeGroup.mk (List.map (fun x => (x.1, true)) a1)) =
    BraidGroupInf.mk (FreeGroup.mk (List.map (fun x => (x.1, true)) b1)) := by
  apply congr_arg (BraidMonoidFin.toBraidGroupFin n) at h
  rw [BraidMonoidFin.toBraidGroupFin_mk, BraidMonoidFin.toBraidGroupFin_mk] at h
  apply congr_arg (BraidGroupFin.toBraidGroupInf n) at h
  rw [BraidGroupFin.toBraidGroupInf_mk_mk, BraidGroupFin.toBraidGroupInf_mk_mk, List.map_map, List.map_map] at h
  exact h

def BraidMonoidInf.toBraidMonoidFin :=
  PresentedMonoid.lift (fun a => σ a) toBraidGroupInf_helper
