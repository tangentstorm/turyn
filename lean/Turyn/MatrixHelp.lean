import Turyn.TSequence

open Finset
open BigOperators

/-!
# Matrix Helpers

Reusable list, row, and circulant lemmas for the standalone Hadamard pipeline.
-/

/-- Dot product of two integer lists. -/
def listDotProduct : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + listDotProduct xs ys

/-- Reverse a row, corresponding to the reversal matrix action on columns. -/
def applyR (row : List Int) : List Int := row.reverse

/-- Negate every entry in a row. -/
def negRow (row : List Int) : List Int := row.map (· * (-1))

@[simp] theorem applyR_length (row : List Int) : (applyR row).length = row.length := by
  simp [applyR]

@[simp] theorem negRow_length (row : List Int) : (negRow row).length = row.length := by
  simp [negRow]

lemma applyR_getD {row : List Int} {k : Nat} (hk : k < row.length) :
    (applyR row).getD k 0 = row.getD (row.length - 1 - k) 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa [applyR] using hk)]
  rw [List.getD_eq_getElem _ _ (by omega)]
  simpa [applyR] using List.getElem_reverse (l := row) (i := k) hk

/-- Circulant matrix rows from a length-`m` first row. -/
def circulantRow (m : Nat) (a : List Int) (i : Nat) : List Int :=
  (List.range m).map fun j =>
    a.getD ((j + m - i) % m) 0

/-- Circulant matrix rows from a length-`m` first row. -/
def circulantRows (m : Nat) (a : List Int) : List (List Int) :=
  (List.range m).map fun i => circulantRow m a i

@[simp] theorem circulantRows_length (m : Nat) (a : List Int) :
    (circulantRows m a).length = m := by
  simp [circulantRows]

@[simp] theorem circulantRow_length (m : Nat) (a : List Int) (i : Nat) :
    (circulantRow m a i).length = m := by
  simp [circulantRow]

lemma periodicAutocorr_eq_sum_of_length {a : List Int} {m s : Nat}
    (ha : a.length = m) (hm : m ≠ 0) :
    periodicAutocorr a s =
      ∑ i ∈ Finset.range m, a.getD i 0 * a.getD ((i + s) % m) 0 := by
  unfold periodicAutocorr
  simp [ha, hm]

lemma combinedPeriodicAutocorr_eq_sum_of_lengths
    {a b c d : List Int} {m s : Nat}
    (ha : a.length = m) (hb : b.length = m) (hc : c.length = m) (hd : d.length = m)
    (hm : m ≠ 0) :
    combinedPeriodicAutocorr a b c d s =
      ∑ i ∈ Finset.range m,
        (a.getD i 0 * a.getD ((i + s) % m) 0 +
          b.getD i 0 * b.getD ((i + s) % m) 0 +
          c.getD i 0 * c.getD ((i + s) % m) 0 +
          d.getD i 0 * d.getD ((i + s) % m) 0) := by
  rw [combinedPeriodicAutocorr]
  rw [periodicAutocorr_eq_sum_of_length ha hm,
      periodicAutocorr_eq_sum_of_length hb hm,
      periodicAutocorr_eq_sum_of_length hc hm,
      periodicAutocorr_eq_sum_of_length hd hm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

lemma pmOne_bool_of_eq (x : Int) (hx : x = 1 ∨ x = -1) :
    (x == 1 || x == -1) = true := by
  rcases hx with rfl | rfl <;> decide

lemma list_all_pmOne_of_forall (row : List Int)
    (hrow : ∀ v, v ∈ row → v = 1 ∨ v = -1) :
    row.all (fun v => v == 1 || v == -1) = true := by
  induction row with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : x = 1 ∨ x = -1 := hrow x (by simp)
      have hxbool : (x == 1 || x == -1) = true := pmOne_bool_of_eq x hx
      have hxs : ∀ v, v ∈ xs → v = 1 ∨ v = -1 := by
        intro v hv
        exact hrow v (by simp [hv])
      simp [hxbool, ih hxs]

lemma append_pmOne_mem {r₁ r₂ : List Int}
    (h₁ : ∀ v, v ∈ r₁ → v = 1 ∨ v = -1)
    (h₂ : ∀ v, v ∈ r₂ → v = 1 ∨ v = -1) :
    ∀ v, v ∈ r₁ ++ r₂ → v = 1 ∨ v = -1 := by
  intro v hv
  simp at hv
  rcases hv with hv | hv
  · exact h₁ v hv
  · exact h₂ v hv

lemma applyR_pmOne_mem {row : List Int}
    (hrow : ∀ v, v ∈ row → v = 1 ∨ v = -1) :
    ∀ v, v ∈ applyR row → v = 1 ∨ v = -1 := by
  intro v hv
  have hmem : v ∈ row := by
    simpa [applyR] using hv
  exact hrow v hmem

lemma negRow_pmOne_mem {row : List Int}
    (hrow : ∀ v, v ∈ row → v = 1 ∨ v = -1) :
    ∀ v, v ∈ negRow row → v = 1 ∨ v = -1 := by
  intro v hv
  unfold negRow at hv
  rw [List.mem_map] at hv
  rcases hv with ⟨u, hu, rfl⟩
  rcases hrow u hu with hu1 | hu1 <;> simp [hu1]

lemma circulantRow_pmOne_mem {m : Nat} {x : List Int}
    (hx_len : x.length = m)
    (hx_pm : ∀ j, j < m → x.getD j 0 = 1 ∨ x.getD j 0 = -1)
    (i : Nat) :
    ∀ v, v ∈ circulantRow m x i → v = 1 ∨ v = -1 := by
  intro v hv
  simp [circulantRow] at hv
  rcases hv with ⟨j, hj, rfl⟩
  have hmod : (j + m - i) % m < m := by
    by_cases hm : m = 0
    · subst hm
      simp at hj
    · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
  exact hx_pm ((j + m - i) % m) hmod

lemma listDotProduct_eq_sum {a b : List Int} (h : a.length = b.length) :
    listDotProduct a b =
      ∑ i ∈ Finset.range a.length, a.getD i 0 * b.getD i 0 := by
  revert b
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil =>
          simp [listDotProduct]
      | cons y ys =>
          simp at h
  | cons x xs ih =>
      intro b h
      cases b with
      | nil =>
          simp at h
      | cons y ys =>
          simp at h
          simp [listDotProduct]
          rw [Finset.sum_range_succ']
          simp [ih h, add_comm]

lemma listDotProduct_comm {a b : List Int} (h : a.length = b.length) :
    listDotProduct a b = listDotProduct b a := by
  rw [listDotProduct_eq_sum h, listDotProduct_eq_sum h.symm]
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma sum_range_reflect {α : Type} [AddCommMonoid α] {m : Nat} (hm : m ≠ 0) (f : Nat → α) :
    (∑ k ∈ Finset.range m, f k) = ∑ k ∈ Finset.range m, f (m - 1 - k) := by
  simpa using (Finset.sum_range_reflect (f := f) (n := m)).symm

/-- Dot product of concatenated rows splits when the first parts have equal length. -/
lemma listDotProduct_append (a1 a2 b1 b2 : List Int)
    (h : a1.length = b1.length) :
    listDotProduct (a1 ++ a2) (b1 ++ b2) =
      listDotProduct a1 b1 + listDotProduct a2 b2 := by
  revert b1
  induction a1 with
  | nil =>
      intro b1 h
      cases b1 with
      | nil =>
          simp [listDotProduct]
      | cons y ys =>
          simp at h
  | cons x xs ih =>
      intro b1 h
      cases b1 with
      | nil =>
          simp at h
      | cons y ys =>
          simp at h
          simp [listDotProduct, ih ys h]
          ring

/-- Simultaneous reversal preserves dot product. -/
lemma listDotProduct_reverse (a b : List Int) (h : a.length = b.length) :
    listDotProduct (applyR a) (applyR b) = listDotProduct a b := by
  unfold applyR
  revert b
  induction a using List.reverseRecOn with
  | nil =>
      intro b h
      cases b with
      | nil =>
          simp [listDotProduct]
      | cons y ys =>
          simp at h
  | append_singleton a x ih =>
      intro b h
      cases b using List.reverseRecOn with
      | nil =>
          simp at h
      | append_singleton b y =>
          simp at h
          rw [List.reverse_append, List.reverse_append]
          have happ := listDotProduct_append a [x] b [y] h
          simp [listDotProduct] at happ
          simpa [listDotProduct, ih b h, add_comm, add_left_comm, add_assoc] using happ.symm

/-- Negating the left row negates the dot product. -/
lemma listDotProduct_negRow_left (a b : List Int) :
    listDotProduct (negRow a) b = - listDotProduct a b := by
  revert b
  induction a with
  | nil =>
      intro b
      cases b <;> simp [listDotProduct, negRow]
  | cons x xs ih =>
      intro b
      cases b with
      | nil =>
          simp [listDotProduct, negRow]
      | cons y ys =>
          simp [listDotProduct, negRow]
          simpa [add_assoc, add_left_comm, add_comm, negRow] using
            congrArg (fun t => -(x * y) + t) (ih ys)

/-- Negating the right row negates the dot product. -/
lemma listDotProduct_negRow_right (a b : List Int) :
    listDotProduct a (negRow b) = - listDotProduct a b := by
  revert b
  induction a with
  | nil =>
      intro b
      cases b <;> simp [listDotProduct, negRow]
  | cons x xs ih =>
      intro b
      cases b with
      | nil =>
          simp [listDotProduct, negRow]
      | cons y ys =>
          simp [listDotProduct, negRow]
          simpa [add_assoc, add_left_comm, add_comm, negRow] using
            congrArg (fun t => -(x * y) + t) (ih ys)

lemma circulantRow_getD {m : Nat} (x : List Int) {r c : Nat} (hc : c < m) :
    (circulantRow m x r).getD c 0 = x.getD ((c + m - r) % m) 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa [circulantRow] using hc)]
  simp [circulantRow]

lemma circulantRow_dot_eq_sum {m : Nat} (x : List Int)
    {i j : Nat} (hi : i < m) (hj : j < m) :
    listDotProduct (circulantRow m x i) (circulantRow m x j) =
      ∑ k ∈ Finset.range m,
        x.getD ((k + m - i) % m) 0 * x.getD ((k + m - j) % m) 0 := by
  have hlen : (circulantRow m x i).length = (circulantRow m x j).length := by
    simp [circulantRow]
  rw [listDotProduct_eq_sum hlen]
  simp only [circulantRow_length]
  apply Finset.sum_congr rfl
  intro k hk
  rw [circulantRow_getD x (r := i) (Finset.mem_range.mp hk),
      circulantRow_getD x (r := j) (Finset.mem_range.mp hk)]

/-- Self dot product of a `±1` row is its length. -/
lemma listDotProduct_self_pmone (a : List Int)
    (ha : ∀ j, j < a.length → a.getD j 0 = 1 ∨ a.getD j 0 = -1) :
    listDotProduct a a = a.length := by
  rw [listDotProduct_eq_sum rfl]
  have hsquare : ∀ i ∈ Finset.range a.length, a.getD i 0 * a.getD i 0 = 1 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)]
    rcases ha i (Finset.mem_range.mp hi) with h | h
    · rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)] at h
      simp [h]
    · rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hi)] at h
      simp [h]
  calc
    ∑ i ∈ Finset.range a.length, a.getD i 0 * a.getD i 0
      = ∑ i ∈ Finset.range a.length, (1 : Int) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsquare i hi
    _ = a.length := by simp

/-- Zero-lag periodic autocorrelation of a `±1` sequence is its length. -/
lemma periodicAutocorr_zero_pmone {m : Nat} (a : List Int)
    (ha_len : a.length = m)
    (ha_pm : ∀ j, j < m → a.getD j 0 = 1 ∨ a.getD j 0 = -1) :
    periodicAutocorr a 0 = m := by
  by_cases hm : m = 0
  · subst hm
    have ha_nil : a = [] := List.eq_nil_of_length_eq_zero ha_len
    subst ha_nil
    simp [periodicAutocorr]
  · rw [periodicAutocorr_eq_sum_of_length ha_len hm]
    have hsquare : ∀ i ∈ Finset.range m, a.getD i 0 * a.getD ((i + 0) % m) 0 = 1 := by
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have hpm := ha_pm i hi'
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
      rw [← ha_len] at hi'
      rw [List.getD_eq_getElem _ _ hi']
      rcases hpm with h | h
      · rw [List.getD_eq_getElem _ _ (by simpa [ha_len] using Finset.mem_range.mp hi)] at h
        simp [h]
      · rw [List.getD_eq_getElem _ _ (by simpa [ha_len] using Finset.mem_range.mp hi)] at h
        simp [h]
    calc
      ∑ i ∈ Finset.range m, a.getD i 0 * a.getD ((i + 0) % m) 0
        = ∑ i ∈ Finset.range m, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hsquare i hi
      _ = m := by simp
