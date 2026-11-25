import PEqualNP.Defs

-- Counterproof of project assignment L-meta-16093.
-- The live-wire search is adapted from PEqualNP.Outside.L_meta_16561 in
-- open-goat/pequalnp-proofs. Here the sampled function, the input restriction,
-- the proof that the restriction saves a binary gate, and the certificate are
-- specific to L-meta-16093. The project repository contains the Apache 2.0 license.
--
-- Fix input 5 to false. Seven binary operations fail even when negations
-- are free. Changing input 5 can change the output, so a circuit for the
-- six-input function must have at least nine AND or OR gates. A circuit
-- that also contains a unary NOT therefore has at least ten gates.

namespace PEqualNP.Outside.L_meta_16093_counterproof

open PEqualNP.CircuitLowerBounds

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 62

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 31 := ((x >>> 31) ^^^ x).setWidth 31
def cuts (ws : List W) : BitVec 31 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 31) ++ (0 : BitVec 31)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 31) (w : W) : Prop :=
  w.getLsbD (31+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 31) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 31+i.val < 62 := by omega
  have hi' : i.val < 62 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem goal_differs {t : W} (ht : t = goal ∨ t = ~~~goal) : ∀ i, differs i t := by
  rcases ht with rfl | rfl <;> unfold differs <;> decide +kernel

theorem cuts_spec (ws : List W) (i : Fin 31) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs hg _) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 31)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem and_ones (x : W) : x &&& ~~~0 = x :=
  (congrArg (x &&& ·) (BitVec.not_zero (n := 62))).trans BitVec.and_allOnes

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · rw [BitVec.and_comm, and_ones]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · rw [and_ones]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

def bit (k : Fin 62) (z : W) : Bool := z[k.val]
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit (w : List W) (i : ℕ) (k : Fin 62) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 62) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#62)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    and_ones]

  · exact .inl (.inr (.inl rfl))
  · exact .inl (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inl (available_read hw _)
  · exact .inl (available_read hw _)
  · exact holds_not (available_read hw _)
  · exact and_reach (available_read hw _) (available_read hw _)
  · exact or_reach (available_read hw _) (available_read hw _)
  · exact holds_not (available_read hw _)

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide +kernel : goal ≠ 0) zero)
    · exact False.elim ((by decide +kernel : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


abbrev Tr := W × Bool
def agrees (u : Tr) : Prop := bit 2 u.1 = u.2 ∨ u.1 = 0 ∨ u.1 = ~~~0
def traceAnd (a b : Tr) : Tr := (a.1 &&& b.1, a.2 && b.2)
def traceOr (a b : Tr) : Tr := (a.1 ||| b.1, a.2 || b.2)
def traceNot (a : Tr) : Tr := (~~~a.1, !a.2)

theorem agrees_not {a : Tr} (ha : agrees a) : agrees (traceNot a) := by
  rcases ha with p | p | p
  · left; simp [traceNot, bit, ← p]
  · right; right; simp [traceNot, p]
  · right; left; simp [traceNot, p]

theorem and_break {a b : Tr} {av : Finset W} (ha : agrees a) (hb : agrees b)
    (aok : holds av a.1) (bok : holds av b.1) (bad : ¬ agrees (traceAnd a b)) :
    holds av (traceAnd a b).1 := by
  rcases ha with p | p | p
  · rcases hb with q | q | q
    · exfalso; apply bad; left; simp [traceAnd, bit, ← p, ← q]
    · exact .inl (by simp [traceAnd, q])
    · simpa only [traceAnd, q, and_ones] using aok
  · exact .inl (by simp [traceAnd, p])
  · simpa only [traceAnd, p, BitVec.and_comm (~~~0) b.1, and_ones] using bok

theorem orzero (x : W) : x ||| (0 : W) = x := BitVec.or_zero
theorem zeroor (x : W) : (0 : W) ||| x = x := (BitVec.or_comm ..).trans (orzero x)
theorem orones (x : W) : x ||| (~~~(0:W)) = ~~~(0:W) := by
  have h : ~~~(0:W) = BitVec.allOnes _ := by decide +kernel
  rw [h]
  exact BitVec.or_allOnes
theorem onesor (x : W) : (~~~(0:W)) ||| x = ~~~(0:W) := (BitVec.or_comm ..).trans (orones x)

theorem or_break {a b : Tr} {av : Finset W} (ha : agrees a) (hb : agrees b)
    (aok : holds av a.1) (bok : holds av b.1) (bad : ¬ agrees (traceOr a b)) :
    holds av (traceOr a b).1 := by
  rcases ha with p | p | p
  · rcases hb with q | q | q
    · exfalso; apply bad; left; simp [traceOr, bit, ← p, ← q]
    · simpa only [traceOr, q, orzero] using aok
    · exact .inr (.inl (by simpa only [traceOr, q] using orones a.1))
  · simpa only [traceOr, p, zeroor] using bok
  · exact .inr (.inl (by simpa only [traceOr, p] using onesor b.1))

theorem read_map_trace {α β : Type} (w : List α) (f : α → β) (i : Nat) (a : α) :
    (w.map f).getD i (f a) = f (w.getD i a) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h)]

def nextTrace (w : List Tr) (g : Gate) : Tr := (action (w.map Prod.fst) g,
  g.op.eval (g.inputs.map fun i => (w.map Prod.snd).getD i false))

theorem break_gate {w : List Tr} {g : Gate} {av : Finset W} (legalg : legal g)
    (good : ∀ u ∈ w, agrees u) (hw : ∀ u ∈ w, holds av u.1)
    (bad : ¬ agrees (nextTrace w g)) : isBinary g = true ∧ holds av (nextTrace w g).1 := by
  let rd (i : Nat) := w.getD i (0,false)
  have fr (i : Nat) : (w.map Prod.fst).getD i 0 = (rd i).1 := read_map_trace w Prod.fst i (0,false)
  have sr (i : Nat) : (w.map Prod.snd).getD i false = (rd i).2 := read_map_trace w Prod.snd i (0,false)
  have H (i : Nat) : agrees (rd i) ∧ holds av (rd i).1 := by
    by_cases h : i < w.length
    · have e : rd i = w[i] := by simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [e]; exact ⟨good _ (List.getElem_mem h), hw _ (List.getElem_mem h)⟩
    · simp only [rd, List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
      exact ⟨.inr (.inl rfl), .inl rfl⟩
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := legalg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [nextTrace, action, GateOp.eval, List.map_cons, List.map_nil, List.foldr_cons,List.foldr_nil,
      List.head?_cons,List.head?_nil,List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,
      Option.getD_some,Option.getD_none,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,
      Bool.and_true,Bool.or_false,Bool.not_false,orzero,and_ones,fr,sr,isBinary] at bad ⊢
  · exact False.elim (bad (.inr (.inr rfl)))
  · exact False.elim (bad (.inr (.inl rfl)))
  · exact False.elim (bad (.inr (.inr rfl)))
  · exact False.elim (bad (H i).1)
  · exact False.elim (bad (H i).1)
  · exact False.elim (bad (agrees_not (H i).1))
  · exact ⟨True.intro, and_break (H i).1 (H j).1 (H i).2 (H j).2 bad⟩
  · exact ⟨True.intro, or_break (H i).1 (H j).1 (H i).2 (H j).2 bad⟩
  · exact False.elim (bad (agrees_not (H i).1))

theorem compile_loss (gs : List Gate) (out : Nat) (hg : ∀ g ∈ gs, legal g)
    (w : List Tr) (av : Finset W) (good : ∀ u ∈ w, agrees u)
    (hw : ∀ u ∈ w, holds av u.1)
    (he : ∀ k, (gs.foldl step ((w.map Prod.fst).map (bit k))).getD out false = bit k goal)
    (high : (gs.foldl step (w.map Prod.snd)).getD out false = true) :
    ∃ k < binaryCost gs, ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t k av := by
  induction gs generalizing w av with
  | nil =>
    let u := w.getD out (0,false)
    have value : u.1 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      have row := he ⟨i,hi⟩
      rw [List.foldl_nil, read_bit, read_map_trace w Prod.fst out (0,false)] at row
      exact row
    have probe : u.2 = true := by
      rw [List.foldl_nil, read_map_trace w Prod.snd out (0,false)] at high
      exact high
    have ok : agrees u := by
      by_cases h : out < w.length
      · have eq : u = w[out] := by simp [u, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
        exact eq ▸ good _ (List.getElem_mem h)
      · simp only [u,List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
        exact .inr (.inl rfl)
    rcases ok with p | p | p
    · rw [value, probe] at p
      exact False.elim ((by decide +kernel : bit 2 goal ≠ true) p)
    · rw [value] at p; exact False.elim ((by decide +kernel : goal ≠ 0) p)
    · rw [value] at p; exact False.elim ((by decide +kernel : goal ≠ ~~~0) p)
  | cons g gs ih =>
    let z := nextTrace w g
    let nw := w ++ [z]
    have htail := fun t (h : t ∈ gs) => hg t (by simp [h])
    have nextEval (k : Fin 62) :
        (gs.foldl step ((nw.map Prod.fst).map (bit k))).getD out false = bit k goal := by
      simpa only [List.foldl_cons, action_spec (w.map Prod.fst) g (hg g (by simp)) k,
        nw, List.map_append, List.map_cons, List.map_nil, z, nextTrace] using he k
    have nextHigh : (gs.foldl step (nw.map Prod.snd)).getD out false = true := by
      simpa only [List.foldl_cons, step, nw, List.map_append, List.map_cons, List.map_nil, z, nextTrace] using high
    have extend (A : Finset W) (old : ∀ u ∈ w, holds A u.1) (hz : holds A z.1) :
        ∀ u ∈ nw, holds A u.1 := by
      intro u hu; rcases List.mem_append.mp hu with l|r
      · exact old u l
      · exact (List.mem_singleton.mp r) ▸ hz
    have holdmap : ∀ u ∈ w.map Prod.fst, holds av u := by
      intro u hu; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu; exact hw _ hv
    by_cases keep : agrees z
    · have nextGood : ∀ u ∈ nw, agrees u := by
        intro u hu; rcases List.mem_append.mp hu with l|r
        · exact good _ l
        · exact (List.mem_singleton.mp r) ▸ keep
      have reach := gate_reach (w.map Prod.fst) av holdmap g (hg g (by simp))
      cases hb : isBinary g
      · simp only [hb, Bool.false_eq_true, ite_false] at reach
        simpa [binaryCost,hb] using ih htail nw av nextGood (extend av hw reach) nextEval nextHigh
      · simp only [hb, ite_true] at reach
        have cost : binaryCost (g::gs) = binaryCost gs + 1 := by simp [binaryCost,hb]
        rw [cost]
        rcases reach with old | ⟨a,ha,b,hb',ne,c,hc,ok⟩
        · obtain ⟨j,hj,t,ht,run⟩ := ih htail nw av nextGood (extend av hw old) nextEval nextHigh
          exact ⟨j,by omega,t,ht,run⟩
        · have sup : ∀ u ∈ w, holds (insert c av) u.1 :=
            fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)
          obtain ⟨j,hj,t,ht,run⟩ := ih htail nw (insert c av) nextGood
            (extend _ sup ok) nextEval nextHigh
          exact ⟨j+1,by omega,t,ht,Or.inr ⟨a,ha,b,hb',ne,c,hc,run⟩⟩
    · obtain ⟨hb, FREE⟩ := break_gate (hg g (by simp)) good hw keep
      have nextHold : ∀ u ∈ nw.map Prod.fst, holds av u := by
        intro u hu; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
        exact extend av hw FREE v hv
      obtain ⟨t,ht,run⟩ := compile gs out htail (nw.map Prod.fst) av nextHold nextEval
      refine ⟨binaryCost gs, ?_, t,ht,run⟩
      simp [binaryCost,hb]
def ins : List W := [4012139918074606445, 1070536041623358610, 1833976111034732316, 3133986303800512480, 4287423703471353856]

end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
open PEqualNP.CircuitLowerBounds
def traceInputs : List Tr := [(ins.getD 0 0, true), (ins.getD 1 0, false), (ins.getD 2 0, true), (ins.getD 3 0, false), (ins.getD 4 0, false), (0,true)]
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3936938664 * 2 ^ 32 + 3936913544) (∑ i : Fin 6, if x i then 2 ^ i.val else 0)
theorem trace_good : ∀ u ∈ traceInputs, agrees u := by
  intro u hu
  simp only [traceInputs, List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact .inl (by decide +kernel) | exact .inr (.inl rfl)
theorem trace_init : ∀ u ∈ traceInputs, holds ins.toFinset u.1 := by
  intro u hu
  simp only [traceInputs,List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact .inr (.inr ⟨_, (by exact @of_decide_eq_true _ _ rfl), .inl rfl⟩) | exact .inl rfl
theorem trace_samples : ∀ k : Fin 62, target (fun i => bit k ((traceInputs.map Prod.fst).getD i.val 0)) = bit k goal :=
  by decide +kernel
theorem trace_bound (noSmall : search 7 ins = false) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) :
    8 < binaryCost C.gates := by
  by_contra! small
  have legalC : ∀ g ∈ C.gates, legal g := fun g hg => hf g hg
  have eval (k : Fin 62) :
      (C.gates.foldl step ((traceInputs.map Prod.fst).map (bit k))).getD C.output false = bit k goal := by
    let x : Fin 6 → Bool := fun i => bit k ((traceInputs.map Prod.fst).getD i.val 0)
    have same : List.ofFn x = (traceInputs.map Prod.fst).map (bit k) := by
      apply List.ext_getElem
      · simp [traceInputs]
      · intro i hi hj
        have hlt : i < (traceInputs.map Prod.fst).length := by simpa using hj
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt,Option.getD_some]
    change C.eval ((traceInputs.map Prod.fst).map (bit k)) = bit k goal
    rw [← same, he]; exact trace_samples k
  let x : Fin 6 → Bool := fun i => (i.val==0 || i.val==2 || i.val==5)
  have endpoint : C.eval (traceInputs.map Prod.snd) = true := by
    rw [← show List.ofFn x = traceInputs.map Prod.snd from by decide +kernel, he]
    decide +kernel
  obtain ⟨k,hk,t,ht,run⟩ := compile_loss C.gates C.output legalC traceInputs ins.toFinset
    trace_good trace_init eval endpoint
  have lift {a b : Nat} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) :
      build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.false_ne_true
    (noSmall.symm.trans (search_complete ht 7 ins (by decide +kernel) (lift (by omega) run)))

end PEqualNP.Outside.L_meta_16093_counterproof

theorem PEqualNP.Outside.L_meta_16093_counterproof_closing (h : PEqualNP.Outside.L_meta_16093_counterproof.search 7 PEqualNP.Outside.L_meta_16093_counterproof.ins = false) : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
    g.inputs.length = 1) ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
    Nat.testBit (3936938664 * 2 ^ 32 + 3936913544) (∑ i : Fin 6, if x i then 2 ^ i.val else 0)) := by
  rintro ⟨C,hf,⟨g,hg,hop,_⟩,small,he⟩
  have many := PEqualNP.Outside.L_meta_16093_counterproof.trace_bound h C hf he
  have cut : PEqualNP.Outside.L_meta_16093_counterproof.binaryCost C.gates < C.size :=
    (List.length_filter_lt_length_iff_exists).mpr ⟨g,hg,by simp [PEqualNP.Outside.L_meta_16093_counterproof.isBinary,hop]⟩
  omega

namespace PEqualNP.Outside.L_meta_16093_counterproof
abbrev S := Nat × List W
def choices (e : Nat) (a b : W) (r : List W) (w : W) : List S :=
  let v := sep w ||| cuts r
  let opts : List (Bool × S) := [
      (v == -1, e, w :: r),
      ((e != 0) && (v ||| sep a == -1), e-1, w :: a :: r),
      ((e != 0) && (v ||| sep b == -1), e-1, w :: b :: r),
      (decide (e ≥ 2) && (v ||| sep a ||| sep b == -1), e-2, w :: a :: b :: r)]
  (opts.filter Prod.fst).map Prod.snd

def nexts (s : S) : List S :=
  (pairs s.2).flatMap (fun (a,b,r) => (ops a b).flatMap (choices s.1 a b r))

theorem dispatch_choices (e : Nat) (next : Nat → List W → Bool) (a b : W) (r : List W) :
    dispatch e next a b r = ((ops a b).flatMap (choices e a b r)).any (fun s => next s.1 s.2) := by
  rw [List.any_flatMap]
  unfold dispatch
  dsimp only
  apply congrArg (List.any (ops a b))
  funext w
  simp only [choices, List.any_map, List.any_filter, List.any_cons, List.any_nil, Bool.or_false,
    Function.comp_apply, Bool.and_or_distrib_left, Bool.and_assoc]
  ac_rfl

theorem opt_next (k : Nat) (e : Nat) (w : List W) :
    optimized (k+1) e w = ((w == [goal] || w == [~~~goal]) ||
      (nexts (e, w)).any (fun s => optimized k s.1 s.2)) := by
  rw [nexts, List.any_flatMap]
  rw [optimized]
  apply congrArg (fun z => (w == [goal] || w == [~~~goal]) || z)
  apply congrArg (List.any (pairs w))
  funext ⟨a,b,r⟩
  exact dispatch_choices _ _ _ _ _
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
-- Each word records the value of one wire on the selected pairs of inputs.
-- Giving repeated words one name keeps the exhaustive certificate small.
def wireWord0 : W := 4012139918074606445
def wireWord1 : W := 1070536041623358610
def wireWord2 : W := 4287423703471353856
def wireWord3 : W := 1833976111034732316
def wireWord4 : W := 3133986303800512480
def wireWord5 : W := 1833973319305986048
def wireWord6 : W := 3133983211424055296
def wireWord7 : W := 2453450384165367808
def wireWord8 : W := 1153440492047298560
def wireWord9 : W := 470989942642704384
def wireWord10 : W := 3687877603135352832
def wireWord11 : W := 3541149976787251200
def wireWord12 : W := 324262314939253613
def wireWord13 : W := 4611686018410609810
def wireWord14 : W := 4287347673725341692
def wireWord15 : W := 680614741109903104
def wireWord16 : W := 2453371562690609376
def wireWord17 : W := 1153361369924829212
def wireWord18 : W := 4611686017873248237
def wireWord19 : W := 599830365682928656
def wireWord20 : W := 1234145745351803660
def wireWord21 : W := 745916178709351552
def wireWord22 : W := 2388070125091160928
def wireWord23 : W := 4611686018138472317
def wireWord24 : W := 2791728746268
def wireWord25 : W := 3092376457184
def wireWord26 : W := 3541149975431902061
def wireWord27 : W := 470705675940429954
def wireWord28 : W := 2534440204001870688
def wireWord29 : W := 324619862914007058
def wireWord30 : W := 4611686018410607469
def wireWord31 : W := 599546100336001024
def wireWord32 : W := 1234430010970866444
def wireWord33 : W := 2777709907103740001
def wireWord34 : W := 599546100063865872
def wireWord35 : W := 2304681786975162270
def wireWord36 : W := 1477699714072735757
def wireWord37 : W := 599546099798641792
def wireWord38 : W := 3458606166714519538
def wireWord39 : W := 324262314939255954
def wireWord40 : W := 746273726684102656
def wireWord41 : W := 4611686017055260671
def wireWord42 : W := 599546098980654226
def wireWord43 : W := 4287426795847811040
def wireWord44 : W := 4287426495200100124
def wireWord45 : W := 680611992330829824
def wireWord46 : W := 79165072142336
def wireWord47 : W := 1153361326975156224
def wireWord48 : W := 2453371219093225472
def wireWord49 : W := 1234427219242123264
def wireWord50 : W := 272138240
def wireWord51 : W := 2453450383893229568
def wireWord52 : W := 599546100063862784
def wireWord53 : W := 2534437111625416704
def wireWord54 : W := 537362432
def wireWord55 : W := 1153440491509936128
def wireWord56 : W := 599546099798638592
def wireWord57 : W := 599827573954183168
def wireWord58 : W := 2307004231435448320
def wireWord59 : W := 146446152729919488
def wireWord60 : W := 1234145745351802880
def wireWord61 : W := 745913086332895232
def wireWord62 : W := 1153079851696091136
def wireWord63 : W := 360640351207424
def wireWord64 : W := 2388070125091160064

def rootCell0 : S := (1, [wireWord9, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
def r0l0 : S := (0, [wireWord9, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l0Dead : optimized 5 r0l0.1 r0l0.2 = false := by decide +kernel
def r0l1 : S := (1, [wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l1Dead : optimized 5 r0l1.1 r0l1.2 = false := by decide +kernel
def r0l2 : S := (0, [wireWord0, wireWord9, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l2Dead : optimized 5 r0l2.1 r0l2.2 = false := by decide +kernel
def r0l3 : S := (0, [wireWord0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l3Dead : optimized 5 r0l3.1 r0l3.2 = false := by decide +kernel
def r0l4 : S := (0, [0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l4Dead : optimized 5 r0l4.1 r0l4.2 = false := by decide +kernel
def r0l5 : S := (0, [wireWord26, wireWord9, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l5Dead : optimized 5 r0l5.1 r0l5.2 = false := by decide +kernel
def r0l6 : S := (0, [wireWord26, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l6Dead : optimized 5 r0l6.1 r0l6.2 = false := by decide +kernel
def r0l7 : S := (0, [wireWord9, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l7Dead : optimized 5 r0l7.1 r0l7.2 = false := by decide +kernel
def r0l8 : S := (1, [wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l8Dead : optimized 5 r0l8.1 r0l8.2 = false := by decide +kernel
def r0l9 : S := (0, [wireWord1, wireWord9, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l9Dead : optimized 5 r0l9.1 r0l9.2 = false := by decide +kernel
def r0l10 : S := (0, [wireWord1, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l10Dead : optimized 5 r0l10.1 r0l10.2 = false := by decide +kernel
def r0l11 : S := (0, [0, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l11Dead : optimized 5 r0l11.1 r0l11.2 = false := by decide +kernel
def r0l12 : S := (0, [wireWord42, wireWord9, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l12Dead : optimized 5 r0l12.1 r0l12.2 = false := by decide +kernel
def r0l13 : S := (0, [wireWord42, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l13Dead : optimized 5 r0l13.1 r0l13.2 = false := by decide +kernel
def r0l14 : S := (0, [284266705453056, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l14Dead : optimized 5 r0l14.1 r0l14.2 = false := by decide +kernel
def r0l15 : S := (1, [2304681786971983644, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l15Dead : optimized 5 r0l15.1 r0l15.2 = false := by decide +kernel
def r0l16 : S := (0, [2304681786971983644, wireWord9, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l16Dead : optimized 5 r0l16.1 r0l16.2 = false := by decide +kernel
def r0l17 : S := (0, [2304681786971983644, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l17Dead : optimized 5 r0l17.1 r0l17.2 = false := by decide +kernel
def r0l18 : S := (0, [470705675937251328, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l18Dead : optimized 5 r0l18.1 r0l18.2 = false := by decide +kernel
def r0l19 : S := (1, [1833691844329279260, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l19Dead : optimized 5 r0l19.1 r0l19.2 = false := by decide +kernel
def r0l20 : S := (0, [1833691844329279260, wireWord9, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l20Dead : optimized 5 r0l20.1 r0l20.2 = false := by decide +kernel
def r0l21 : S := (0, [1833691844329279260, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l21Dead : optimized 5 r0l21.1 r0l21.2 = false := by decide +kernel
def r0l22 : S := (0, [146370080265994240, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l22Dead : optimized 5 r0l22.1 r0l22.2 = false := by decide +kernel
def r0l23 : S := (1, [3458606166177222624, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l23Dead : optimized 5 r0l23.1 r0l23.2 = false := by decide +kernel
def r0l24 : S := (0, [3458606166177222624, wireWord9, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l24Dead : optimized 5 r0l24.1 r0l24.2 = false := by decide +kernel
def r0l25 : S := (0, [3458606166177222624, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l25Dead : optimized 5 r0l25.1 r0l25.2 = false := by decide +kernel
def r0l26 : S := (0, [324619862376710144, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l26Dead : optimized 5 r0l26.1 r0l26.2 = false := by decide +kernel
def r0l27 : S := (1, [2987616223534518240, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l27Dead : optimized 5 r0l27.1 r0l27.2 = false := by decide +kernel
def r0l28 : S := (0, [2987616223534518240, wireWord9, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l28Dead : optimized 5 r0l28.1 r0l28.2 = false := by decide +kernel
def r0l29 : S := (0, [2987616223534518240, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l29Dead : optimized 5 r0l29.1 r0l29.2 = false := by decide +kernel
def r0l30 : S := (0, [146727627703451648, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l30Dead : optimized 5 r0l30.1 r0l30.2 = false := by decide +kernel
def r0l31 : S := (1, [4611686018410606592, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l31Dead : optimized 5 r0l31.1 r0l31.2 = false := by decide +kernel
def r0l32 : S := (0, [4611686018410606592, wireWord9, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l32Dead : optimized 5 r0l32.1 r0l32.2 = false := by decide +kernel
def r0l33 : S := (0, [4611686018410606592, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l33Dead : optimized 5 r0l33.1 r0l33.2 = false := by decide +kernel
def r0l34 : S := (0, [324262314939252736, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l34Dead : optimized 5 r0l34.1 r0l34.2 = false := by decide +kernel
def r0l35 : S := (1, [4140696075767902208, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l35Dead : optimized 5 r0l35.1 r0l35.2 = false := by decide +kernel
def r0l36 : S := (0, [4140696075767902208, wireWord9, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l36Dead : optimized 5 r0l36.1 r0l36.2 = false := by decide +kernel
def r0l37 : S := (0, [4140696075767902208, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l37Dead : optimized 5 r0l37.1 r0l37.2 = false := by decide +kernel
def r0l38 : S := (0, [wireWord41, wireWord0, wireWord9, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l38Dead : optimized 5 r0l38.1 r0l38.2 = false := by decide +kernel
def r0l39 : S := (0, [wireWord41, wireWord1, wireWord9, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l39Dead : optimized 5 r0l39.1 r0l39.2 = false := by decide +kernel
def r0l40 : S := (0, [wireWord26, wireWord1, wireWord9, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l40Dead : optimized 5 r0l40.1 r0l40.2 = false := by decide +kernel
def r0l41 : S := (0, [wireWord42, wireWord0, wireWord9, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l41Dead : optimized 5 r0l41.1 r0l41.2 = false := by decide +kernel
def r0l42 : S := (0, [wireWord10, wireWord2, wireWord9, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l42Dead : optimized 5 r0l42.1 r0l42.2 = false := by decide +kernel
def r0l43 : S := (0, [wireWord31, wireWord2, wireWord9, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l43Dead : optimized 5 r0l43.1 r0l43.2 = false := by decide +kernel
def r0l44 : S := (0, [wireWord19, wireWord3, wireWord9, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l44Dead : optimized 5 r0l44.1 r0l44.2 = false := by decide +kernel
def r0l45 : S := (0, [wireWord20, wireWord3, wireWord9, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l45Dead : optimized 5 r0l45.1 r0l45.2 = false := by decide +kernel
def r0l46 : S := (0, [wireWord21, wireWord4, wireWord9, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l46Dead : optimized 5 r0l46.1 r0l46.2 = false := by decide +kernel
def r0l47 : S := (0, [wireWord22, wireWord4, wireWord9, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r0l47Dead : optimized 5 r0l47.1 r0l47.2 = false := by decide +kernel
def r0l48 : S := (0, [wireWord40, wireWord2, wireWord9, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l48Dead : optimized 5 r0l48.1 r0l48.2 = false := by decide +kernel
def r0l49 : S := (0, [wireWord11, wireWord2, wireWord9, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l49Dead : optimized 5 r0l49.1 r0l49.2 = false := by decide +kernel
def r0l50 : S := (0, [wireWord5, wireWord2, wireWord9, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l50Dead : optimized 5 r0l50.1 r0l50.2 = false := by decide +kernel
def r0l51 : S := (0, [wireWord7, wireWord2, wireWord9, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r0l51Dead : optimized 5 r0l51.1 r0l51.2 = false := by decide +kernel
def r0l52 : S := (0, [wireWord6, wireWord2, wireWord9, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r0l52Dead : optimized 5 r0l52.1 r0l52.2 = false := by decide +kernel
def r0l53 : S := (0, [wireWord8, wireWord2, wireWord9, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r0l53Dead : optimized 5 r0l53.1 r0l53.2 = false := by decide +kernel
theorem rootCell0Dead : optimized 6 rootCell0.1 rootCell0.2 = false := by
  have kids : nexts (rootCell0.1, rootCell0.2) = [r0l0,r0l1,r0l2,r0l3,r0l4,r0l5,r0l6,r0l7,r0l8,r0l9,r0l10,r0l11,r0l12,r0l13,r0l14,r0l15,r0l16,r0l17,r0l18,r0l19,r0l20,r0l21,r0l22,r0l23,r0l24,r0l25,r0l26,r0l27,r0l28,r0l29,r0l30,r0l31,r0l32,r0l33,r0l34,r0l35,r0l36,r0l37,r0l38,r0l39,r0l40,r0l41,r0l42,r0l43,r0l44,r0l45,r0l46,r0l47,r0l48,r0l49,r0l50,r0l51,r0l52,r0l53] := by decide +kernel
  have stop : (rootCell0.2 == [goal] || rootCell0.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r0l0Dead, r0l1Dead, r0l2Dead, r0l3Dead, r0l4Dead, r0l5Dead, r0l6Dead, r0l7Dead, r0l8Dead, r0l9Dead, r0l10Dead, r0l11Dead, r0l12Dead, r0l13Dead, r0l14Dead, r0l15Dead, r0l16Dead, r0l17Dead, r0l18Dead, r0l19Dead, r0l20Dead, r0l21Dead, r0l22Dead, r0l23Dead, r0l24Dead, r0l25Dead, r0l26Dead, r0l27Dead, r0l28Dead, r0l29Dead, r0l30Dead, r0l31Dead, r0l32Dead, r0l33Dead, r0l34Dead, r0l35Dead, r0l36Dead, r0l37Dead, r0l38Dead, r0l39Dead, r0l40Dead, r0l41Dead, r0l42Dead, r0l43Dead, r0l44Dead, r0l45Dead, r0l46Dead, r0l47Dead, r0l48Dead, r0l49Dead, r0l50Dead, r0l51Dead, r0l52Dead, r0l53Dead]
def rootCell1 : S := (1, [wireWord41, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
def r1l0 : S := (1, [wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l0Dead : optimized 5 r1l0.1 r1l0.2 = false := by decide +kernel
def r1l1 : S := (0, [wireWord0, wireWord41, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l1Dead : optimized 5 r1l1.1 r1l1.2 = false := by decide +kernel
def r1l2 : S := (0, [wireWord0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l2Dead : optimized 5 r1l2.1 r1l2.2 = false := by decide +kernel
def r1l3 : S := (0, [wireWord41, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l3Dead : optimized 5 r1l3.1 r1l3.2 = false := by decide +kernel
def r1l4 : S := (0, [wireWord42, wireWord41, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l4Dead : optimized 5 r1l4.1 r1l4.2 = false := by decide +kernel
def r1l5 : S := (0, [wireWord42, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l5Dead : optimized 5 r1l5.1 r1l5.2 = false := by decide +kernel
def r1l6 : S := (0, [0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l6Dead : optimized 5 r1l6.1 r1l6.2 = false := by decide +kernel
def r1l7 : S := (1, [wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l7Dead : optimized 5 r1l7.1 r1l7.2 = false := by decide +kernel
def r1l8 : S := (0, [wireWord1, wireWord41, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l8Dead : optimized 5 r1l8.1 r1l8.2 = false := by decide +kernel
def r1l9 : S := (0, [wireWord1, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l9Dead : optimized 5 r1l9.1 r1l9.2 = false := by decide +kernel
def r1l10 : S := (0, [wireWord41, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l10Dead : optimized 5 r1l10.1 r1l10.2 = false := by decide +kernel
def r1l11 : S := (0, [wireWord26, wireWord41, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l11Dead : optimized 5 r1l11.1 r1l11.2 = false := by decide +kernel
def r1l12 : S := (0, [wireWord26, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l12Dead : optimized 5 r1l12.1 r1l12.2 = false := by decide +kernel
def r1l13 : S := (0, [0, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l13Dead : optimized 5 r1l13.1 r1l13.2 = false := by decide +kernel
def r1l14 : S := (1, [1833976109948342044, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l14Dead : optimized 5 r1l14.1 r1l14.2 = false := by decide +kernel
def r1l15 : S := (0, [1833976109948342044, wireWord41, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l15Dead : optimized 5 r1l15.1 r1l15.2 = false := by decide +kernel
def r1l16 : S := (0, [1833976109948342044, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l16Dead : optimized 5 r1l16.1 r1l16.2 = false := by decide +kernel
def r1l17 : S := (0, [4611686018141650943, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l17Dead : optimized 5 r1l17.1 r1l17.2 = false := by decide +kernel
def r1l18 : S := (1, [2777709907106918627, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l18Dead : optimized 5 r1l18.1 r1l18.2 = false := by decide +kernel
def r1l19 : S := (0, [2777709907106918627, wireWord41, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l19Dead : optimized 5 r1l19.1 r1l19.2 = false := by decide +kernel
def r1l20 : S := (0, [2777709907106918627, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l20Dead : optimized 5 r1l20.1 r1l20.2 = false := by decide +kernel
def r1l21 : S := (0, [1086390272, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l21Dead : optimized 5 r1l21.1 r1l21.2 = false := by decide +kernel
def r1l22 : S := (1, [3133986302445228000, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l22Dead : optimized 5 r1l22.1 r1l22.2 = false := by decide +kernel
def r1l23 : S := (0, [3133986302445228000, wireWord41, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l23Dead : optimized 5 r1l23.1 r1l23.2 = false := by decide +kernel
def r1l24 : S := (0, [3133986302445228000, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l24Dead : optimized 5 r1l24.1 r1l24.2 = false := by decide +kernel
def r1l25 : S := (0, [4611686018410545151, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l25Dead : optimized 5 r1l25.1 r1l25.2 = false := by decide +kernel
def r1l26 : S := (1, [1477699714610032671, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l26Dead : optimized 5 r1l26.1 r1l26.2 = false := by decide +kernel
def r1l27 : S := (0, [1477699714610032671, wireWord41, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l27Dead : optimized 5 r1l27.1 r1l27.2 = false := by decide +kernel
def r1l28 : S := (0, [1477699714610032671, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l28Dead : optimized 5 r1l28.1 r1l28.2 = false := by decide +kernel
def r1l29 : S := (0, [1355284480, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l29Dead : optimized 5 r1l29.1 r1l29.2 = false := by decide +kernel
def r1l30 : S := (1, [4287423702116003840, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l30Dead : optimized 5 r1l30.1 r1l30.2 = false := by decide +kernel
def r1l31 : S := (0, [4287423702116003840, wireWord41, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l31Dead : optimized 5 r1l31.1 r1l31.2 = false := by decide +kernel
def r1l32 : S := (0, [4287423702116003840, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l32Dead : optimized 5 r1l32.1 r1l32.2 = false := by decide +kernel
def r1l33 : S := (0, [4611686018410610687, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l33Dead : optimized 5 r1l33.1 r1l33.2 = false := by decide +kernel
def r1l34 : S := (1, [324262314939256831, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l34Dead : optimized 5 r1l34.1 r1l34.2 = false := by decide +kernel
def r1l35 : S := (0, [324262314939256831, wireWord41, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l35Dead : optimized 5 r1l35.1 r1l35.2 = false := by decide +kernel
def r1l36 : S := (0, [324262314939256831, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l36Dead : optimized 5 r1l36.1 r1l36.2 = false := by decide +kernel
def r1l37 : S := (0, [1355350016, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l37Dead : optimized 5 r1l37.1 r1l37.2 = false := by decide +kernel
def r1l38 : S := (0, [wireWord9, wireWord0, wireWord41, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l38Dead : optimized 5 r1l38.1 r1l38.2 = false := by decide +kernel
def r1l39 : S := (0, [wireWord9, wireWord1, wireWord41, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l39Dead : optimized 5 r1l39.1 r1l39.2 = false := by decide +kernel
def r1l40 : S := (0, [wireWord26, wireWord0, wireWord41, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l40Dead : optimized 5 r1l40.1 r1l40.2 = false := by decide +kernel
def r1l41 : S := (0, [wireWord42, wireWord1, wireWord41, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r1l41Dead : optimized 5 r1l41.1 r1l41.2 = false := by decide +kernel
def r1l42 : S := (0, [wireWord5, wireWord2, wireWord41, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l42Dead : optimized 5 r1l42.1 r1l42.2 = false := by decide +kernel
def r1l43 : S := (0, [wireWord7, wireWord2, wireWord41, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r1l43Dead : optimized 5 r1l43.1 r1l43.2 = false := by decide +kernel
def r1l44 : S := (0, [wireWord6, wireWord2, wireWord41, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r1l44Dead : optimized 5 r1l44.1 r1l44.2 = false := by decide +kernel
def r1l45 : S := (0, [wireWord8, wireWord2, wireWord41, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r1l45Dead : optimized 5 r1l45.1 r1l45.2 = false := by decide +kernel
theorem rootCell1Dead : optimized 6 rootCell1.1 rootCell1.2 = false := by
  have kids : nexts (rootCell1.1, rootCell1.2) = [r1l0,r1l1,r1l2,r1l3,r1l4,r1l5,r1l6,r1l7,r1l8,r1l9,r1l10,r1l11,r1l12,r1l13,r1l14,r1l15,r1l16,r1l17,r1l18,r1l19,r1l20,r1l21,r1l22,r1l23,r1l24,r1l25,r1l26,r1l27,r1l28,r1l29,r1l30,r1l31,r1l32,r1l33,r1l34,r1l35,r1l36,r1l37,r1l38,r1l39,r1l40,r1l41,r1l42,r1l43,r1l44,r1l45] := by decide +kernel
  have stop : (rootCell1.2 == [goal] || rootCell1.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r1l0Dead, r1l1Dead, r1l2Dead, r1l3Dead, r1l4Dead, r1l5Dead, r1l6Dead, r1l7Dead, r1l8Dead, r1l9Dead, r1l10Dead, r1l11Dead, r1l12Dead, r1l13Dead, r1l14Dead, r1l15Dead, r1l16Dead, r1l17Dead, r1l18Dead, r1l19Dead, r1l20Dead, r1l21Dead, r1l22Dead, r1l23Dead, r1l24Dead, r1l25Dead, r1l26Dead, r1l27Dead, r1l28Dead, r1l29Dead, r1l30Dead, r1l31Dead, r1l32Dead, r1l33Dead, r1l34Dead, r1l35Dead, r1l36Dead, r1l37Dead, r1l38Dead, r1l39Dead, r1l40Dead, r1l41Dead, r1l42Dead, r1l43Dead, r1l44Dead, r1l45Dead]
def rootCell2 : S := (1, [wireWord26, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
def r2l0 : S := (0, [wireWord26, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l0Dead : optimized 5 r2l0.1 r2l0.2 = false := by decide +kernel
def r2l1 : S := (1, [wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l1Dead : optimized 5 r2l1.1 r2l1.2 = false := by decide +kernel
def r2l2 : S := (0, [wireWord0, wireWord26, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l2Dead : optimized 5 r2l2.1 r2l2.2 = false := by decide +kernel
def r2l3 : S := (0, [wireWord0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l3Dead : optimized 5 r2l3.1 r2l3.2 = false := by decide +kernel
def r2l4 : S := (0, [0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l4Dead : optimized 5 r2l4.1 r2l4.2 = false := by decide +kernel
def r2l5 : S := (0, [wireWord9, wireWord26, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l5Dead : optimized 5 r2l5.1 r2l5.2 = false := by decide +kernel
def r2l6 : S := (0, [wireWord9, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l6Dead : optimized 5 r2l6.1 r2l6.2 = false := by decide +kernel
def r2l7 : S := (0, [0, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l7Dead : optimized 5 r2l7.1 r2l7.2 = false := by decide +kernel
def r2l8 : S := (0, [wireWord41, wireWord26, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l8Dead : optimized 5 r2l8.1 r2l8.2 = false := by decide +kernel
def r2l9 : S := (0, [wireWord41, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l9Dead : optimized 5 r2l9.1 r2l9.2 = false := by decide +kernel
def r2l10 : S := (0, [wireWord26, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l10Dead : optimized 5 r2l10.1 r2l10.2 = false := by decide +kernel
def r2l11 : S := (1, [wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l11Dead : optimized 5 r2l11.1 r2l11.2 = false := by decide +kernel
def r2l12 : S := (0, [wireWord1, wireWord26, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l12Dead : optimized 5 r2l12.1 r2l12.2 = false := by decide +kernel
def r2l13 : S := (0, [wireWord1, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l13Dead : optimized 5 r2l13.1 r2l13.2 = false := by decide +kernel
def r2l14 : S := (0, [1234145744265413388, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l14Dead : optimized 5 r2l14.1 r2l14.2 = false := by decide +kernel
def r2l15 : S := (0, [4140980342201220989, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l15Dead : optimized 5 r2l15.1 r2l15.2 = false := by decide +kernel
def r2l16 : S := (0, [2307004231166488673, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l16Dead : optimized 5 r2l16.1 r2l16.2 = false := by decide +kernel
def r2l17 : S := (0, [599830366769318928, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l17Dead : optimized 5 r2l17.1 r2l17.2 = false := by decide +kernel
def r2l18 : S := (0, [2388070123735876448, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l18Dead : optimized 5 r2l18.1 r2l18.2 = false := by decide +kernel
def r2l19 : S := (0, [4287066155496538093, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l19Dead : optimized 5 r2l19.1 r2l19.2 = false := by decide +kernel
def r2l20 : S := (0, [1153079851696025613, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l20Dead : optimized 5 r2l20.1 r2l20.2 = false := by decide +kernel
def r2l21 : S := (0, [745916180064636032, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l21Dead : optimized 5 r2l21.1 r2l21.2 = false := by decide +kernel
def r2l22 : S := (0, [3541149975431901184, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l22Dead : optimized 5 r2l22.1 r2l22.2 = false := by decide +kernel
def r2l23 : S := (0, [4287423703471354733, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l23Dead : optimized 5 r2l23.1 r2l23.2 = false := by decide +kernel
def r2l24 : S := (0, [877, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l24Dead : optimized 5 r2l24.1 r2l24.2 = false := by decide +kernel
def r2l25 : S := (0, [746273728039452672, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l25Dead : optimized 5 r2l25.1 r2l25.2 = false := by decide +kernel
def r2l26 : S := (0, [wireWord9, wireWord1, wireWord26, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l26Dead : optimized 5 r2l26.1 r2l26.2 = false := by decide +kernel
def r2l27 : S := (0, [wireWord41, wireWord0, wireWord26, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l27Dead : optimized 5 r2l27.1 r2l27.2 = false := by decide +kernel
def r2l28 : S := (0, [wireWord42, wireWord0, wireWord26, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l28Dead : optimized 5 r2l28.1 r2l28.2 = false := by decide +kernel
def r2l29 : S := (0, [wireWord42, wireWord1, wireWord26, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l29Dead : optimized 5 r2l29.1 r2l29.2 = false := by decide +kernel
def r2l30 : S := (0, [wireWord19, wireWord3, wireWord26, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l30Dead : optimized 5 r2l30.1 r2l30.2 = false := by decide +kernel
def r2l31 : S := (0, [wireWord20, wireWord3, wireWord26, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l31Dead : optimized 5 r2l31.1 r2l31.2 = false := by decide +kernel
def r2l32 : S := (0, [wireWord21, wireWord4, wireWord26, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l32Dead : optimized 5 r2l32.1 r2l32.2 = false := by decide +kernel
def r2l33 : S := (0, [wireWord22, wireWord4, wireWord26, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r2l33Dead : optimized 5 r2l33.1 r2l33.2 = false := by decide +kernel
def r2l34 : S := (0, [wireWord40, wireWord2, wireWord26, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l34Dead : optimized 5 r2l34.1 r2l34.2 = false := by decide +kernel
def r2l35 : S := (0, [wireWord11, wireWord2, wireWord26, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l35Dead : optimized 5 r2l35.1 r2l35.2 = false := by decide +kernel
def r2l36 : S := (0, [wireWord5, wireWord2, wireWord26, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l36Dead : optimized 5 r2l36.1 r2l36.2 = false := by decide +kernel
def r2l37 : S := (0, [wireWord7, wireWord2, wireWord26, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r2l37Dead : optimized 5 r2l37.1 r2l37.2 = false := by decide +kernel
def r2l38 : S := (0, [wireWord6, wireWord2, wireWord26, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r2l38Dead : optimized 5 r2l38.1 r2l38.2 = false := by decide +kernel
def r2l39 : S := (0, [wireWord8, wireWord2, wireWord26, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r2l39Dead : optimized 5 r2l39.1 r2l39.2 = false := by decide +kernel
theorem rootCell2Dead : optimized 6 rootCell2.1 rootCell2.2 = false := by
  have kids : nexts (rootCell2.1, rootCell2.2) = [r2l0,r2l1,r2l2,r2l3,r2l4,r2l5,r2l6,r2l7,r2l8,r2l9,r2l10,r2l11,r2l12,r2l13,r2l14,r2l15,r2l16,r2l17,r2l18,r2l19,r2l20,r2l21,r2l22,r2l23,r2l24,r2l25,r2l26,r2l27,r2l28,r2l29,r2l30,r2l31,r2l32,r2l33,r2l34,r2l35,r2l36,r2l37,r2l38,r2l39] := by decide +kernel
  have stop : (rootCell2.2 == [goal] || rootCell2.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r2l0Dead, r2l1Dead, r2l2Dead, r2l3Dead, r2l4Dead, r2l5Dead, r2l6Dead, r2l7Dead, r2l8Dead, r2l9Dead, r2l10Dead, r2l11Dead, r2l12Dead, r2l13Dead, r2l14Dead, r2l15Dead, r2l16Dead, r2l17Dead, r2l18Dead, r2l19Dead, r2l20Dead, r2l21Dead, r2l22Dead, r2l23Dead, r2l24Dead, r2l25Dead, r2l26Dead, r2l27Dead, r2l28Dead, r2l29Dead, r2l30Dead, r2l31Dead, r2l32Dead, r2l33Dead, r2l34Dead, r2l35Dead, r2l36Dead, r2l37Dead, r2l38Dead, r2l39Dead]
def rootCell3 : S := (1, [wireWord42, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
def r3l0 : S := (0, [0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l0Dead : optimized 5 r3l0.1 r3l0.2 = false := by decide +kernel
def r3l1 : S := (0, [wireWord41, wireWord42, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l1Dead : optimized 5 r3l1.1 r3l1.2 = false := by decide +kernel
def r3l2 : S := (0, [wireWord41, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l2Dead : optimized 5 r3l2.1 r3l2.2 = false := by decide +kernel
def r3l3 : S := (0, [wireWord42, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l3Dead : optimized 5 r3l3.1 r3l3.2 = false := by decide +kernel
def r3l4 : S := (1, [wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l4Dead : optimized 5 r3l4.1 r3l4.2 = false := by decide +kernel
def r3l5 : S := (0, [wireWord0, wireWord42, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l5Dead : optimized 5 r3l5.1 r3l5.2 = false := by decide +kernel
def r3l6 : S := (0, [wireWord0, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l6Dead : optimized 5 r3l6.1 r3l6.2 = false := by decide +kernel
def r3l7 : S := (0, [wireWord42, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l7Dead : optimized 5 r3l7.1 r3l7.2 = false := by decide +kernel
def r3l8 : S := (1, [wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l8Dead : optimized 5 r3l8.1 r3l8.2 = false := by decide +kernel
def r3l9 : S := (0, [wireWord1, wireWord42, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l9Dead : optimized 5 r3l9.1 r3l9.2 = false := by decide +kernel
def r3l10 : S := (0, [wireWord1, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l10Dead : optimized 5 r3l10.1 r3l10.2 = false := by decide +kernel
def r3l11 : S := (0, [0, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l11Dead : optimized 5 r3l11.1 r3l11.2 = false := by decide +kernel
def r3l12 : S := (0, [wireWord9, wireWord42, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l12Dead : optimized 5 r3l12.1 r3l12.2 = false := by decide +kernel
def r3l13 : S := (0, [wireWord9, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l13Dead : optimized 5 r3l13.1 r3l13.2 = false := by decide +kernel
def r3l14 : S := (0, [599546098977475600, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l14Dead : optimized 5 r3l14.1 r3l14.2 = false := by decide +kernel
def r3l15 : S := (0, [1833976111037910942, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l15Dead : optimized 5 r3l15.1 r3l15.2 = false := by decide +kernel
def r3l16 : S := (0, [3178626, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l16Dead : optimized 5 r3l16.1 r3l16.2 = false := by decide +kernel
def r3l17 : S := (0, [1234430012057256716, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l17Dead : optimized 5 r3l17.1 r3l17.2 = false := by decide +kernel
def r3l18 : S := (0, [599546098443357312, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l18Dead : optimized 5 r3l18.1 r3l18.2 = false := by decide +kernel
def r3l19 : S := (0, [3133986304337809394, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l19Dead : optimized 5 r3l19.1 r3l19.2 = false := by decide +kernel
def r3l20 : S := (0, [537296914, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l20Dead : optimized 5 r3l20.1 r3l20.2 = false := by decide +kernel
def r3l21 : S := (0, [2534440205357155168, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l21Dead : optimized 5 r3l21.1 r3l21.2 = false := by decide +kernel
def r3l22 : S := (0, [599546098980651008, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l22Dead : optimized 5 r3l22.1 r3l22.2 = false := by decide +kernel
def r3l23 : S := (0, [4287423703471357074, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l23Dead : optimized 5 r3l23.1 r3l23.2 = false := by decide +kernel
def r3l24 : S := (0, [3218, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l24Dead : optimized 5 r3l24.1 r3l24.2 = false := by decide +kernel
def r3l25 : S := (0, [3687877604490702848, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l25Dead : optimized 5 r3l25.1 r3l25.2 = false := by decide +kernel
def r3l26 : S := (0, [wireWord9, wireWord0, wireWord42, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l26Dead : optimized 5 r3l26.1 r3l26.2 = false := by decide +kernel
def r3l27 : S := (0, [wireWord41, wireWord1, wireWord42, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l27Dead : optimized 5 r3l27.1 r3l27.2 = false := by decide +kernel
def r3l28 : S := (0, [wireWord26, wireWord0, wireWord42, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l28Dead : optimized 5 r3l28.1 r3l28.2 = false := by decide +kernel
def r3l29 : S := (0, [wireWord26, wireWord1, wireWord42, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r3l29Dead : optimized 5 r3l29.1 r3l29.2 = false := by decide +kernel
def r3l30 : S := (0, [wireWord10, wireWord2, wireWord42, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l30Dead : optimized 5 r3l30.1 r3l30.2 = false := by decide +kernel
def r3l31 : S := (0, [wireWord31, wireWord2, wireWord42, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l31Dead : optimized 5 r3l31.1 r3l31.2 = false := by decide +kernel
def r3l32 : S := (0, [wireWord5, wireWord2, wireWord42, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l32Dead : optimized 5 r3l32.1 r3l32.2 = false := by decide +kernel
def r3l33 : S := (0, [wireWord7, wireWord2, wireWord42, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r3l33Dead : optimized 5 r3l33.1 r3l33.2 = false := by decide +kernel
def r3l34 : S := (0, [wireWord6, wireWord2, wireWord42, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r3l34Dead : optimized 5 r3l34.1 r3l34.2 = false := by decide +kernel
def r3l35 : S := (0, [wireWord8, wireWord2, wireWord42, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r3l35Dead : optimized 5 r3l35.1 r3l35.2 = false := by decide +kernel
theorem rootCell3Dead : optimized 6 rootCell3.1 rootCell3.2 = false := by
  have kids : nexts (rootCell3.1, rootCell3.2) = [r3l0,r3l1,r3l2,r3l3,r3l4,r3l5,r3l6,r3l7,r3l8,r3l9,r3l10,r3l11,r3l12,r3l13,r3l14,r3l15,r3l16,r3l17,r3l18,r3l19,r3l20,r3l21,r3l22,r3l23,r3l24,r3l25,r3l26,r3l27,r3l28,r3l29,r3l30,r3l31,r3l32,r3l33,r3l34,r3l35] := by decide +kernel
  have stop : (rootCell3.2 == [goal] || rootCell3.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r3l0Dead, r3l1Dead, r3l2Dead, r3l3Dead, r3l4Dead, r3l5Dead, r3l6Dead, r3l7Dead, r3l8Dead, r3l9Dead, r3l10Dead, r3l11Dead, r3l12Dead, r3l13Dead, r3l14Dead, r3l15Dead, r3l16Dead, r3l17Dead, r3l18Dead, r3l19Dead, r3l20Dead, r3l21Dead, r3l22Dead, r3l23Dead, r3l24Dead, r3l25Dead, r3l26Dead, r3l27Dead, r3l28Dead, r3l29Dead, r3l30Dead, r3l31Dead, r3l32Dead, r3l33Dead, r3l34Dead, r3l35Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell4 : S := (1, [wireWord32, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
def r4l0 : S := (0, [wireWord32, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l0Dead : optimized 5 r4l0.1 r4l0.2 = false := by decide +kernel
def r4l1 : S := (1, [wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l1Dead : optimized 5 r4l1.1 r4l1.2 = false := by decide +kernel
def r4l2 : S := (0, [wireWord0, wireWord32, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l2Dead : optimized 5 r4l2.1 r4l2.2 = false := by decide +kernel
def r4l3 : S := (0, [wireWord0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l3Dead : optimized 5 r4l3.1 r4l3.2 = false := by decide +kernel
def r4l4 : S := (0, [0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l4Dead : optimized 5 r4l4.1 r4l4.2 = false := by decide +kernel
def r4l5 : S := (0, [wireWord33, wireWord32, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l5Dead : optimized 5 r4l5.1 r4l5.2 = false := by decide +kernel
def r4l6 : S := (0, [wireWord33, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l6Dead : optimized 5 r4l6.1 r4l6.2 = false := by decide +kernel
def r4l7 : S := (0, [wireWord32, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l7Dead : optimized 5 r4l7.1 r4l7.2 = false := by decide +kernel
def r4l8 : S := (1, [wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l8Dead : optimized 5 r4l8.1 r4l8.2 = false := by decide +kernel
def r4l9 : S := (0, [wireWord3, wireWord32, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l9Dead : optimized 5 r4l9.1 r4l9.2 = false := by decide +kernel
def r4l10 : S := (0, [wireWord3, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l10Dead : optimized 5 r4l10.1 r4l10.2 = false := by decide +kernel
def r4l11 : S := (0, [0, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l11Dead : optimized 5 r4l11.1 r4l11.2 = false := by decide +kernel
def r4l12 : S := (0, [wireWord34, wireWord32, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l12Dead : optimized 5 r4l12.1 r4l12.2 = false := by decide +kernel
def r4l13 : S := (0, [wireWord34, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l13Dead : optimized 5 r4l13.1 r4l13.2 = false := by decide +kernel
def r4l14 : S := (0, [284266705453056, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l14Dead : optimized 5 r4l14.1 r4l14.2 = false := by decide +kernel
def r4l15 : S := (0, [2304681785888771998, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l15Dead : optimized 5 r4l15.1 r4l15.2 = false := by decide +kernel
def r4l16 : S := (0, [1234145744265413388, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l16Dead : optimized 5 r4l16.1 r4l16.2 = false := by decide +kernel
def r4l17 : S := (0, [1070251774917905554, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l17Dead : optimized 5 r4l17.1 r4l17.2 = false := by decide +kernel
def r4l18 : S := (0, [81068641583366912, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l18Dead : optimized 5 r4l18.1 r4l18.2 = false := by decide +kernel
def r4l19 : S := (1, [4287347673188012012, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l19Dead : optimized 5 r4l19.1 r4l19.2 = false := by decide +kernel
def r4l20 : S := (0, [4287347673188012012, wireWord32, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l20Dead : optimized 5 r4l20.1 r4l20.2 = false := by decide +kernel
def r4l21 : S := (0, [4287347673188012012, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l21Dead : optimized 5 r4l21.1 r4l21.2 = false := by decide +kernel
def r4l22 : S := (0, [1153361369387499532, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l22Dead : optimized 5 r4l22.1 r4l22.2 = false := by decide +kernel
def r4l23 : S := (1, [3052917662217145568, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l23Dead : optimized 5 r4l23.1 r4l23.2 = false := by decide +kernel
def r4l24 : S := (0, [3052917662217145568, wireWord32, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l24Dead : optimized 5 r4l24.1 r4l24.2 = false := by decide +kernel
def r4l25 : S := (0, [3052917662217145568, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l25Dead : optimized 5 r4l25.1 r4l25.2 = false := by decide +kernel
def r4l26 : S := (0, [wireWord49, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r4l26Dead : optimized 5 r4l26.1 r4l26.2 = false := by decide +kernel
def r4l27 : S := (0, [4287426495200097036, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r4l27Dead : optimized 5 r4l27.1 r4l27.2 = false := by decide +kernel
def r4l28 : S := (0, [2791728743180, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r4l28Dead : optimized 5 r4l28.1 r4l28.2 = false := by decide +kernel
def r4l29 : S := (0, [3052996484229230592, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r4l29Dead : optimized 5 r4l29.1 r4l29.2 = false := by decide +kernel
def r4l30 : S := (0, [wireWord23, wireWord0, wireWord32, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l30Dead : optimized 5 r4l30.1 r4l30.2 = false := by decide +kernel
def r4l31 : S := (0, [wireWord23, wireWord3, wireWord32, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l31Dead : optimized 5 r4l31.1 r4l31.2 = false := by decide +kernel
def r4l32 : S := (0, [wireWord33, wireWord3, wireWord32, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l32Dead : optimized 5 r4l32.1 r4l32.2 = false := by decide +kernel
def r4l33 : S := (0, [wireWord34, wireWord0, wireWord32, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l33Dead : optimized 5 r4l33.1 r4l33.2 = false := by decide +kernel
def r4l34 : S := (0, [wireWord19, wireWord1, wireWord32, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l34Dead : optimized 5 r4l34.1 r4l34.2 = false := by decide +kernel
def r4l35 : S := (0, [wireWord27, wireWord1, wireWord32, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l35Dead : optimized 5 r4l35.1 r4l35.2 = false := by decide +kernel
def r4l36 : S := (0, [wireWord15, wireWord4, wireWord32, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l36Dead : optimized 5 r4l36.1 r4l36.2 = false := by decide +kernel
def r4l37 : S := (0, [wireWord16, wireWord4, wireWord32, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r4l37Dead : optimized 5 r4l37.1 r4l37.2 = false := by decide +kernel
def r4l38 : S := (0, [wireWord5, wireWord2, wireWord32, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r4l38Dead : optimized 5 r4l38.1 r4l38.2 = false := by decide +kernel
def r4l39 : S := (0, [wireWord7, wireWord2, wireWord32, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r4l39Dead : optimized 5 r4l39.1 r4l39.2 = false := by decide +kernel
def r4l40 : S := (0, [wireWord6, wireWord2, wireWord32, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r4l40Dead : optimized 5 r4l40.1 r4l40.2 = false := by decide +kernel
def r4l41 : S := (0, [wireWord8, wireWord2, wireWord32, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r4l41Dead : optimized 5 r4l41.1 r4l41.2 = false := by decide +kernel
theorem rootCell4Dead : optimized 6 rootCell4.1 rootCell4.2 = false := by
  have kids : nexts (rootCell4.1, rootCell4.2) = [r4l0,r4l1,r4l2,r4l3,r4l4,r4l5,r4l6,r4l7,r4l8,r4l9,r4l10,r4l11,r4l12,r4l13,r4l14,r4l15,r4l16,r4l17,r4l18,r4l19,r4l20,r4l21,r4l22,r4l23,r4l24,r4l25,r4l26,r4l27,r4l28,r4l29,r4l30,r4l31,r4l32,r4l33,r4l34,r4l35,r4l36,r4l37,r4l38,r4l39,r4l40,r4l41] := by decide +kernel
  have stop : (rootCell4.2 == [goal] || rootCell4.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r4l0Dead, r4l1Dead, r4l2Dead, r4l3Dead, r4l4Dead, r4l5Dead, r4l6Dead, r4l7Dead, r4l8Dead, r4l9Dead, r4l10Dead, r4l11Dead, r4l12Dead, r4l13Dead, r4l14Dead, r4l15Dead, r4l16Dead, r4l17Dead, r4l18Dead, r4l19Dead, r4l20Dead, r4l21Dead, r4l22Dead, r4l23Dead, r4l24Dead, r4l25Dead, r4l26Dead, r4l27Dead, r4l28Dead, r4l29Dead, r4l30Dead, r4l31Dead, r4l32Dead, r4l33Dead, r4l34Dead, r4l35Dead, r4l36Dead, r4l37Dead, r4l38Dead, r4l39Dead, r4l40Dead, r4l41Dead]
def rootCell5 : S := (1, [wireWord23, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
def r5l0 : S := (1, [wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l0Dead : optimized 5 r5l0.1 r5l0.2 = false := by decide +kernel
def r5l1 : S := (0, [wireWord0, wireWord23, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l1Dead : optimized 5 r5l1.1 r5l1.2 = false := by decide +kernel
def r5l2 : S := (0, [wireWord0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l2Dead : optimized 5 r5l2.1 r5l2.2 = false := by decide +kernel
def r5l3 : S := (0, [wireWord23, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l3Dead : optimized 5 r5l3.1 r5l3.2 = false := by decide +kernel
def r5l4 : S := (0, [wireWord34, wireWord23, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l4Dead : optimized 5 r5l4.1 r5l4.2 = false := by decide +kernel
def r5l5 : S := (0, [wireWord34, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l5Dead : optimized 5 r5l5.1 r5l5.2 = false := by decide +kernel
def r5l6 : S := (0, [0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l6Dead : optimized 5 r5l6.1 r5l6.2 = false := by decide +kernel
def r5l7 : S := (1, [wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l7Dead : optimized 5 r5l7.1 r5l7.2 = false := by decide +kernel
def r5l8 : S := (0, [wireWord3, wireWord23, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l8Dead : optimized 5 r5l8.1 r5l8.2 = false := by decide +kernel
def r5l9 : S := (0, [wireWord3, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l9Dead : optimized 5 r5l9.1 r5l9.2 = false := by decide +kernel
def r5l10 : S := (0, [wireWord23, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l10Dead : optimized 5 r5l10.1 r5l10.2 = false := by decide +kernel
def r5l11 : S := (0, [wireWord33, wireWord23, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l11Dead : optimized 5 r5l11.1 r5l11.2 = false := by decide +kernel
def r5l12 : S := (0, [wireWord33, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l12Dead : optimized 5 r5l12.1 r5l12.2 = false := by decide +kernel
def r5l13 : S := (0, [0, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l13Dead : optimized 5 r5l13.1 r5l13.2 = false := by decide +kernel
def r5l14 : S := (1, [1070536041620179984, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l14Dead : optimized 5 r5l14.1 r5l14.2 = false := by decide +kernel
def r5l15 : S := (0, [1070536041620179984, wireWord23, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l15Dead : optimized 5 r5l15.1 r5l15.2 = false := by decide +kernel
def r5l16 : S := (0, [1070536041620179984, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l16Dead : optimized 5 r5l16.1 r5l16.2 = false := by decide +kernel
def r5l17 : S := (0, [4611686018141650943, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l17Dead : optimized 5 r5l17.1 r5l17.2 = false := by decide +kernel
def r5l18 : S := (1, [3541149976518292333, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l18Dead : optimized 5 r5l18.1 r5l18.2 = false := by decide +kernel
def r5l19 : S := (0, [3541149976518292333, wireWord23, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l19Dead : optimized 5 r5l19.1 r5l19.2 = false := by decide +kernel
def r5l20 : S := (0, [3541149976518292333, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l20Dead : optimized 5 r5l20.1 r5l20.2 = false := by decide +kernel
def r5l21 : S := (0, [3178626, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l21Dead : optimized 5 r5l21.1 r5l21.2 = false := by decide +kernel
def r5l22 : S := (1, [3133986303528406880, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l22Dead : optimized 5 r5l22.1 r5l22.2 = false := by decide +kernel
def r5l23 : S := (0, [3133986303528406880, wireWord23, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l23Dead : optimized 5 r5l23.1 r5l23.2 = false := by decide +kernel
def r5l24 : S := (0, [3133986303528406880, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l24Dead : optimized 5 r5l24.1 r5l24.2 = false := by decide +kernel
def r5l25 : S := (0, [4611686018410577917, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l25Dead : optimized 5 r5l25.1 r5l25.2 = false := by decide +kernel
def r5l26 : S := (1, [1477699714610065437, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l26Dead : optimized 5 r5l26.1 r5l26.2 = false := by decide +kernel
def r5l27 : S := (0, [1477699714610065437, wireWord23, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l27Dead : optimized 5 r5l27.1 r5l27.2 = false := by decide +kernel
def r5l28 : S := (0, [1477699714610065437, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l28Dead : optimized 5 r5l28.1 r5l28.2 = false := by decide +kernel
def r5l29 : S := (0, [272105600, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l29Dead : optimized 5 r5l29.1 r5l29.2 = false := by decide +kernel
def r5l30 : S := (1, [4287423703199215616, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l30Dead : optimized 5 r5l30.1 r5l30.2 = false := by decide +kernel
def r5l31 : S := (0, [4287423703199215616, wireWord23, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l31Dead : optimized 5 r5l31.1 r5l31.2 = false := by decide +kernel
def r5l32 : S := (0, [4287423703199215616, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l32Dead : optimized 5 r5l32.1 r5l32.2 = false := by decide +kernel
def r5l33 : S := (0, [4611686018410610557, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l33Dead : optimized 5 r5l33.1 r5l33.2 = false := by decide +kernel
def r5l34 : S := (1, [324262314939256701, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l34Dead : optimized 5 r5l34.1 r5l34.2 = false := by decide +kernel
def r5l35 : S := (0, [324262314939256701, wireWord23, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l35Dead : optimized 5 r5l35.1 r5l35.2 = false := by decide +kernel
def r5l36 : S := (0, [324262314939256701, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l36Dead : optimized 5 r5l36.1 r5l36.2 = false := by decide +kernel
def r5l37 : S := (0, [wireWord50, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l37Dead : optimized 5 r5l37.1 r5l37.2 = false := by decide +kernel
def r5l38 : S := (0, [wireWord32, wireWord0, wireWord23, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l38Dead : optimized 5 r5l38.1 r5l38.2 = false := by decide +kernel
def r5l39 : S := (0, [wireWord32, wireWord3, wireWord23, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l39Dead : optimized 5 r5l39.1 r5l39.2 = false := by decide +kernel
def r5l40 : S := (0, [wireWord33, wireWord0, wireWord23, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l40Dead : optimized 5 r5l40.1 r5l40.2 = false := by decide +kernel
def r5l41 : S := (0, [wireWord34, wireWord3, wireWord23, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l41Dead : optimized 5 r5l41.1 r5l41.2 = false := by decide +kernel
def r5l42 : S := (0, [wireWord35, wireWord1, wireWord23, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l42Dead : optimized 5 r5l42.1 r5l42.2 = false := by decide +kernel
def r5l43 : S := (0, [wireWord20, wireWord1, wireWord23, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l43Dead : optimized 5 r5l43.1 r5l43.2 = false := by decide +kernel
def r5l44 : S := (0, [wireWord14, wireWord4, wireWord23, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l44Dead : optimized 5 r5l44.1 r5l44.2 = false := by decide +kernel
def r5l45 : S := (0, [wireWord17, wireWord4, wireWord23, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r5l45Dead : optimized 5 r5l45.1 r5l45.2 = false := by decide +kernel
def r5l46 : S := (0, [wireWord5, wireWord2, wireWord23, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l46Dead : optimized 5 r5l46.1 r5l46.2 = false := by decide +kernel
def r5l47 : S := (0, [wireWord7, wireWord2, wireWord23, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r5l47Dead : optimized 5 r5l47.1 r5l47.2 = false := by decide +kernel
def r5l48 : S := (0, [wireWord6, wireWord2, wireWord23, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r5l48Dead : optimized 5 r5l48.1 r5l48.2 = false := by decide +kernel
def r5l49 : S := (0, [wireWord8, wireWord2, wireWord23, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r5l49Dead : optimized 5 r5l49.1 r5l49.2 = false := by decide +kernel
theorem rootCell5Dead : optimized 6 rootCell5.1 rootCell5.2 = false := by
  have kids : nexts (rootCell5.1, rootCell5.2) = [r5l0,r5l1,r5l2,r5l3,r5l4,r5l5,r5l6,r5l7,r5l8,r5l9,r5l10,r5l11,r5l12,r5l13,r5l14,r5l15,r5l16,r5l17,r5l18,r5l19,r5l20,r5l21,r5l22,r5l23,r5l24,r5l25,r5l26,r5l27,r5l28,r5l29,r5l30,r5l31,r5l32,r5l33,r5l34,r5l35,r5l36,r5l37,r5l38,r5l39,r5l40,r5l41,r5l42,r5l43,r5l44,r5l45,r5l46,r5l47,r5l48,r5l49] := by decide +kernel
  have stop : (rootCell5.2 == [goal] || rootCell5.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r5l0Dead, r5l1Dead, r5l2Dead, r5l3Dead, r5l4Dead, r5l5Dead, r5l6Dead, r5l7Dead, r5l8Dead, r5l9Dead, r5l10Dead, r5l11Dead, r5l12Dead, r5l13Dead, r5l14Dead, r5l15Dead, r5l16Dead, r5l17Dead, r5l18Dead, r5l19Dead, r5l20Dead, r5l21Dead, r5l22Dead, r5l23Dead, r5l24Dead, r5l25Dead, r5l26Dead, r5l27Dead, r5l28Dead, r5l29Dead, r5l30Dead, r5l31Dead, r5l32Dead, r5l33Dead, r5l34Dead, r5l35Dead, r5l36Dead, r5l37Dead, r5l38Dead, r5l39Dead, r5l40Dead, r5l41Dead, r5l42Dead, r5l43Dead, r5l44Dead, r5l45Dead, r5l46Dead, r5l47Dead, r5l48Dead, r5l49Dead]
def rootCell6 : S := (1, [wireWord33, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
def r6l0 : S := (0, [wireWord33, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l0Dead : optimized 5 r6l0.1 r6l0.2 = false := by decide +kernel
def r6l1 : S := (1, [wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l1Dead : optimized 5 r6l1.1 r6l1.2 = false := by decide +kernel
def r6l2 : S := (0, [wireWord0, wireWord33, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l2Dead : optimized 5 r6l2.1 r6l2.2 = false := by decide +kernel
def r6l3 : S := (0, [wireWord0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l3Dead : optimized 5 r6l3.1 r6l3.2 = false := by decide +kernel
def r6l4 : S := (0, [0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l4Dead : optimized 5 r6l4.1 r6l4.2 = false := by decide +kernel
def r6l5 : S := (0, [wireWord32, wireWord33, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l5Dead : optimized 5 r6l5.1 r6l5.2 = false := by decide +kernel
def r6l6 : S := (0, [wireWord32, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l6Dead : optimized 5 r6l6.1 r6l6.2 = false := by decide +kernel
def r6l7 : S := (0, [0, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l7Dead : optimized 5 r6l7.1 r6l7.2 = false := by decide +kernel
def r6l8 : S := (0, [wireWord23, wireWord33, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l8Dead : optimized 5 r6l8.1 r6l8.2 = false := by decide +kernel
def r6l9 : S := (0, [wireWord23, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l9Dead : optimized 5 r6l9.1 r6l9.2 = false := by decide +kernel
def r6l10 : S := (0, [wireWord33, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l10Dead : optimized 5 r6l10.1 r6l10.2 = false := by decide +kernel
def r6l11 : S := (1, [wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l11Dead : optimized 5 r6l11.1 r6l11.2 = false := by decide +kernel
def r6l12 : S := (0, [wireWord3, wireWord33, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l12Dead : optimized 5 r6l12.1 r6l12.2 = false := by decide +kernel
def r6l13 : S := (0, [wireWord3, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l13Dead : optimized 5 r6l13.1 r6l13.2 = false := by decide +kernel
def r6l14 : S := (0, [470705675937251328, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l14Dead : optimized 5 r6l14.1 r6l14.2 = false := by decide +kernel
def r6l15 : S := (0, [3377540272789847283, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l15Dead : optimized 5 r6l15.1 r6l15.2 = false := by decide +kernel
def r6l16 : S := (0, [2307004231166488673, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l16Dead : optimized 5 r6l16.1 r6l16.2 = false := by decide +kernel
def r6l17 : S := (0, [599830365686107282, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l17Dead : optimized 5 r6l17.1 r6l17.2 = false := by decide +kernel
def r6l18 : S := (0, [2453371562418503776, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l18Dead : optimized 5 r6l18.1 r6l18.2 = false := by decide +kernel
def r6l19 : S := (0, [3458324648485748705, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l19Dead : optimized 5 r6l19.1 r6l19.2 = false := by decide +kernel
def r6l20 : S := (0, [324338344685236225, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l20Dead : optimized 5 r6l20.1 r6l20.2 = false := by decide +kernel
def r6l21 : S := (0, [680614741382008704, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l21Dead : optimized 5 r6l21.1 r6l21.2 = false := by decide +kernel
def r6l22 : S := (0, [wireWord51, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r6l22Dead : optimized 5 r6l22.1 r6l22.2 = false := by decide +kernel
def r6l23 : S := (0, [4611683226681864289, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r6l23Dead : optimized 5 r6l23.1 r6l23.2 = false := by decide +kernel
def r6l24 : S := (0, [324259523210510433, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r6l24Dead : optimized 5 r6l24.1 r6l24.2 = false := by decide +kernel
def r6l25 : S := (0, [1833973319578124288, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r6l25Dead : optimized 5 r6l25.1 r6l25.2 = false := by decide +kernel
def r6l26 : S := (0, [wireWord32, wireWord3, wireWord33, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l26Dead : optimized 5 r6l26.1 r6l26.2 = false := by decide +kernel
def r6l27 : S := (0, [wireWord23, wireWord0, wireWord33, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l27Dead : optimized 5 r6l27.1 r6l27.2 = false := by decide +kernel
def r6l28 : S := (1, [wireWord34, wireWord33, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l28Dead : optimized 5 r6l28.1 r6l28.2 = false := by decide +kernel
def r6l29 : S := (0, [wireWord34, wireWord0, wireWord33, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l29Dead : optimized 5 r6l29.1 r6l29.2 = false := by decide +kernel
def r6l30 : S := (0, [wireWord34, wireWord3, wireWord33, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l30Dead : optimized 5 r6l30.1 r6l30.2 = false := by decide +kernel
def r6l31 : S := (0, [wireWord19, wireWord1, wireWord33, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l31Dead : optimized 5 r6l31.1 r6l31.2 = false := by decide +kernel
def r6l32 : S := (0, [wireWord27, wireWord1, wireWord33, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l32Dead : optimized 5 r6l32.1 r6l32.2 = false := by decide +kernel
def r6l33 : S := (0, [wireWord15, wireWord4, wireWord33, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l33Dead : optimized 5 r6l33.1 r6l33.2 = false := by decide +kernel
def r6l34 : S := (0, [wireWord16, wireWord4, wireWord33, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r6l34Dead : optimized 5 r6l34.1 r6l34.2 = false := by decide +kernel
def r6l35 : S := (0, [wireWord5, wireWord2, wireWord33, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r6l35Dead : optimized 5 r6l35.1 r6l35.2 = false := by decide +kernel
def r6l36 : S := (0, [wireWord7, wireWord2, wireWord33, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r6l36Dead : optimized 5 r6l36.1 r6l36.2 = false := by decide +kernel
def r6l37 : S := (0, [wireWord6, wireWord2, wireWord33, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r6l37Dead : optimized 5 r6l37.1 r6l37.2 = false := by decide +kernel
def r6l38 : S := (0, [wireWord8, wireWord2, wireWord33, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r6l38Dead : optimized 5 r6l38.1 r6l38.2 = false := by decide +kernel
theorem rootCell6Dead : optimized 6 rootCell6.1 rootCell6.2 = false := by
  have kids : nexts (rootCell6.1, rootCell6.2) = [r6l0,r6l1,r6l2,r6l3,r6l4,r6l5,r6l6,r6l7,r6l8,r6l9,r6l10,r6l11,r6l12,r6l13,r6l14,r6l15,r6l16,r6l17,r6l18,r6l19,r6l20,r6l21,r6l22,r6l23,r6l24,r6l25,r6l26,r6l27,r6l28,r6l29,r6l30,r6l31,r6l32,r6l33,r6l34,r6l35,r6l36,r6l37,r6l38] := by decide +kernel
  have stop : (rootCell6.2 == [goal] || rootCell6.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r6l0Dead, r6l1Dead, r6l2Dead, r6l3Dead, r6l4Dead, r6l5Dead, r6l6Dead, r6l7Dead, r6l8Dead, r6l9Dead, r6l10Dead, r6l11Dead, r6l12Dead, r6l13Dead, r6l14Dead, r6l15Dead, r6l16Dead, r6l17Dead, r6l18Dead, r6l19Dead, r6l20Dead, r6l21Dead, r6l22Dead, r6l23Dead, r6l24Dead, r6l25Dead, r6l26Dead, r6l27Dead, r6l28Dead, r6l29Dead, r6l30Dead, r6l31Dead, r6l32Dead, r6l33Dead, r6l34Dead, r6l35Dead, r6l36Dead, r6l37Dead, r6l38Dead]
def rootCell7 : S := (1, [wireWord34, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
def r7l0 : S := (0, [0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l0Dead : optimized 5 r7l0.1 r7l0.2 = false := by decide +kernel
def r7l1 : S := (0, [wireWord23, wireWord34, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l1Dead : optimized 5 r7l1.1 r7l1.2 = false := by decide +kernel
def r7l2 : S := (0, [wireWord23, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l2Dead : optimized 5 r7l2.1 r7l2.2 = false := by decide +kernel
def r7l3 : S := (0, [wireWord34, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l3Dead : optimized 5 r7l3.1 r7l3.2 = false := by decide +kernel
def r7l4 : S := (1, [wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l4Dead : optimized 5 r7l4.1 r7l4.2 = false := by decide +kernel
def r7l5 : S := (0, [wireWord0, wireWord34, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l5Dead : optimized 5 r7l5.1 r7l5.2 = false := by decide +kernel
def r7l6 : S := (0, [wireWord0, wireWord0, wireWord3, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l6Dead : optimized 5 r7l6.1 r7l6.2 = false := by decide +kernel
def r7l7 : S := (0, [wireWord34, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l7Dead : optimized 5 r7l7.1 r7l7.2 = false := by decide +kernel
def r7l8 : S := (1, [wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l8Dead : optimized 5 r7l8.1 r7l8.2 = false := by decide +kernel
def r7l9 : S := (0, [wireWord3, wireWord34, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l9Dead : optimized 5 r7l9.1 r7l9.2 = false := by decide +kernel
def r7l10 : S := (0, [wireWord3, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l10Dead : optimized 5 r7l10.1 r7l10.2 = false := by decide +kernel
def r7l11 : S := (0, [0, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l11Dead : optimized 5 r7l11.1 r7l11.2 = false := by decide +kernel
def r7l12 : S := (0, [wireWord32, wireWord34, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l12Dead : optimized 5 r7l12.1 r7l12.2 = false := by decide +kernel
def r7l13 : S := (0, [wireWord32, wireWord3, wireWord0, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l13Dead : optimized 5 r7l13.1 r7l13.2 = false := by decide +kernel
def r7l14 : S := (0, [599546098977475600, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l14Dead : optimized 5 r7l14.1 r7l14.2 = false := by decide +kernel
def r7l15 : S := (0, [1070536042709748882, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l15Dead : optimized 5 r7l15.1 r7l15.2 = false := by decide +kernel
def r7l16 : S := (0, [1086390272, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l16Dead : optimized 5 r7l16.1 r7l16.2 = false := by decide +kernel
def r7l17 : S := (0, [470989942645883010, wireWord1, wireWord0, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l17Dead : optimized 5 r7l17.1 r7l17.2 = false := by decide +kernel
def r7l18 : S := (0, [599546099526536192, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l18Dead : optimized 5 r7l18.1 r7l18.2 = false := by decide +kernel
def r7l19 : S := (0, [3133986304337842160, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l19Dead : optimized 5 r7l19.1 r7l19.2 = false := by decide +kernel
def r7l20 : S := (0, [537329680, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l20Dead : optimized 5 r7l20.1 r7l20.2 = false := by decide +kernel
def r7l21 : S := (0, [2534440204273976288, wireWord4, wireWord0, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l21Dead : optimized 5 r7l21.1 r7l21.2 = false := by decide +kernel
def r7l22 : S := (0, [wireWord52, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r7l22Dead : optimized 5 r7l22.1 r7l22.2 = false := by decide +kernel
def r7l23 : S := (0, [4287423703471356944, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r7l23Dead : optimized 5 r7l23.1 r7l23.2 = false := by decide +kernel
def r7l24 : S := (0, [3088, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r7l24Dead : optimized 5 r7l24.1 r7l24.2 = false := by decide +kernel
def r7l25 : S := (0, [3687877603407491072, wireWord2, wireWord0, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r7l25Dead : optimized 5 r7l25.1 r7l25.2 = false := by decide +kernel
def r7l26 : S := (0, [wireWord32, wireWord0, wireWord34, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l26Dead : optimized 5 r7l26.1 r7l26.2 = false := by decide +kernel
def r7l27 : S := (0, [wireWord23, wireWord3, wireWord34, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l27Dead : optimized 5 r7l27.1 r7l27.2 = false := by decide +kernel
def r7l28 : S := (1, [wireWord33, wireWord34, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l28Dead : optimized 5 r7l28.1 r7l28.2 = false := by decide +kernel
def r7l29 : S := (0, [wireWord33, wireWord0, wireWord34, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l29Dead : optimized 5 r7l29.1 r7l29.2 = false := by decide +kernel
def r7l30 : S := (0, [wireWord33, wireWord3, wireWord34, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l30Dead : optimized 5 r7l30.1 r7l30.2 = false := by decide +kernel
def r7l31 : S := (0, [wireWord35, wireWord1, wireWord34, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l31Dead : optimized 5 r7l31.1 r7l31.2 = false := by decide +kernel
def r7l32 : S := (0, [wireWord20, wireWord1, wireWord34, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l32Dead : optimized 5 r7l32.1 r7l32.2 = false := by decide +kernel
def r7l33 : S := (0, [wireWord14, wireWord4, wireWord34, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l33Dead : optimized 5 r7l33.1 r7l33.2 = false := by decide +kernel
def r7l34 : S := (0, [wireWord17, wireWord4, wireWord34, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r7l34Dead : optimized 5 r7l34.1 r7l34.2 = false := by decide +kernel
def r7l35 : S := (0, [wireWord5, wireWord2, wireWord34, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r7l35Dead : optimized 5 r7l35.1 r7l35.2 = false := by decide +kernel
def r7l36 : S := (0, [wireWord7, wireWord2, wireWord34, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r7l36Dead : optimized 5 r7l36.1 r7l36.2 = false := by decide +kernel
def r7l37 : S := (0, [wireWord6, wireWord2, wireWord34, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r7l37Dead : optimized 5 r7l37.1 r7l37.2 = false := by decide +kernel
def r7l38 : S := (0, [wireWord8, wireWord2, wireWord34, wireWord0, wireWord3, wireWord1])
set_option maxHeartbeats 0 in
theorem r7l38Dead : optimized 5 r7l38.1 r7l38.2 = false := by decide +kernel
theorem rootCell7Dead : optimized 6 rootCell7.1 rootCell7.2 = false := by
  have kids : nexts (rootCell7.1, rootCell7.2) = [r7l0,r7l1,r7l2,r7l3,r7l4,r7l5,r7l6,r7l7,r7l8,r7l9,r7l10,r7l11,r7l12,r7l13,r7l14,r7l15,r7l16,r7l17,r7l18,r7l19,r7l20,r7l21,r7l22,r7l23,r7l24,r7l25,r7l26,r7l27,r7l28,r7l29,r7l30,r7l31,r7l32,r7l33,r7l34,r7l35,r7l36,r7l37,r7l38] := by decide +kernel
  have stop : (rootCell7.2 == [goal] || rootCell7.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r7l0Dead, r7l1Dead, r7l2Dead, r7l3Dead, r7l4Dead, r7l5Dead, r7l6Dead, r7l7Dead, r7l8Dead, r7l9Dead, r7l10Dead, r7l11Dead, r7l12Dead, r7l13Dead, r7l14Dead, r7l15Dead, r7l16Dead, r7l17Dead, r7l18Dead, r7l19Dead, r7l20Dead, r7l21Dead, r7l22Dead, r7l23Dead, r7l24Dead, r7l25Dead, r7l26Dead, r7l27Dead, r7l28Dead, r7l29Dead, r7l30Dead, r7l31Dead, r7l32Dead, r7l33Dead, r7l34Dead, r7l35Dead, r7l36Dead, r7l37Dead, r7l38Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell8 : S := (1, [wireWord28, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
def r8l0 : S := (0, [wireWord28, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l0Dead : optimized 5 r8l0.1 r8l0.2 = false := by decide +kernel
def r8l1 : S := (1, [wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l1Dead : optimized 5 r8l1.1 r8l1.2 = false := by decide +kernel
def r8l2 : S := (0, [wireWord0, wireWord28, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l2Dead : optimized 5 r8l2.1 r8l2.2 = false := by decide +kernel
def r8l3 : S := (0, [wireWord0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l3Dead : optimized 5 r8l3.1 r8l3.2 = false := by decide +kernel
def r8l4 : S := (0, [0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l4Dead : optimized 5 r8l4.1 r8l4.2 = false := by decide +kernel
def r8l5 : S := (0, [wireWord36, wireWord28, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l5Dead : optimized 5 r8l5.1 r8l5.2 = false := by decide +kernel
def r8l6 : S := (0, [wireWord36, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l6Dead : optimized 5 r8l6.1 r8l6.2 = false := by decide +kernel
def r8l7 : S := (0, [wireWord28, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l7Dead : optimized 5 r8l7.1 r8l7.2 = false := by decide +kernel
def r8l8 : S := (1, [wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l8Dead : optimized 5 r8l8.1 r8l8.2 = false := by decide +kernel
def r8l9 : S := (0, [wireWord4, wireWord28, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l9Dead : optimized 5 r8l9.1 r8l9.2 = false := by decide +kernel
def r8l10 : S := (0, [wireWord4, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l10Dead : optimized 5 r8l10.1 r8l10.2 = false := by decide +kernel
def r8l11 : S := (0, [0, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l11Dead : optimized 5 r8l11.1 r8l11.2 = false := by decide +kernel
def r8l12 : S := (0, [wireWord37, wireWord28, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l12Dead : optimized 5 r8l12.1 r8l12.2 = false := by decide +kernel
def r8l13 : S := (0, [wireWord37, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l13Dead : optimized 5 r8l13.1 r8l13.2 = false := by decide +kernel
def r8l14 : S := (0, [146370080265994240, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l14Dead : optimized 5 r8l14.1 r8l14.2 = false := by decide +kernel
def r8l15 : S := (0, [3458606165359235058, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l15Dead : optimized 5 r8l15.1 r8l15.2 = false := by decide +kernel
def r8l16 : S := (0, [2388070123735876448, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l16Dead : optimized 5 r8l16.1 r8l16.2 = false := by decide +kernel
def r8l17 : S := (0, [924165961357364370, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l17Dead : optimized 5 r8l17.1 r8l17.2 = false := by decide +kernel
def r8l18 : S := (0, [81068641583366912, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l18Dead : optimized 5 r8l18.1 r8l18.2 = false := by decide +kernel
def r8l19 : S := (1, [4287347673453236092, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l19Dead : optimized 5 r8l19.1 r8l19.2 = false := by decide +kernel
def r8l20 : S := (0, [4287347673453236092, wireWord28, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l20Dead : optimized 5 r8l20.1 r8l20.2 = false := by decide +kernel
def r8l21 : S := (0, [4287347673453236092, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l21Dead : optimized 5 r8l21.1 r8l21.2 = false := by decide +kernel
def r8l22 : S := (0, [2453371562418503776, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l22Dead : optimized 5 r8l22.1 r8l22.2 = false := by decide +kernel
def r8l23 : S := (1, [1752907469451365404, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l23Dead : optimized 5 r8l23.1 r8l23.2 = false := by decide +kernel
def r8l24 : S := (0, [1752907469451365404, wireWord28, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l24Dead : optimized 5 r8l24.1 r8l24.2 = false := by decide +kernel
def r8l25 : S := (0, [1752907469451365404, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l25Dead : optimized 5 r8l25.1 r8l25.2 = false := by decide +kernel
def r8l26 : S := (0, [wireWord53, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r8l26Dead : optimized 5 r8l26.1 r8l26.2 = false := by decide +kernel
def r8l27 : S := (0, [4287426795847807840, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r8l27Dead : optimized 5 r8l27.1 r8l27.2 = false := by decide +kernel
def r8l28 : S := (0, [3092376453984, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r8l28Dead : optimized 5 r8l28.1 r8l28.2 = false := by decide +kernel
def r8l29 : S := (0, [1752986591845937152, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r8l29Dead : optimized 5 r8l29.1 r8l29.2 = false := by decide +kernel
def r8l30 : S := (1, [wireWord18, wireWord28, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l30Dead : optimized 5 r8l30.1 r8l30.2 = false := by decide +kernel
def r8l31 : S := (0, [wireWord18, wireWord0, wireWord28, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l31Dead : optimized 5 r8l31.1 r8l31.2 = false := by decide +kernel
def r8l32 : S := (0, [wireWord18, wireWord4, wireWord28, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l32Dead : optimized 5 r8l32.1 r8l32.2 = false := by decide +kernel
def r8l33 : S := (0, [wireWord36, wireWord4, wireWord28, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l33Dead : optimized 5 r8l33.1 r8l33.2 = false := by decide +kernel
def r8l34 : S := (0, [wireWord37, wireWord0, wireWord28, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l34Dead : optimized 5 r8l34.1 r8l34.2 = false := by decide +kernel
def r8l35 : S := (0, [wireWord21, wireWord1, wireWord28, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l35Dead : optimized 5 r8l35.1 r8l35.2 = false := by decide +kernel
def r8l36 : S := (0, [wireWord29, wireWord1, wireWord28, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l36Dead : optimized 5 r8l36.1 r8l36.2 = false := by decide +kernel
def r8l37 : S := (0, [wireWord15, wireWord3, wireWord28, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l37Dead : optimized 5 r8l37.1 r8l37.2 = false := by decide +kernel
def r8l38 : S := (0, [wireWord17, wireWord3, wireWord28, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r8l38Dead : optimized 5 r8l38.1 r8l38.2 = false := by decide +kernel
def r8l39 : S := (0, [wireWord6, wireWord2, wireWord28, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r8l39Dead : optimized 5 r8l39.1 r8l39.2 = false := by decide +kernel
def r8l40 : S := (0, [wireWord8, wireWord2, wireWord28, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r8l40Dead : optimized 5 r8l40.1 r8l40.2 = false := by decide +kernel
def r8l41 : S := (0, [wireWord5, wireWord2, wireWord28, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r8l41Dead : optimized 5 r8l41.1 r8l41.2 = false := by decide +kernel
def r8l42 : S := (0, [wireWord7, wireWord2, wireWord28, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r8l42Dead : optimized 5 r8l42.1 r8l42.2 = false := by decide +kernel
theorem rootCell8Dead : optimized 6 rootCell8.1 rootCell8.2 = false := by
  have kids : nexts (rootCell8.1, rootCell8.2) = [r8l0,r8l1,r8l2,r8l3,r8l4,r8l5,r8l6,r8l7,r8l8,r8l9,r8l10,r8l11,r8l12,r8l13,r8l14,r8l15,r8l16,r8l17,r8l18,r8l19,r8l20,r8l21,r8l22,r8l23,r8l24,r8l25,r8l26,r8l27,r8l28,r8l29,r8l30,r8l31,r8l32,r8l33,r8l34,r8l35,r8l36,r8l37,r8l38,r8l39,r8l40,r8l41,r8l42] := by decide +kernel
  have stop : (rootCell8.2 == [goal] || rootCell8.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r8l0Dead, r8l1Dead, r8l2Dead, r8l3Dead, r8l4Dead, r8l5Dead, r8l6Dead, r8l7Dead, r8l8Dead, r8l9Dead, r8l10Dead, r8l11Dead, r8l12Dead, r8l13Dead, r8l14Dead, r8l15Dead, r8l16Dead, r8l17Dead, r8l18Dead, r8l19Dead, r8l20Dead, r8l21Dead, r8l22Dead, r8l23Dead, r8l24Dead, r8l25Dead, r8l26Dead, r8l27Dead, r8l28Dead, r8l29Dead, r8l30Dead, r8l31Dead, r8l32Dead, r8l33Dead, r8l34Dead, r8l35Dead, r8l36Dead, r8l37Dead, r8l38Dead, r8l39Dead, r8l40Dead, r8l41Dead, r8l42Dead]
def rootCell9 : S := (1, [wireWord18, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
def r9l0 : S := (1, [wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l0Dead : optimized 5 r9l0.1 r9l0.2 = false := by decide +kernel
def r9l1 : S := (0, [wireWord0, wireWord18, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l1Dead : optimized 5 r9l1.1 r9l1.2 = false := by decide +kernel
def r9l2 : S := (0, [wireWord0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l2Dead : optimized 5 r9l2.1 r9l2.2 = false := by decide +kernel
def r9l3 : S := (0, [wireWord18, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l3Dead : optimized 5 r9l3.1 r9l3.2 = false := by decide +kernel
def r9l4 : S := (0, [wireWord37, wireWord18, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l4Dead : optimized 5 r9l4.1 r9l4.2 = false := by decide +kernel
def r9l5 : S := (0, [wireWord37, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l5Dead : optimized 5 r9l5.1 r9l5.2 = false := by decide +kernel
def r9l6 : S := (0, [0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l6Dead : optimized 5 r9l6.1 r9l6.2 = false := by decide +kernel
def r9l7 : S := (1, [wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l7Dead : optimized 5 r9l7.1 r9l7.2 = false := by decide +kernel
def r9l8 : S := (0, [wireWord4, wireWord18, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l8Dead : optimized 5 r9l8.1 r9l8.2 = false := by decide +kernel
def r9l9 : S := (0, [wireWord4, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l9Dead : optimized 5 r9l9.1 r9l9.2 = false := by decide +kernel
def r9l10 : S := (0, [wireWord18, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l10Dead : optimized 5 r9l10.1 r9l10.2 = false := by decide +kernel
def r9l11 : S := (0, [wireWord36, wireWord18, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l11Dead : optimized 5 r9l11.1 r9l11.2 = false := by decide +kernel
def r9l12 : S := (0, [wireWord36, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l12Dead : optimized 5 r9l12.1 r9l12.2 = false := by decide +kernel
def r9l13 : S := (0, [0, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l13Dead : optimized 5 r9l13.1 r9l13.2 = false := by decide +kernel
def r9l14 : S := (1, [1070536041086061696, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l14Dead : optimized 5 r9l14.1 r9l14.2 = false := by decide +kernel
def r9l15 : S := (0, [1070536041086061696, wireWord18, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l15Dead : optimized 5 r9l15.1 r9l15.2 = false := by decide +kernel
def r9l16 : S := (0, [1070536041086061696, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l16Dead : optimized 5 r9l16.1 r9l16.2 = false := by decide +kernel
def r9l17 : S := (0, [4611686018410545151, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l17Dead : optimized 5 r9l17.1 r9l17.2 = false := by decide +kernel
def r9l18 : S := (1, [3541149976787186541, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l18Dead : optimized 5 r9l18.1 r9l18.2 = false := by decide +kernel
def r9l19 : S := (0, [3541149976787186541, wireWord18, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l19Dead : optimized 5 r9l19.1 r9l19.2 = false := by decide +kernel
def r9l20 : S := (0, [3541149976787186541, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l20Dead : optimized 5 r9l20.1 r9l20.2 = false := by decide +kernel
def r9l21 : S := (0, [537296914, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l21Dead : optimized 5 r9l21.1 r9l21.2 = false := by decide +kernel
def r9l22 : S := (1, [1833976110497402636, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l22Dead : optimized 5 r9l22.1 r9l22.2 = false := by decide +kernel
def r9l23 : S := (0, [1833976110497402636, wireWord18, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l23Dead : optimized 5 r9l23.1 r9l23.2 = false := by decide +kernel
def r9l24 : S := (0, [1833976110497402636, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l24Dead : optimized 5 r9l24.1 r9l24.2 = false := by decide +kernel
def r9l25 : S := (0, [4611686018410577917, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l25Dead : optimized 5 r9l25.1 r9l25.2 = false := by decide +kernel
def r9l26 : S := (1, [2777709907375845601, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l26Dead : optimized 5 r9l26.1 r9l26.2 = false := by decide +kernel
def r9l27 : S := (0, [2777709907375845601, wireWord18, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l27Dead : optimized 5 r9l27.1 r9l27.2 = false := by decide +kernel
def r9l28 : S := (0, [2777709907375845601, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l28Dead : optimized 5 r9l28.1 r9l28.2 = false := by decide +kernel
def r9l29 : S := (0, [537329680, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l29Dead : optimized 5 r9l29.1 r9l29.2 = false := by decide +kernel
def r9l30 : S := (1, [4287423702933991424, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l30Dead : optimized 5 r9l30.1 r9l30.2 = false := by decide +kernel
def r9l31 : S := (0, [4287423702933991424, wireWord18, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l31Dead : optimized 5 r9l31.1 r9l31.2 = false := by decide +kernel
def r9l32 : S := (0, [4287423702933991424, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l32Dead : optimized 5 r9l32.1 r9l32.2 = false := by decide +kernel
def r9l33 : S := (0, [4611686018410610669, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l33Dead : optimized 5 r9l33.1 r9l33.2 = false := by decide +kernel
def r9l34 : S := (1, [324262314939256813, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l34Dead : optimized 5 r9l34.1 r9l34.2 = false := by decide +kernel
def r9l35 : S := (0, [324262314939256813, wireWord18, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l35Dead : optimized 5 r9l35.1 r9l35.2 = false := by decide +kernel
def r9l36 : S := (0, [324262314939256813, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l36Dead : optimized 5 r9l36.1 r9l36.2 = false := by decide +kernel
def r9l37 : S := (0, [wireWord54, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l37Dead : optimized 5 r9l37.1 r9l37.2 = false := by decide +kernel
def r9l38 : S := (1, [wireWord28, wireWord18, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l38Dead : optimized 5 r9l38.1 r9l38.2 = false := by decide +kernel
def r9l39 : S := (0, [wireWord28, wireWord0, wireWord18, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l39Dead : optimized 5 r9l39.1 r9l39.2 = false := by decide +kernel
def r9l40 : S := (0, [wireWord28, wireWord4, wireWord18, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l40Dead : optimized 5 r9l40.1 r9l40.2 = false := by decide +kernel
def r9l41 : S := (0, [wireWord36, wireWord0, wireWord18, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l41Dead : optimized 5 r9l41.1 r9l41.2 = false := by decide +kernel
def r9l42 : S := (0, [wireWord37, wireWord4, wireWord18, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l42Dead : optimized 5 r9l42.1 r9l42.2 = false := by decide +kernel
def r9l43 : S := (0, [wireWord38, wireWord1, wireWord18, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l43Dead : optimized 5 r9l43.1 r9l43.2 = false := by decide +kernel
def r9l44 : S := (0, [wireWord22, wireWord1, wireWord18, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l44Dead : optimized 5 r9l44.1 r9l44.2 = false := by decide +kernel
def r9l45 : S := (0, [wireWord14, wireWord3, wireWord18, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l45Dead : optimized 5 r9l45.1 r9l45.2 = false := by decide +kernel
def r9l46 : S := (0, [wireWord16, wireWord3, wireWord18, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r9l46Dead : optimized 5 r9l46.1 r9l46.2 = false := by decide +kernel
def r9l47 : S := (0, [wireWord6, wireWord2, wireWord18, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l47Dead : optimized 5 r9l47.1 r9l47.2 = false := by decide +kernel
def r9l48 : S := (0, [wireWord8, wireWord2, wireWord18, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r9l48Dead : optimized 5 r9l48.1 r9l48.2 = false := by decide +kernel
def r9l49 : S := (0, [wireWord5, wireWord2, wireWord18, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r9l49Dead : optimized 5 r9l49.1 r9l49.2 = false := by decide +kernel
def r9l50 : S := (0, [wireWord7, wireWord2, wireWord18, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r9l50Dead : optimized 5 r9l50.1 r9l50.2 = false := by decide +kernel
theorem rootCell9Dead : optimized 6 rootCell9.1 rootCell9.2 = false := by
  have kids : nexts (rootCell9.1, rootCell9.2) = [r9l0,r9l1,r9l2,r9l3,r9l4,r9l5,r9l6,r9l7,r9l8,r9l9,r9l10,r9l11,r9l12,r9l13,r9l14,r9l15,r9l16,r9l17,r9l18,r9l19,r9l20,r9l21,r9l22,r9l23,r9l24,r9l25,r9l26,r9l27,r9l28,r9l29,r9l30,r9l31,r9l32,r9l33,r9l34,r9l35,r9l36,r9l37,r9l38,r9l39,r9l40,r9l41,r9l42,r9l43,r9l44,r9l45,r9l46,r9l47,r9l48,r9l49,r9l50] := by decide +kernel
  have stop : (rootCell9.2 == [goal] || rootCell9.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r9l0Dead, r9l1Dead, r9l2Dead, r9l3Dead, r9l4Dead, r9l5Dead, r9l6Dead, r9l7Dead, r9l8Dead, r9l9Dead, r9l10Dead, r9l11Dead, r9l12Dead, r9l13Dead, r9l14Dead, r9l15Dead, r9l16Dead, r9l17Dead, r9l18Dead, r9l19Dead, r9l20Dead, r9l21Dead, r9l22Dead, r9l23Dead, r9l24Dead, r9l25Dead, r9l26Dead, r9l27Dead, r9l28Dead, r9l29Dead, r9l30Dead, r9l31Dead, r9l32Dead, r9l33Dead, r9l34Dead, r9l35Dead, r9l36Dead, r9l37Dead, r9l38Dead, r9l39Dead, r9l40Dead, r9l41Dead, r9l42Dead, r9l43Dead, r9l44Dead, r9l45Dead, r9l46Dead, r9l47Dead, r9l48Dead, r9l49Dead, r9l50Dead]
def rootCell10 : S := (1, [wireWord36, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
def r10l0 : S := (0, [wireWord36, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l0Dead : optimized 5 r10l0.1 r10l0.2 = false := by decide +kernel
def r10l1 : S := (1, [wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l1Dead : optimized 5 r10l1.1 r10l1.2 = false := by decide +kernel
def r10l2 : S := (0, [wireWord0, wireWord36, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l2Dead : optimized 5 r10l2.1 r10l2.2 = false := by decide +kernel
def r10l3 : S := (0, [wireWord0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l3Dead : optimized 5 r10l3.1 r10l3.2 = false := by decide +kernel
def r10l4 : S := (0, [0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l4Dead : optimized 5 r10l4.1 r10l4.2 = false := by decide +kernel
def r10l5 : S := (0, [wireWord28, wireWord36, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l5Dead : optimized 5 r10l5.1 r10l5.2 = false := by decide +kernel
def r10l6 : S := (0, [wireWord28, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l6Dead : optimized 5 r10l6.1 r10l6.2 = false := by decide +kernel
def r10l7 : S := (0, [0, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l7Dead : optimized 5 r10l7.1 r10l7.2 = false := by decide +kernel
def r10l8 : S := (0, [wireWord18, wireWord36, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l8Dead : optimized 5 r10l8.1 r10l8.2 = false := by decide +kernel
def r10l9 : S := (0, [wireWord18, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l9Dead : optimized 5 r10l9.1 r10l9.2 = false := by decide +kernel
def r10l10 : S := (0, [wireWord36, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l10Dead : optimized 5 r10l10.1 r10l10.2 = false := by decide +kernel
def r10l11 : S := (1, [wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l11Dead : optimized 5 r10l11.1 r10l11.2 = false := by decide +kernel
def r10l12 : S := (0, [wireWord4, wireWord36, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l12Dead : optimized 5 r10l12.1 r10l12.2 = false := by decide +kernel
def r10l13 : S := (0, [wireWord4, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l13Dead : optimized 5 r10l13.1 r10l13.2 = false := by decide +kernel
def r10l14 : S := (0, [324619862376710144, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l14Dead : optimized 5 r10l14.1 r10l14.2 = false := by decide +kernel
def r10l15 : S := (0, [2223615893319384223, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l15Dead : optimized 5 r10l15.1 r10l15.2 = false := by decide +kernel
def r10l16 : S := (0, [1153079851696025613, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l16Dead : optimized 5 r10l16.1 r10l16.2 = false := by decide +kernel
def r10l17 : S := (0, [745916179246648466, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l17Dead : optimized 5 r10l17.1 r10l17.2 = false := by decide +kernel
def r10l18 : S := (0, [1153361369387499532, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l18Dead : optimized 5 r10l18.1 r10l18.2 = false := by decide +kernel
def r10l19 : S := (0, [2158314455719968541, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l19Dead : optimized 5 r10l19.1 r10l19.2 = false := by decide +kernel
def r10l20 : S := (0, [324338344685236225, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l20Dead : optimized 5 r10l20.1 r10l20.2 = false := by decide +kernel
def r10l21 : S := (0, [680614741647232784, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l21Dead : optimized 5 r10l21.1 r10l21.2 = false := by decide +kernel
def r10l22 : S := (0, [wireWord55, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r10l22Dead : optimized 5 r10l22.1 r10l22.2 = false := by decide +kernel
def r10l23 : S := (0, [4611682926034153485, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r10l23Dead : optimized 5 r10l23.1 r10l23.2 = false := by decide +kernel
def r10l24 : S := (0, [324259222562799629, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r10l24Dead : optimized 5 r10l24.1 r10l24.2 = false := by decide +kernel
def r10l25 : S := (0, [3133983211961417728, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r10l25Dead : optimized 5 r10l25.1 r10l25.2 = false := by decide +kernel
def r10l26 : S := (0, [wireWord28, wireWord4, wireWord36, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l26Dead : optimized 5 r10l26.1 r10l26.2 = false := by decide +kernel
def r10l27 : S := (0, [wireWord18, wireWord0, wireWord36, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l27Dead : optimized 5 r10l27.1 r10l27.2 = false := by decide +kernel
def r10l28 : S := (1, [wireWord37, wireWord36, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l28Dead : optimized 5 r10l28.1 r10l28.2 = false := by decide +kernel
def r10l29 : S := (0, [wireWord37, wireWord0, wireWord36, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l29Dead : optimized 5 r10l29.1 r10l29.2 = false := by decide +kernel
def r10l30 : S := (0, [wireWord37, wireWord4, wireWord36, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l30Dead : optimized 5 r10l30.1 r10l30.2 = false := by decide +kernel
def r10l31 : S := (0, [wireWord21, wireWord1, wireWord36, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l31Dead : optimized 5 r10l31.1 r10l31.2 = false := by decide +kernel
def r10l32 : S := (0, [wireWord29, wireWord1, wireWord36, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l32Dead : optimized 5 r10l32.1 r10l32.2 = false := by decide +kernel
def r10l33 : S := (0, [wireWord15, wireWord3, wireWord36, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l33Dead : optimized 5 r10l33.1 r10l33.2 = false := by decide +kernel
def r10l34 : S := (0, [wireWord17, wireWord3, wireWord36, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r10l34Dead : optimized 5 r10l34.1 r10l34.2 = false := by decide +kernel
def r10l35 : S := (0, [wireWord6, wireWord2, wireWord36, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r10l35Dead : optimized 5 r10l35.1 r10l35.2 = false := by decide +kernel
def r10l36 : S := (0, [wireWord8, wireWord2, wireWord36, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r10l36Dead : optimized 5 r10l36.1 r10l36.2 = false := by decide +kernel
def r10l37 : S := (0, [wireWord5, wireWord2, wireWord36, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r10l37Dead : optimized 5 r10l37.1 r10l37.2 = false := by decide +kernel
def r10l38 : S := (0, [wireWord7, wireWord2, wireWord36, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r10l38Dead : optimized 5 r10l38.1 r10l38.2 = false := by decide +kernel
theorem rootCell10Dead : optimized 6 rootCell10.1 rootCell10.2 = false := by
  have kids : nexts (rootCell10.1, rootCell10.2) = [r10l0,r10l1,r10l2,r10l3,r10l4,r10l5,r10l6,r10l7,r10l8,r10l9,r10l10,r10l11,r10l12,r10l13,r10l14,r10l15,r10l16,r10l17,r10l18,r10l19,r10l20,r10l21,r10l22,r10l23,r10l24,r10l25,r10l26,r10l27,r10l28,r10l29,r10l30,r10l31,r10l32,r10l33,r10l34,r10l35,r10l36,r10l37,r10l38] := by decide +kernel
  have stop : (rootCell10.2 == [goal] || rootCell10.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r10l0Dead, r10l1Dead, r10l2Dead, r10l3Dead, r10l4Dead, r10l5Dead, r10l6Dead, r10l7Dead, r10l8Dead, r10l9Dead, r10l10Dead, r10l11Dead, r10l12Dead, r10l13Dead, r10l14Dead, r10l15Dead, r10l16Dead, r10l17Dead, r10l18Dead, r10l19Dead, r10l20Dead, r10l21Dead, r10l22Dead, r10l23Dead, r10l24Dead, r10l25Dead, r10l26Dead, r10l27Dead, r10l28Dead, r10l29Dead, r10l30Dead, r10l31Dead, r10l32Dead, r10l33Dead, r10l34Dead, r10l35Dead, r10l36Dead, r10l37Dead, r10l38Dead]
def rootCell11 : S := (1, [wireWord37, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
def r11l0 : S := (0, [0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l0Dead : optimized 5 r11l0.1 r11l0.2 = false := by decide +kernel
def r11l1 : S := (0, [wireWord18, wireWord37, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l1Dead : optimized 5 r11l1.1 r11l1.2 = false := by decide +kernel
def r11l2 : S := (0, [wireWord18, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l2Dead : optimized 5 r11l2.1 r11l2.2 = false := by decide +kernel
def r11l3 : S := (0, [wireWord37, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l3Dead : optimized 5 r11l3.1 r11l3.2 = false := by decide +kernel
def r11l4 : S := (1, [wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l4Dead : optimized 5 r11l4.1 r11l4.2 = false := by decide +kernel
def r11l5 : S := (0, [wireWord0, wireWord37, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l5Dead : optimized 5 r11l5.1 r11l5.2 = false := by decide +kernel
def r11l6 : S := (0, [wireWord0, wireWord0, wireWord4, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l6Dead : optimized 5 r11l6.1 r11l6.2 = false := by decide +kernel
def r11l7 : S := (0, [wireWord37, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l7Dead : optimized 5 r11l7.1 r11l7.2 = false := by decide +kernel
def r11l8 : S := (1, [wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l8Dead : optimized 5 r11l8.1 r11l8.2 = false := by decide +kernel
def r11l9 : S := (0, [wireWord4, wireWord37, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l9Dead : optimized 5 r11l9.1 r11l9.2 = false := by decide +kernel
def r11l10 : S := (0, [wireWord4, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l10Dead : optimized 5 r11l10.1 r11l10.2 = false := by decide +kernel
def r11l11 : S := (0, [0, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l11Dead : optimized 5 r11l11.1 r11l11.2 = false := by decide +kernel
def r11l12 : S := (0, [wireWord28, wireWord37, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l12Dead : optimized 5 r11l12.1 r11l12.2 = false := by decide +kernel
def r11l13 : S := (0, [wireWord28, wireWord4, wireWord0, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l13Dead : optimized 5 r11l13.1 r11l13.2 = false := by decide +kernel
def r11l14 : S := (0, [599546098443357312, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l14Dead : optimized 5 r11l14.1 r11l14.2 = false := by decide +kernel
def r11l15 : S := (0, [1070536042978643090, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l15Dead : optimized 5 r11l15.1 r11l15.2 = false := by decide +kernel
def r11l16 : S := (0, [1355284480, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l16Dead : optimized 5 r11l16.1 r11l16.2 = false := by decide +kernel
def r11l17 : S := (0, [470989943180001298, wireWord1, wireWord0, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l17Dead : optimized 5 r11l17.1 r11l17.2 = false := by decide +kernel
def r11l18 : S := (0, [599546099526536192, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l18Dead : optimized 5 r11l18.1 r11l18.2 = false := by decide +kernel
def r11l19 : S := (0, [1833976111306837916, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l19Dead : optimized 5 r11l19.1 r11l19.2 = false := by decide +kernel
def r11l20 : S := (0, [272105600, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l20Dead : optimized 5 r11l20.1 r11l20.2 = false := by decide +kernel
def r11l21 : S := (0, [1234430011508196124, wireWord3, wireWord0, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l21Dead : optimized 5 r11l21.1 r11l21.2 = false := by decide +kernel
def r11l22 : S := (0, [wireWord56, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r11l22Dead : optimized 5 r11l22.1 r11l22.2 = false := by decide +kernel
def r11l23 : S := (0, [4287423703471357056, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r11l23Dead : optimized 5 r11l23.1 r11l23.2 = false := by decide +kernel
def r11l24 : S := (0, [3200, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r11l24Dead : optimized 5 r11l24.1 r11l24.2 = false := by decide +kernel
def r11l25 : S := (0, [3687877603672715264, wireWord2, wireWord0, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r11l25Dead : optimized 5 r11l25.1 r11l25.2 = false := by decide +kernel
def r11l26 : S := (0, [wireWord28, wireWord0, wireWord37, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l26Dead : optimized 5 r11l26.1 r11l26.2 = false := by decide +kernel
def r11l27 : S := (0, [wireWord18, wireWord4, wireWord37, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l27Dead : optimized 5 r11l27.1 r11l27.2 = false := by decide +kernel
def r11l28 : S := (1, [wireWord36, wireWord37, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l28Dead : optimized 5 r11l28.1 r11l28.2 = false := by decide +kernel
def r11l29 : S := (0, [wireWord36, wireWord0, wireWord37, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l29Dead : optimized 5 r11l29.1 r11l29.2 = false := by decide +kernel
def r11l30 : S := (0, [wireWord36, wireWord4, wireWord37, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l30Dead : optimized 5 r11l30.1 r11l30.2 = false := by decide +kernel
def r11l31 : S := (0, [wireWord38, wireWord1, wireWord37, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l31Dead : optimized 5 r11l31.1 r11l31.2 = false := by decide +kernel
def r11l32 : S := (0, [wireWord22, wireWord1, wireWord37, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l32Dead : optimized 5 r11l32.1 r11l32.2 = false := by decide +kernel
def r11l33 : S := (0, [wireWord14, wireWord3, wireWord37, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l33Dead : optimized 5 r11l33.1 r11l33.2 = false := by decide +kernel
def r11l34 : S := (0, [wireWord16, wireWord3, wireWord37, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r11l34Dead : optimized 5 r11l34.1 r11l34.2 = false := by decide +kernel
def r11l35 : S := (0, [wireWord6, wireWord2, wireWord37, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r11l35Dead : optimized 5 r11l35.1 r11l35.2 = false := by decide +kernel
def r11l36 : S := (0, [wireWord8, wireWord2, wireWord37, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r11l36Dead : optimized 5 r11l36.1 r11l36.2 = false := by decide +kernel
def r11l37 : S := (0, [wireWord5, wireWord2, wireWord37, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r11l37Dead : optimized 5 r11l37.1 r11l37.2 = false := by decide +kernel
def r11l38 : S := (0, [wireWord7, wireWord2, wireWord37, wireWord0, wireWord4, wireWord1])
set_option maxHeartbeats 0 in
theorem r11l38Dead : optimized 5 r11l38.1 r11l38.2 = false := by decide +kernel
theorem rootCell11Dead : optimized 6 rootCell11.1 rootCell11.2 = false := by
  have kids : nexts (rootCell11.1, rootCell11.2) = [r11l0,r11l1,r11l2,r11l3,r11l4,r11l5,r11l6,r11l7,r11l8,r11l9,r11l10,r11l11,r11l12,r11l13,r11l14,r11l15,r11l16,r11l17,r11l18,r11l19,r11l20,r11l21,r11l22,r11l23,r11l24,r11l25,r11l26,r11l27,r11l28,r11l29,r11l30,r11l31,r11l32,r11l33,r11l34,r11l35,r11l36,r11l37,r11l38] := by decide +kernel
  have stop : (rootCell11.2 == [goal] || rootCell11.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r11l0Dead, r11l1Dead, r11l2Dead, r11l3Dead, r11l4Dead, r11l5Dead, r11l6Dead, r11l7Dead, r11l8Dead, r11l9Dead, r11l10Dead, r11l11Dead, r11l12Dead, r11l13Dead, r11l14Dead, r11l15Dead, r11l16Dead, r11l17Dead, r11l18Dead, r11l19Dead, r11l20Dead, r11l21Dead, r11l22Dead, r11l23Dead, r11l24Dead, r11l25Dead, r11l26Dead, r11l27Dead, r11l28Dead, r11l29Dead, r11l30Dead, r11l31Dead, r11l32Dead, r11l33Dead, r11l34Dead, r11l35Dead, r11l36Dead, r11l37Dead, r11l38Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell12 : S := (1, [wireWord10, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
def r12l0 : S := (0, [wireWord10, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l0Dead : optimized 5 r12l0.1 r12l0.2 = false := by decide +kernel
def r12l1 : S := (1, [wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l1Dead : optimized 5 r12l1.1 r12l1.2 = false := by decide +kernel
def r12l2 : S := (0, [wireWord0, wireWord10, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l2Dead : optimized 5 r12l2.1 r12l2.2 = false := by decide +kernel
def r12l3 : S := (0, [wireWord0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l3Dead : optimized 5 r12l3.1 r12l3.2 = false := by decide +kernel
def r12l4 : S := (0, [0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l4Dead : optimized 5 r12l4.1 r12l4.2 = false := by decide +kernel
def r12l5 : S := (0, [wireWord12, wireWord10, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l5Dead : optimized 5 r12l5.1 r12l5.2 = false := by decide +kernel
def r12l6 : S := (0, [wireWord12, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l6Dead : optimized 5 r12l6.1 r12l6.2 = false := by decide +kernel
def r12l7 : S := (0, [wireWord10, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l7Dead : optimized 5 r12l7.1 r12l7.2 = false := by decide +kernel
def r12l8 : S := (1, [wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l8Dead : optimized 5 r12l8.1 r12l8.2 = false := by decide +kernel
def r12l9 : S := (0, [wireWord2, wireWord10, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l9Dead : optimized 5 r12l9.1 r12l9.2 = false := by decide +kernel
def r12l10 : S := (0, [wireWord2, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l10Dead : optimized 5 r12l10.1 r12l10.2 = false := by decide +kernel
def r12l11 : S := (0, [0, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l11Dead : optimized 5 r12l11.1 r12l11.2 = false := by decide +kernel
def r12l12 : S := (0, [wireWord31, wireWord10, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l12Dead : optimized 5 r12l12.1 r12l12.2 = false := by decide +kernel
def r12l13 : S := (0, [wireWord31, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l13Dead : optimized 5 r12l13.1 r12l13.2 = false := by decide +kernel
def r12l14 : S := (0, [146727627703451648, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l14Dead : optimized 5 r12l14.1 r12l14.2 = false := by decide +kernel
def r12l15 : S := (0, [4611686017055259794, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l15Dead : optimized 5 r12l15.1 r12l15.2 = false := by decide +kernel
def r12l16 : S := (0, [3541149975431901184, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l16Dead : optimized 5 r12l16.1 r12l16.2 = false := by decide +kernel
def r12l17 : S := (0, [923808413919906962, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l17Dead : optimized 5 r12l17.1 r12l17.2 = false := by decide +kernel
def r12l18 : S := (0, [wireWord49, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l18Dead : optimized 5 r12l18.1 r12l18.2 = false := by decide +kernel
def r12l19 : S := (0, [4287426494927961884, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l19Dead : optimized 5 r12l19.1 r12l19.2 = false := by decide +kernel
def r12l20 : S := (0, [wireWord51, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l20Dead : optimized 5 r12l20.1 r12l20.2 = false := by decide +kernel
def r12l21 : S := (0, [599548891792609052, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l21Dead : optimized 5 r12l21.1 r12l21.2 = false := by decide +kernel
def r12l22 : S := (0, [wireWord53, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l22Dead : optimized 5 r12l22.1 r12l22.2 = false := by decide +kernel
def r12l23 : S := (0, [4287426795310448608, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l23Dead : optimized 5 r12l23.1 r12l23.2 = false := by decide +kernel
def r12l24 : S := (0, [wireWord55, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l24Dead : optimized 5 r12l24.1 r12l24.2 = false := by decide +kernel
def r12l25 : S := (0, [599549192175095776, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l25Dead : optimized 5 r12l25.1 r12l25.2 = false := by decide +kernel
def r12l26 : S := (1, [wireWord30, wireWord10, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l26Dead : optimized 5 r12l26.1 r12l26.2 = false := by decide +kernel
def r12l27 : S := (0, [wireWord30, wireWord0, wireWord10, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l27Dead : optimized 5 r12l27.1 r12l27.2 = false := by decide +kernel
def r12l28 : S := (0, [wireWord30, wireWord2, wireWord10, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l28Dead : optimized 5 r12l28.1 r12l28.2 = false := by decide +kernel
def r12l29 : S := (0, [wireWord12, wireWord2, wireWord10, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l29Dead : optimized 5 r12l29.1 r12l29.2 = false := by decide +kernel
def r12l30 : S := (0, [wireWord31, wireWord0, wireWord10, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l30Dead : optimized 5 r12l30.1 r12l30.2 = false := by decide +kernel
def r12l31 : S := (0, [wireWord9, wireWord1, wireWord10, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l31Dead : optimized 5 r12l31.1 r12l31.2 = false := by decide +kernel
def r12l32 : S := (0, [wireWord42, wireWord1, wireWord10, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l32Dead : optimized 5 r12l32.1 r12l32.2 = false := by decide +kernel
def r12l33 : S := (0, [wireWord40, wireWord1, wireWord10, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l33Dead : optimized 5 r12l33.1 r12l33.2 = false := by decide +kernel
def r12l34 : S := (0, [wireWord39, wireWord1, wireWord10, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l34Dead : optimized 5 r12l34.1 r12l34.2 = false := by decide +kernel
def r12l35 : S := (1, [wireWord5, wireWord10, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l35Dead : optimized 5 r12l35.1 r12l35.2 = false := by decide +kernel
def r12l36 : S := (0, [wireWord5, wireWord2, wireWord10, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l36Dead : optimized 5 r12l36.1 r12l36.2 = false := by decide +kernel
def r12l37 : S := (0, [wireWord5, wireWord3, wireWord10, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l37Dead : optimized 5 r12l37.1 r12l37.2 = false := by decide +kernel
def r12l38 : S := (0, [wireWord7, wireWord2, wireWord10, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l38Dead : optimized 5 r12l38.1 r12l38.2 = false := by decide +kernel
def r12l39 : S := (0, [wireWord24, wireWord3, wireWord10, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r12l39Dead : optimized 5 r12l39.1 r12l39.2 = false := by decide +kernel
def r12l40 : S := (1, [wireWord6, wireWord10, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l40Dead : optimized 5 r12l40.1 r12l40.2 = false := by decide +kernel
def r12l41 : S := (0, [wireWord6, wireWord2, wireWord10, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l41Dead : optimized 5 r12l41.1 r12l41.2 = false := by decide +kernel
def r12l42 : S := (0, [wireWord6, wireWord4, wireWord10, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l42Dead : optimized 5 r12l42.1 r12l42.2 = false := by decide +kernel
def r12l43 : S := (0, [wireWord8, wireWord2, wireWord10, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l43Dead : optimized 5 r12l43.1 r12l43.2 = false := by decide +kernel
def r12l44 : S := (0, [wireWord25, wireWord4, wireWord10, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r12l44Dead : optimized 5 r12l44.1 r12l44.2 = false := by decide +kernel
theorem rootCell12Dead : optimized 6 rootCell12.1 rootCell12.2 = false := by
  have kids : nexts (rootCell12.1, rootCell12.2) = [r12l0,r12l1,r12l2,r12l3,r12l4,r12l5,r12l6,r12l7,r12l8,r12l9,r12l10,r12l11,r12l12,r12l13,r12l14,r12l15,r12l16,r12l17,r12l18,r12l19,r12l20,r12l21,r12l22,r12l23,r12l24,r12l25,r12l26,r12l27,r12l28,r12l29,r12l30,r12l31,r12l32,r12l33,r12l34,r12l35,r12l36,r12l37,r12l38,r12l39,r12l40,r12l41,r12l42,r12l43,r12l44] := by decide +kernel
  have stop : (rootCell12.2 == [goal] || rootCell12.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r12l0Dead, r12l1Dead, r12l2Dead, r12l3Dead, r12l4Dead, r12l5Dead, r12l6Dead, r12l7Dead, r12l8Dead, r12l9Dead, r12l10Dead, r12l11Dead, r12l12Dead, r12l13Dead, r12l14Dead, r12l15Dead, r12l16Dead, r12l17Dead, r12l18Dead, r12l19Dead, r12l20Dead, r12l21Dead, r12l22Dead, r12l23Dead, r12l24Dead, r12l25Dead, r12l26Dead, r12l27Dead, r12l28Dead, r12l29Dead, r12l30Dead, r12l31Dead, r12l32Dead, r12l33Dead, r12l34Dead, r12l35Dead, r12l36Dead, r12l37Dead, r12l38Dead, r12l39Dead, r12l40Dead, r12l41Dead, r12l42Dead, r12l43Dead, r12l44Dead]
def rootCell13 : S := (1, [wireWord30, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
def r13l0 : S := (1, [wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l0Dead : optimized 5 r13l0.1 r13l0.2 = false := by decide +kernel
def r13l1 : S := (0, [wireWord0, wireWord30, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l1Dead : optimized 5 r13l1.1 r13l1.2 = false := by decide +kernel
def r13l2 : S := (0, [wireWord0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l2Dead : optimized 5 r13l2.1 r13l2.2 = false := by decide +kernel
def r13l3 : S := (0, [wireWord30, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l3Dead : optimized 5 r13l3.1 r13l3.2 = false := by decide +kernel
def r13l4 : S := (0, [wireWord31, wireWord30, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l4Dead : optimized 5 r13l4.1 r13l4.2 = false := by decide +kernel
def r13l5 : S := (0, [wireWord31, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l5Dead : optimized 5 r13l5.1 r13l5.2 = false := by decide +kernel
def r13l6 : S := (0, [0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l6Dead : optimized 5 r13l6.1 r13l6.2 = false := by decide +kernel
def r13l7 : S := (1, [wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l7Dead : optimized 5 r13l7.1 r13l7.2 = false := by decide +kernel
def r13l8 : S := (0, [wireWord2, wireWord30, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l8Dead : optimized 5 r13l8.1 r13l8.2 = false := by decide +kernel
def r13l9 : S := (0, [wireWord2, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l9Dead : optimized 5 r13l9.1 r13l9.2 = false := by decide +kernel
def r13l10 : S := (0, [wireWord30, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l10Dead : optimized 5 r13l10.1 r13l10.2 = false := by decide +kernel
def r13l11 : S := (0, [wireWord12, wireWord30, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l11Dead : optimized 5 r13l11.1 r13l11.2 = false := by decide +kernel
def r13l12 : S := (0, [wireWord12, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l12Dead : optimized 5 r13l12.1 r13l12.2 = false := by decide +kernel
def r13l13 : S := (0, [0, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l13Dead : optimized 5 r13l13.1 r13l13.2 = false := by decide +kernel
def r13l14 : S := (1, [1070536041623355392, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l14Dead : optimized 5 r13l14.1 r13l14.2 = false := by decide +kernel
def r13l15 : S := (0, [1070536041623355392, wireWord30, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l15Dead : optimized 5 r13l15.1 r13l15.2 = false := by decide +kernel
def r13l16 : S := (0, [1070536041623355392, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l16Dead : optimized 5 r13l16.1 r13l16.2 = false := by decide +kernel
def r13l17 : S := (0, [4611686018410610687, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l17Dead : optimized 5 r13l17.1 r13l17.2 = false := by decide +kernel
def r13l18 : S := (1, [3541149976787252077, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l18Dead : optimized 5 r13l18.1 r13l18.2 = false := by decide +kernel
def r13l19 : S := (0, [3541149976787252077, wireWord30, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l19Dead : optimized 5 r13l19.1 r13l19.2 = false := by decide +kernel
def r13l20 : S := (0, [3541149976787252077, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l20Dead : optimized 5 r13l20.1 r13l20.2 = false := by decide +kernel
def r13l21 : S := (0, [3218, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l21Dead : optimized 5 r13l21.1 r13l21.2 = false := by decide +kernel
def r13l22 : S := (1, [1833976111034729228, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l22Dead : optimized 5 r13l22.1 r13l22.2 = false := by decide +kernel
def r13l23 : S := (0, [1833976111034729228, wireWord30, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l23Dead : optimized 5 r13l23.1 r13l23.2 = false := by decide +kernel
def r13l24 : S := (0, [1833976111034729228, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l24Dead : optimized 5 r13l24.1 r13l24.2 = false := by decide +kernel
def r13l25 : S := (0, [4611686018410610557, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l25Dead : optimized 5 r13l25.1 r13l25.2 = false := by decide +kernel
def r13l26 : S := (1, [2777709907375878241, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l26Dead : optimized 5 r13l26.1 r13l26.2 = false := by decide +kernel
def r13l27 : S := (0, [2777709907375878241, wireWord30, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l27Dead : optimized 5 r13l27.1 r13l27.2 = false := by decide +kernel
def r13l28 : S := (0, [2777709907375878241, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l28Dead : optimized 5 r13l28.1 r13l28.2 = false := by decide +kernel
def r13l29 : S := (0, [3088, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l29Dead : optimized 5 r13l29.1 r13l29.2 = false := by decide +kernel
def r13l30 : S := (1, [3133986303800509280, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l30Dead : optimized 5 r13l30.1 r13l30.2 = false := by decide +kernel
def r13l31 : S := (0, [3133986303800509280, wireWord30, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l31Dead : optimized 5 r13l31.1 r13l31.2 = false := by decide +kernel
def r13l32 : S := (0, [3133986303800509280, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l32Dead : optimized 5 r13l32.1 r13l32.2 = false := by decide +kernel
def r13l33 : S := (0, [4611686018410610669, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l33Dead : optimized 5 r13l33.1 r13l33.2 = false := by decide +kernel
def r13l34 : S := (1, [1477699714610098189, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l34Dead : optimized 5 r13l34.1 r13l34.2 = false := by decide +kernel
def r13l35 : S := (0, [1477699714610098189, wireWord30, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l35Dead : optimized 5 r13l35.1 r13l35.2 = false := by decide +kernel
def r13l36 : S := (0, [1477699714610098189, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l36Dead : optimized 5 r13l36.1 r13l36.2 = false := by decide +kernel
def r13l37 : S := (0, [3200, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l37Dead : optimized 5 r13l37.1 r13l37.2 = false := by decide +kernel
def r13l38 : S := (1, [wireWord10, wireWord30, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l38Dead : optimized 5 r13l38.1 r13l38.2 = false := by decide +kernel
def r13l39 : S := (0, [wireWord10, wireWord0, wireWord30, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l39Dead : optimized 5 r13l39.1 r13l39.2 = false := by decide +kernel
def r13l40 : S := (0, [wireWord10, wireWord2, wireWord30, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l40Dead : optimized 5 r13l40.1 r13l40.2 = false := by decide +kernel
def r13l41 : S := (0, [wireWord12, wireWord0, wireWord30, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l41Dead : optimized 5 r13l41.1 r13l41.2 = false := by decide +kernel
def r13l42 : S := (0, [wireWord31, wireWord2, wireWord30, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l42Dead : optimized 5 r13l42.1 r13l42.2 = false := by decide +kernel
def r13l43 : S := (0, [wireWord13, wireWord1, wireWord30, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l43Dead : optimized 5 r13l43.1 r13l43.2 = false := by decide +kernel
def r13l44 : S := (0, [wireWord11, wireWord1, wireWord30, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l44Dead : optimized 5 r13l44.1 r13l44.2 = false := by decide +kernel
def r13l45 : S := (0, [wireWord5, wireWord2, wireWord30, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l45Dead : optimized 5 r13l45.1 r13l45.2 = false := by decide +kernel
def r13l46 : S := (0, [wireWord7, wireWord2, wireWord30, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r13l46Dead : optimized 5 r13l46.1 r13l46.2 = false := by decide +kernel
def r13l47 : S := (0, [wireWord6, wireWord2, wireWord30, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l47Dead : optimized 5 r13l47.1 r13l47.2 = false := by decide +kernel
def r13l48 : S := (0, [wireWord8, wireWord2, wireWord30, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r13l48Dead : optimized 5 r13l48.1 r13l48.2 = false := by decide +kernel
theorem rootCell13Dead : optimized 6 rootCell13.1 rootCell13.2 = false := by
  have kids : nexts (rootCell13.1, rootCell13.2) = [r13l0,r13l1,r13l2,r13l3,r13l4,r13l5,r13l6,r13l7,r13l8,r13l9,r13l10,r13l11,r13l12,r13l13,r13l14,r13l15,r13l16,r13l17,r13l18,r13l19,r13l20,r13l21,r13l22,r13l23,r13l24,r13l25,r13l26,r13l27,r13l28,r13l29,r13l30,r13l31,r13l32,r13l33,r13l34,r13l35,r13l36,r13l37,r13l38,r13l39,r13l40,r13l41,r13l42,r13l43,r13l44,r13l45,r13l46,r13l47,r13l48] := by decide +kernel
  have stop : (rootCell13.2 == [goal] || rootCell13.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r13l0Dead, r13l1Dead, r13l2Dead, r13l3Dead, r13l4Dead, r13l5Dead, r13l6Dead, r13l7Dead, r13l8Dead, r13l9Dead, r13l10Dead, r13l11Dead, r13l12Dead, r13l13Dead, r13l14Dead, r13l15Dead, r13l16Dead, r13l17Dead, r13l18Dead, r13l19Dead, r13l20Dead, r13l21Dead, r13l22Dead, r13l23Dead, r13l24Dead, r13l25Dead, r13l26Dead, r13l27Dead, r13l28Dead, r13l29Dead, r13l30Dead, r13l31Dead, r13l32Dead, r13l33Dead, r13l34Dead, r13l35Dead, r13l36Dead, r13l37Dead, r13l38Dead, r13l39Dead, r13l40Dead, r13l41Dead, r13l42Dead, r13l43Dead, r13l44Dead, r13l45Dead, r13l46Dead, r13l47Dead, r13l48Dead]
def rootCell14 : S := (1, [wireWord12, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
def r14l0 : S := (0, [wireWord12, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l0Dead : optimized 5 r14l0.1 r14l0.2 = false := by decide +kernel
def r14l1 : S := (1, [wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l1Dead : optimized 5 r14l1.1 r14l1.2 = false := by decide +kernel
def r14l2 : S := (0, [wireWord0, wireWord12, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l2Dead : optimized 5 r14l2.1 r14l2.2 = false := by decide +kernel
def r14l3 : S := (0, [wireWord0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l3Dead : optimized 5 r14l3.1 r14l3.2 = false := by decide +kernel
def r14l4 : S := (0, [0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l4Dead : optimized 5 r14l4.1 r14l4.2 = false := by decide +kernel
def r14l5 : S := (0, [wireWord10, wireWord12, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l5Dead : optimized 5 r14l5.1 r14l5.2 = false := by decide +kernel
def r14l6 : S := (0, [wireWord10, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l6Dead : optimized 5 r14l6.1 r14l6.2 = false := by decide +kernel
def r14l7 : S := (0, [0, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l7Dead : optimized 5 r14l7.1 r14l7.2 = false := by decide +kernel
def r14l8 : S := (0, [wireWord30, wireWord12, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l8Dead : optimized 5 r14l8.1 r14l8.2 = false := by decide +kernel
def r14l9 : S := (0, [wireWord30, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l9Dead : optimized 5 r14l9.1 r14l9.2 = false := by decide +kernel
def r14l10 : S := (0, [wireWord12, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l10Dead : optimized 5 r14l10.1 r14l10.2 = false := by decide +kernel
def r14l11 : S := (1, [wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l11Dead : optimized 5 r14l11.1 r14l11.2 = false := by decide +kernel
def r14l12 : S := (0, [wireWord2, wireWord12, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l12Dead : optimized 5 r14l12.1 r14l12.2 = false := by decide +kernel
def r14l13 : S := (0, [wireWord2, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l13Dead : optimized 5 r14l13.1 r14l13.2 = false := by decide +kernel
def r14l14 : S := (0, [324262314939252736, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l14Dead : optimized 5 r14l14.1 r14l14.2 = false := by decide +kernel
def r14l15 : S := (0, [1070536041623359487, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l15Dead : optimized 5 r14l15.1 r14l15.2 = false := by decide +kernel
def r14l16 : S := (0, [877, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l16Dead : optimized 5 r14l16.1 r14l16.2 = false := by decide +kernel
def r14l17 : S := (0, [746273726684105874, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l17Dead : optimized 5 r14l17.1 r14l17.2 = false := by decide +kernel
def r14l18 : S := (0, [2791728743180, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l18Dead : optimized 5 r14l18.1 r14l18.2 = false := by decide +kernel
def r14l19 : S := (1, [2158235634245242749, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l19Dead : optimized 5 r14l19.1 r14l19.2 = false := by decide +kernel
def r14l20 : S := (0, [2158235634245242749, wireWord12, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l20Dead : optimized 5 r14l20.1 r14l20.2 = false := by decide +kernel
def r14l21 : S := (0, [2158235634245242749, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l21Dead : optimized 5 r14l21.1 r14l21.2 = false := by decide +kernel
def r14l22 : S := (0, [324259523210510433, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l22Dead : optimized 5 r14l22.1 r14l22.2 = false := by decide +kernel
def r14l23 : S := (1, [1833973319305989136, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l23Dead : optimized 5 r14l23.1 r14l23.2 = false := by decide +kernel
def r14l24 : S := (0, [1833973319305989136, wireWord12, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l24Dead : optimized 5 r14l24.1 r14l24.2 = false := by decide +kernel
def r14l25 : S := (0, [1833973319305989136, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l25Dead : optimized 5 r14l25.1 r14l25.2 = false := by decide +kernel
def r14l26 : S := (0, [3092376453984, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l26Dead : optimized 5 r14l26.1 r14l26.2 = false := by decide +kernel
def r14l27 : S := (1, [3458245526363312109, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l27Dead : optimized 5 r14l27.1 r14l27.2 = false := by decide +kernel
def r14l28 : S := (0, [3458245526363312109, wireWord12, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l28Dead : optimized 5 r14l28.1 r14l28.2 = false := by decide +kernel
def r14l29 : S := (0, [3458245526363312109, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l29Dead : optimized 5 r14l29.1 r14l29.2 = false := by decide +kernel
def r14l30 : S := (0, [324259222562799629, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l30Dead : optimized 5 r14l30.1 r14l30.2 = false := by decide +kernel
def r14l31 : S := (1, [3133983211424058496, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l31Dead : optimized 5 r14l31.1 r14l31.2 = false := by decide +kernel
def r14l32 : S := (0, [3133983211424058496, wireWord12, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l32Dead : optimized 5 r14l32.1 r14l32.2 = false := by decide +kernel
def r14l33 : S := (0, [3133983211424058496, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l33Dead : optimized 5 r14l33.1 r14l33.2 = false := by decide +kernel
def r14l34 : S := (0, [wireWord10, wireWord2, wireWord12, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l34Dead : optimized 5 r14l34.1 r14l34.2 = false := by decide +kernel
def r14l35 : S := (0, [wireWord30, wireWord0, wireWord12, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l35Dead : optimized 5 r14l35.1 r14l35.2 = false := by decide +kernel
def r14l36 : S := (1, [wireWord31, wireWord12, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l36Dead : optimized 5 r14l36.1 r14l36.2 = false := by decide +kernel
def r14l37 : S := (0, [wireWord31, wireWord0, wireWord12, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l37Dead : optimized 5 r14l37.1 r14l37.2 = false := by decide +kernel
def r14l38 : S := (0, [wireWord31, wireWord2, wireWord12, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l38Dead : optimized 5 r14l38.1 r14l38.2 = false := by decide +kernel
def r14l39 : S := (0, [wireWord40, wireWord1, wireWord12, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l39Dead : optimized 5 r14l39.1 r14l39.2 = false := by decide +kernel
def r14l40 : S := (0, [wireWord39, wireWord1, wireWord12, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l40Dead : optimized 5 r14l40.1 r14l40.2 = false := by decide +kernel
def r14l41 : S := (1, [wireWord5, wireWord12, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l41Dead : optimized 5 r14l41.1 r14l41.2 = false := by decide +kernel
def r14l42 : S := (0, [wireWord5, wireWord2, wireWord12, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l42Dead : optimized 5 r14l42.1 r14l42.2 = false := by decide +kernel
def r14l43 : S := (0, [wireWord5, wireWord3, wireWord12, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l43Dead : optimized 5 r14l43.1 r14l43.2 = false := by decide +kernel
def r14l44 : S := (0, [wireWord7, wireWord2, wireWord12, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l44Dead : optimized 5 r14l44.1 r14l44.2 = false := by decide +kernel
def r14l45 : S := (0, [wireWord24, wireWord3, wireWord12, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r14l45Dead : optimized 5 r14l45.1 r14l45.2 = false := by decide +kernel
def r14l46 : S := (1, [wireWord6, wireWord12, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l46Dead : optimized 5 r14l46.1 r14l46.2 = false := by decide +kernel
def r14l47 : S := (0, [wireWord6, wireWord2, wireWord12, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l47Dead : optimized 5 r14l47.1 r14l47.2 = false := by decide +kernel
def r14l48 : S := (0, [wireWord6, wireWord4, wireWord12, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l48Dead : optimized 5 r14l48.1 r14l48.2 = false := by decide +kernel
def r14l49 : S := (0, [wireWord8, wireWord2, wireWord12, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l49Dead : optimized 5 r14l49.1 r14l49.2 = false := by decide +kernel
def r14l50 : S := (0, [wireWord25, wireWord4, wireWord12, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r14l50Dead : optimized 5 r14l50.1 r14l50.2 = false := by decide +kernel
theorem rootCell14Dead : optimized 6 rootCell14.1 rootCell14.2 = false := by
  have kids : nexts (rootCell14.1, rootCell14.2) = [r14l0,r14l1,r14l2,r14l3,r14l4,r14l5,r14l6,r14l7,r14l8,r14l9,r14l10,r14l11,r14l12,r14l13,r14l14,r14l15,r14l16,r14l17,r14l18,r14l19,r14l20,r14l21,r14l22,r14l23,r14l24,r14l25,r14l26,r14l27,r14l28,r14l29,r14l30,r14l31,r14l32,r14l33,r14l34,r14l35,r14l36,r14l37,r14l38,r14l39,r14l40,r14l41,r14l42,r14l43,r14l44,r14l45,r14l46,r14l47,r14l48,r14l49,r14l50] := by decide +kernel
  have stop : (rootCell14.2 == [goal] || rootCell14.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r14l0Dead, r14l1Dead, r14l2Dead, r14l3Dead, r14l4Dead, r14l5Dead, r14l6Dead, r14l7Dead, r14l8Dead, r14l9Dead, r14l10Dead, r14l11Dead, r14l12Dead, r14l13Dead, r14l14Dead, r14l15Dead, r14l16Dead, r14l17Dead, r14l18Dead, r14l19Dead, r14l20Dead, r14l21Dead, r14l22Dead, r14l23Dead, r14l24Dead, r14l25Dead, r14l26Dead, r14l27Dead, r14l28Dead, r14l29Dead, r14l30Dead, r14l31Dead, r14l32Dead, r14l33Dead, r14l34Dead, r14l35Dead, r14l36Dead, r14l37Dead, r14l38Dead, r14l39Dead, r14l40Dead, r14l41Dead, r14l42Dead, r14l43Dead, r14l44Dead, r14l45Dead, r14l46Dead, r14l47Dead, r14l48Dead, r14l49Dead, r14l50Dead]
def rootCell15 : S := (1, [wireWord31, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
def r15l0 : S := (0, [0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l0Dead : optimized 5 r15l0.1 r15l0.2 = false := by decide +kernel
def r15l1 : S := (0, [wireWord30, wireWord31, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l1Dead : optimized 5 r15l1.1 r15l1.2 = false := by decide +kernel
def r15l2 : S := (0, [wireWord30, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l2Dead : optimized 5 r15l2.1 r15l2.2 = false := by decide +kernel
def r15l3 : S := (0, [wireWord31, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l3Dead : optimized 5 r15l3.1 r15l3.2 = false := by decide +kernel
def r15l4 : S := (1, [wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l4Dead : optimized 5 r15l4.1 r15l4.2 = false := by decide +kernel
def r15l5 : S := (0, [wireWord0, wireWord31, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l5Dead : optimized 5 r15l5.1 r15l5.2 = false := by decide +kernel
def r15l6 : S := (0, [wireWord0, wireWord0, wireWord2, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l6Dead : optimized 5 r15l6.1 r15l6.2 = false := by decide +kernel
def r15l7 : S := (0, [wireWord31, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l7Dead : optimized 5 r15l7.1 r15l7.2 = false := by decide +kernel
def r15l8 : S := (1, [wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l8Dead : optimized 5 r15l8.1 r15l8.2 = false := by decide +kernel
def r15l9 : S := (0, [wireWord2, wireWord31, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l9Dead : optimized 5 r15l9.1 r15l9.2 = false := by decide +kernel
def r15l10 : S := (0, [wireWord2, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l10Dead : optimized 5 r15l10.1 r15l10.2 = false := by decide +kernel
def r15l11 : S := (0, [0, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l11Dead : optimized 5 r15l11.1 r15l11.2 = false := by decide +kernel
def r15l12 : S := (0, [wireWord10, wireWord31, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l12Dead : optimized 5 r15l12.1 r15l12.2 = false := by decide +kernel
def r15l13 : S := (0, [wireWord10, wireWord2, wireWord0, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l13Dead : optimized 5 r15l13.1 r15l13.2 = false := by decide +kernel
def r15l14 : S := (0, [599546098980651008, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l14Dead : optimized 5 r15l14.1 r15l14.2 = false := by decide +kernel
def r15l15 : S := (0, [1070536042978708626, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l15Dead : optimized 5 r15l15.1 r15l15.2 = false := by decide +kernel
def r15l16 : S := (0, [1355350016, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l16Dead : optimized 5 r15l16.1 r15l16.2 = false := by decide +kernel
def r15l17 : S := (0, [470989942642707602, wireWord1, wireWord0, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l17Dead : optimized 5 r15l17.1 r15l17.2 = false := by decide +kernel
def r15l18 : S := (0, [wireWord52, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l18Dead : optimized 5 r15l18.1 r15l18.2 = false := by decide +kernel
def r15l19 : S := (0, [1833976111306870556, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l19Dead : optimized 5 r15l19.1 r15l19.2 = false := by decide +kernel
def r15l20 : S := (0, [wireWord50, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l20Dead : optimized 5 r15l20.1 r15l20.2 = false := by decide +kernel
def r15l21 : S := (0, [1234430010970869532, wireWord3, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l21Dead : optimized 5 r15l21.1 r15l21.2 = false := by decide +kernel
def r15l22 : S := (0, [wireWord56, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r15l22Dead : optimized 5 r15l22.1 r15l22.2 = false := by decide +kernel
def r15l23 : S := (0, [3133986304337874912, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r15l23Dead : optimized 5 r15l23.1 r15l23.2 = false := by decide +kernel
def r15l24 : S := (0, [wireWord54, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r15l24Dead : optimized 5 r15l24.1 r15l24.2 = false := by decide +kernel
def r15l25 : S := (0, [2534440204001873888, wireWord4, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r15l25Dead : optimized 5 r15l25.1 r15l25.2 = false := by decide +kernel
def r15l26 : S := (0, [wireWord10, wireWord0, wireWord31, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l26Dead : optimized 5 r15l26.1 r15l26.2 = false := by decide +kernel
def r15l27 : S := (0, [wireWord30, wireWord2, wireWord31, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l27Dead : optimized 5 r15l27.1 r15l27.2 = false := by decide +kernel
def r15l28 : S := (1, [wireWord12, wireWord31, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l28Dead : optimized 5 r15l28.1 r15l28.2 = false := by decide +kernel
def r15l29 : S := (0, [wireWord12, wireWord0, wireWord31, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l29Dead : optimized 5 r15l29.1 r15l29.2 = false := by decide +kernel
def r15l30 : S := (0, [wireWord12, wireWord2, wireWord31, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l30Dead : optimized 5 r15l30.1 r15l30.2 = false := by decide +kernel
def r15l31 : S := (0, [wireWord9, wireWord1, wireWord31, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l31Dead : optimized 5 r15l31.1 r15l31.2 = false := by decide +kernel
def r15l32 : S := (0, [wireWord42, wireWord1, wireWord31, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l32Dead : optimized 5 r15l32.1 r15l32.2 = false := by decide +kernel
def r15l33 : S := (0, [wireWord13, wireWord1, wireWord31, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l33Dead : optimized 5 r15l33.1 r15l33.2 = false := by decide +kernel
def r15l34 : S := (0, [wireWord11, wireWord1, wireWord31, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l34Dead : optimized 5 r15l34.1 r15l34.2 = false := by decide +kernel
def r15l35 : S := (0, [wireWord5, wireWord2, wireWord31, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l35Dead : optimized 5 r15l35.1 r15l35.2 = false := by decide +kernel
def r15l36 : S := (0, [wireWord7, wireWord2, wireWord31, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r15l36Dead : optimized 5 r15l36.1 r15l36.2 = false := by decide +kernel
def r15l37 : S := (0, [wireWord6, wireWord2, wireWord31, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r15l37Dead : optimized 5 r15l37.1 r15l37.2 = false := by decide +kernel
def r15l38 : S := (0, [wireWord8, wireWord2, wireWord31, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r15l38Dead : optimized 5 r15l38.1 r15l38.2 = false := by decide +kernel
theorem rootCell15Dead : optimized 6 rootCell15.1 rootCell15.2 = false := by
  have kids : nexts (rootCell15.1, rootCell15.2) = [r15l0,r15l1,r15l2,r15l3,r15l4,r15l5,r15l6,r15l7,r15l8,r15l9,r15l10,r15l11,r15l12,r15l13,r15l14,r15l15,r15l16,r15l17,r15l18,r15l19,r15l20,r15l21,r15l22,r15l23,r15l24,r15l25,r15l26,r15l27,r15l28,r15l29,r15l30,r15l31,r15l32,r15l33,r15l34,r15l35,r15l36,r15l37,r15l38] := by decide +kernel
  have stop : (rootCell15.2 == [goal] || rootCell15.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r15l0Dead, r15l1Dead, r15l2Dead, r15l3Dead, r15l4Dead, r15l5Dead, r15l6Dead, r15l7Dead, r15l8Dead, r15l9Dead, r15l10Dead, r15l11Dead, r15l12Dead, r15l13Dead, r15l14Dead, r15l15Dead, r15l16Dead, r15l17Dead, r15l18Dead, r15l19Dead, r15l20Dead, r15l21Dead, r15l22Dead, r15l23Dead, r15l24Dead, r15l25Dead, r15l26Dead, r15l27Dead, r15l28Dead, r15l29Dead, r15l30Dead, r15l31Dead, r15l32Dead, r15l33Dead, r15l34Dead, r15l35Dead, r15l36Dead, r15l37Dead, r15l38Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell16 : S := (1, [wireWord19, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
def r16l0 : S := (0, [wireWord19, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l0Dead : optimized 5 r16l0.1 r16l0.2 = false := by decide +kernel
def r16l1 : S := (1, [wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l1Dead : optimized 5 r16l1.1 r16l1.2 = false := by decide +kernel
def r16l2 : S := (0, [wireWord1, wireWord19, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l2Dead : optimized 5 r16l2.1 r16l2.2 = false := by decide +kernel
def r16l3 : S := (0, [wireWord1, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l3Dead : optimized 5 r16l3.1 r16l3.2 = false := by decide +kernel
def r16l4 : S := (0, [0, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l4Dead : optimized 5 r16l4.1 r16l4.2 = false := by decide +kernel
def r16l5 : S := (0, [wireWord27, wireWord19, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l5Dead : optimized 5 r16l5.1 r16l5.2 = false := by decide +kernel
def r16l6 : S := (0, [wireWord27, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l6Dead : optimized 5 r16l6.1 r16l6.2 = false := by decide +kernel
def r16l7 : S := (0, [wireWord19, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l7Dead : optimized 5 r16l7.1 r16l7.2 = false := by decide +kernel
def r16l8 : S := (1, [wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l8Dead : optimized 5 r16l8.1 r16l8.2 = false := by decide +kernel
def r16l9 : S := (0, [wireWord3, wireWord19, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l9Dead : optimized 5 r16l9.1 r16l9.2 = false := by decide +kernel
def r16l10 : S := (0, [wireWord3, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l10Dead : optimized 5 r16l10.1 r16l10.2 = false := by decide +kernel
def r16l11 : S := (0, [0, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l11Dead : optimized 5 r16l11.1 r16l11.2 = false := by decide +kernel
def r16l12 : S := (0, [wireWord20, wireWord19, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l12Dead : optimized 5 r16l12.1 r16l12.2 = false := by decide +kernel
def r16l13 : S := (0, [wireWord20, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l13Dead : optimized 5 r16l13.1 r16l13.2 = false := by decide +kernel
def r16l14 : S := (0, [284266705453056, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l14Dead : optimized 5 r16l14.1 r16l14.2 = false := by decide +kernel
def r16l15 : S := (0, [4611686017052082045, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l15Dead : optimized 5 r16l15.1 r16l15.2 = false := by decide +kernel
def r16l16 : S := (0, [599546098977475600, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l16Dead : optimized 5 r16l16.1 r16l16.2 = false := by decide +kernel
def r16l17 : S := (0, [4011855651369153389, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l17Dead : optimized 5 r16l17.1 r16l17.2 = false := by decide +kernel
def r16l18 : S := (0, [599548847219280896, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l18Dead : optimized 5 r16l18.1 r16l18.2 = false := by decide +kernel
def r16l19 : S := (0, [3134267822264160240, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l19Dead : optimized 5 r16l19.1 r16l19.2 = false := by decide +kernel
def r16l20 : S := (0, [281518463647760, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l20Dead : optimized 5 r16l20.1 r16l20.2 = false := by decide +kernel
def r16l21 : S := (0, [2534437456581231584, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l21Dead : optimized 5 r16l21.1 r16l21.2 = false := by decide +kernel
def r16l22 : S := (0, [wireWord57, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r16l22Dead : optimized 5 r16l22.1 r16l22.2 = false := by decide +kernel
def r16l23 : S := (0, [4287426495200099344, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r16l23Dead : optimized 5 r16l23.1 r16l23.2 = false := by decide +kernel
def r16l24 : S := (0, [2791728745488, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r16l24Dead : optimized 5 r16l24.1 r16l24.2 = false := by decide +kernel
def r16l25 : S := (0, [3687596129517170688, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r16l25Dead : optimized 5 r16l25.1 r16l25.2 = false := by decide +kernel
def r16l26 : S := (1, [wireWord35, wireWord19, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l26Dead : optimized 5 r16l26.1 r16l26.2 = false := by decide +kernel
def r16l27 : S := (0, [wireWord35, wireWord1, wireWord19, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l27Dead : optimized 5 r16l27.1 r16l27.2 = false := by decide +kernel
def r16l28 : S := (0, [wireWord35, wireWord3, wireWord19, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l28Dead : optimized 5 r16l28.1 r16l28.2 = false := by decide +kernel
def r16l29 : S := (0, [wireWord27, wireWord3, wireWord19, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l29Dead : optimized 5 r16l29.1 r16l29.2 = false := by decide +kernel
def r16l30 : S := (0, [wireWord20, wireWord1, wireWord19, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l30Dead : optimized 5 r16l30.1 r16l30.2 = false := by decide +kernel
def r16l31 : S := (0, [wireWord9, wireWord0, wireWord19, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l31Dead : optimized 5 r16l31.1 r16l31.2 = false := by decide +kernel
def r16l32 : S := (0, [wireWord26, wireWord0, wireWord19, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l32Dead : optimized 5 r16l32.1 r16l32.2 = false := by decide +kernel
def r16l33 : S := (0, [wireWord32, wireWord0, wireWord19, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l33Dead : optimized 5 r16l33.1 r16l33.2 = false := by decide +kernel
def r16l34 : S := (0, [wireWord33, wireWord0, wireWord19, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l34Dead : optimized 5 r16l34.1 r16l34.2 = false := by decide +kernel
def r16l35 : S := (0, [wireWord14, wireWord4, wireWord19, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l35Dead : optimized 5 r16l35.1 r16l35.2 = false := by decide +kernel
def r16l36 : S := (0, [wireWord17, wireWord4, wireWord19, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r16l36Dead : optimized 5 r16l36.1 r16l36.2 = false := by decide +kernel
def r16l37 : S := (0, [wireWord5, wireWord2, wireWord19, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r16l37Dead : optimized 5 r16l37.1 r16l37.2 = false := by decide +kernel
def r16l38 : S := (0, [wireWord7, wireWord2, wireWord19, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r16l38Dead : optimized 5 r16l38.1 r16l38.2 = false := by decide +kernel
def r16l39 : S := (0, [wireWord6, wireWord2, wireWord19, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r16l39Dead : optimized 5 r16l39.1 r16l39.2 = false := by decide +kernel
def r16l40 : S := (0, [wireWord8, wireWord2, wireWord19, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r16l40Dead : optimized 5 r16l40.1 r16l40.2 = false := by decide +kernel
theorem rootCell16Dead : optimized 6 rootCell16.1 rootCell16.2 = false := by
  have kids : nexts (rootCell16.1, rootCell16.2) = [r16l0,r16l1,r16l2,r16l3,r16l4,r16l5,r16l6,r16l7,r16l8,r16l9,r16l10,r16l11,r16l12,r16l13,r16l14,r16l15,r16l16,r16l17,r16l18,r16l19,r16l20,r16l21,r16l22,r16l23,r16l24,r16l25,r16l26,r16l27,r16l28,r16l29,r16l30,r16l31,r16l32,r16l33,r16l34,r16l35,r16l36,r16l37,r16l38,r16l39,r16l40] := by decide +kernel
  have stop : (rootCell16.2 == [goal] || rootCell16.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r16l0Dead, r16l1Dead, r16l2Dead, r16l3Dead, r16l4Dead, r16l5Dead, r16l6Dead, r16l7Dead, r16l8Dead, r16l9Dead, r16l10Dead, r16l11Dead, r16l12Dead, r16l13Dead, r16l14Dead, r16l15Dead, r16l16Dead, r16l17Dead, r16l18Dead, r16l19Dead, r16l20Dead, r16l21Dead, r16l22Dead, r16l23Dead, r16l24Dead, r16l25Dead, r16l26Dead, r16l27Dead, r16l28Dead, r16l29Dead, r16l30Dead, r16l31Dead, r16l32Dead, r16l33Dead, r16l34Dead, r16l35Dead, r16l36Dead, r16l37Dead, r16l38Dead, r16l39Dead, r16l40Dead]
def rootCell17 : S := (1, [wireWord35, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
def r17l0 : S := (1, [wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l0Dead : optimized 5 r17l0.1 r17l0.2 = false := by decide +kernel
def r17l1 : S := (0, [wireWord1, wireWord35, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l1Dead : optimized 5 r17l1.1 r17l1.2 = false := by decide +kernel
def r17l2 : S := (0, [wireWord1, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l2Dead : optimized 5 r17l2.1 r17l2.2 = false := by decide +kernel
def r17l3 : S := (0, [wireWord35, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l3Dead : optimized 5 r17l3.1 r17l3.2 = false := by decide +kernel
def r17l4 : S := (0, [wireWord20, wireWord35, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l4Dead : optimized 5 r17l4.1 r17l4.2 = false := by decide +kernel
def r17l5 : S := (0, [wireWord20, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l5Dead : optimized 5 r17l5.1 r17l5.2 = false := by decide +kernel
def r17l6 : S := (0, [0, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l6Dead : optimized 5 r17l6.1 r17l6.2 = false := by decide +kernel
def r17l7 : S := (1, [wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l7Dead : optimized 5 r17l7.1 r17l7.2 = false := by decide +kernel
def r17l8 : S := (0, [wireWord3, wireWord35, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l8Dead : optimized 5 r17l8.1 r17l8.2 = false := by decide +kernel
def r17l9 : S := (0, [wireWord3, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l9Dead : optimized 5 r17l9.1 r17l9.2 = false := by decide +kernel
def r17l10 : S := (0, [wireWord35, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l10Dead : optimized 5 r17l10.1 r17l10.2 = false := by decide +kernel
def r17l11 : S := (0, [wireWord27, wireWord35, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l11Dead : optimized 5 r17l11.1 r17l11.2 = false := by decide +kernel
def r17l12 : S := (0, [wireWord27, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l12Dead : optimized 5 r17l12.1 r17l12.2 = false := by decide +kernel
def r17l13 : S := (0, [0, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l13Dead : optimized 5 r17l13.1 r17l13.2 = false := by decide +kernel
def r17l14 : S := (0, [1705135686908117772, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l14Dead : optimized 5 r17l14.1 r17l14.2 = false := by decide +kernel
def r17l15 : S := (0, [4611686018141650943, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l15Dead : optimized 5 r17l15.1 r17l15.2 = false := by decide +kernel
def r17l16 : S := (0, [599546100067044498, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l16Dead : optimized 5 r17l16.1 r17l16.2 = false := by decide +kernel
def r17l17 : S := (0, [2307004231166488673, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l17Dead : optimized 5 r17l17.1 r17l17.2 = false := by decide +kernel
def r17l18 : S := (0, [826982072599973760, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l18Dead : optimized 5 r17l18.1 r17l18.2 = false := by decide +kernel
def r17l19 : S := (0, [4611686018175700990, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l19Dead : optimized 5 r17l19.1 r17l19.2 = false := by decide +kernel
def r17l20 : S := (0, [1477699714375188510, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l20Dead : optimized 5 r17l20.1 r17l20.2 = false := by decide +kernel
def r17l21 : S := (0, [2307004231200538720, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l21Dead : optimized 5 r17l21.1 r17l21.2 = false := by decide +kernel
def r17l22 : S := (0, [1980419472035905536, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r17l22Dead : optimized 5 r17l22.1 r17l22.2 = false := by decide +kernel
def r17l23 : S := (0, [4611686018410610590, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r17l23Dead : optimized 5 r17l23.1 r17l23.2 = false := by decide +kernel
def r17l24 : S := (0, [324262314939256734, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r17l24Dead : optimized 5 r17l24.1 r17l24.2 = false := by decide +kernel
def r17l25 : S := (0, [wireWord58, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r17l25Dead : optimized 5 r17l25.1 r17l25.2 = false := by decide +kernel
def r17l26 : S := (1, [wireWord19, wireWord35, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l26Dead : optimized 5 r17l26.1 r17l26.2 = false := by decide +kernel
def r17l27 : S := (0, [wireWord19, wireWord1, wireWord35, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l27Dead : optimized 5 r17l27.1 r17l27.2 = false := by decide +kernel
def r17l28 : S := (0, [wireWord19, wireWord3, wireWord35, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l28Dead : optimized 5 r17l28.1 r17l28.2 = false := by decide +kernel
def r17l29 : S := (0, [wireWord27, wireWord1, wireWord35, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l29Dead : optimized 5 r17l29.1 r17l29.2 = false := by decide +kernel
def r17l30 : S := (0, [wireWord20, wireWord3, wireWord35, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l30Dead : optimized 5 r17l30.1 r17l30.2 = false := by decide +kernel
def r17l31 : S := (0, [wireWord23, wireWord0, wireWord35, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l31Dead : optimized 5 r17l31.1 r17l31.2 = false := by decide +kernel
def r17l32 : S := (0, [wireWord34, wireWord0, wireWord35, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l32Dead : optimized 5 r17l32.1 r17l32.2 = false := by decide +kernel
def r17l33 : S := (0, [wireWord15, wireWord4, wireWord35, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l33Dead : optimized 5 r17l33.1 r17l33.2 = false := by decide +kernel
def r17l34 : S := (0, [wireWord16, wireWord4, wireWord35, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r17l34Dead : optimized 5 r17l34.1 r17l34.2 = false := by decide +kernel
def r17l35 : S := (0, [wireWord5, wireWord2, wireWord35, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r17l35Dead : optimized 5 r17l35.1 r17l35.2 = false := by decide +kernel
def r17l36 : S := (0, [wireWord7, wireWord2, wireWord35, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r17l36Dead : optimized 5 r17l36.1 r17l36.2 = false := by decide +kernel
def r17l37 : S := (0, [wireWord6, wireWord2, wireWord35, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r17l37Dead : optimized 5 r17l37.1 r17l37.2 = false := by decide +kernel
def r17l38 : S := (0, [wireWord8, wireWord2, wireWord35, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r17l38Dead : optimized 5 r17l38.1 r17l38.2 = false := by decide +kernel
theorem rootCell17Dead : optimized 6 rootCell17.1 rootCell17.2 = false := by
  have kids : nexts (rootCell17.1, rootCell17.2) = [r17l0,r17l1,r17l2,r17l3,r17l4,r17l5,r17l6,r17l7,r17l8,r17l9,r17l10,r17l11,r17l12,r17l13,r17l14,r17l15,r17l16,r17l17,r17l18,r17l19,r17l20,r17l21,r17l22,r17l23,r17l24,r17l25,r17l26,r17l27,r17l28,r17l29,r17l30,r17l31,r17l32,r17l33,r17l34,r17l35,r17l36,r17l37,r17l38] := by decide +kernel
  have stop : (rootCell17.2 == [goal] || rootCell17.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r17l0Dead, r17l1Dead, r17l2Dead, r17l3Dead, r17l4Dead, r17l5Dead, r17l6Dead, r17l7Dead, r17l8Dead, r17l9Dead, r17l10Dead, r17l11Dead, r17l12Dead, r17l13Dead, r17l14Dead, r17l15Dead, r17l16Dead, r17l17Dead, r17l18Dead, r17l19Dead, r17l20Dead, r17l21Dead, r17l22Dead, r17l23Dead, r17l24Dead, r17l25Dead, r17l26Dead, r17l27Dead, r17l28Dead, r17l29Dead, r17l30Dead, r17l31Dead, r17l32Dead, r17l33Dead, r17l34Dead, r17l35Dead, r17l36Dead, r17l37Dead, r17l38Dead]
def rootCell18 : S := (1, [wireWord27, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
def r18l0 : S := (0, [wireWord27, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l0Dead : optimized 5 r18l0.1 r18l0.2 = false := by decide +kernel
def r18l1 : S := (1, [wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l1Dead : optimized 5 r18l1.1 r18l1.2 = false := by decide +kernel
def r18l2 : S := (0, [wireWord1, wireWord27, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l2Dead : optimized 5 r18l2.1 r18l2.2 = false := by decide +kernel
def r18l3 : S := (0, [wireWord1, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l3Dead : optimized 5 r18l3.1 r18l3.2 = false := by decide +kernel
def r18l4 : S := (0, [0, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l4Dead : optimized 5 r18l4.1 r18l4.2 = false := by decide +kernel
def r18l5 : S := (0, [wireWord19, wireWord27, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l5Dead : optimized 5 r18l5.1 r18l5.2 = false := by decide +kernel
def r18l6 : S := (0, [wireWord19, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l6Dead : optimized 5 r18l6.1 r18l6.2 = false := by decide +kernel
def r18l7 : S := (0, [0, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l7Dead : optimized 5 r18l7.1 r18l7.2 = false := by decide +kernel
def r18l8 : S := (0, [wireWord35, wireWord27, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l8Dead : optimized 5 r18l8.1 r18l8.2 = false := by decide +kernel
def r18l9 : S := (0, [wireWord35, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l9Dead : optimized 5 r18l9.1 r18l9.2 = false := by decide +kernel
def r18l10 : S := (0, [wireWord27, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l10Dead : optimized 5 r18l10.1 r18l10.2 = false := by decide +kernel
def r18l11 : S := (1, [wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l11Dead : optimized 5 r18l11.1 r18l11.2 = false := by decide +kernel
def r18l12 : S := (0, [wireWord3, wireWord27, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l12Dead : optimized 5 r18l12.1 r18l12.2 = false := by decide +kernel
def r18l13 : S := (0, [wireWord3, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l13Dead : optimized 5 r18l13.1 r18l13.2 = false := by decide +kernel
def r18l14 : S := (0, [470705675937251328, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l14Dead : optimized 5 r18l14.1 r18l14.2 = false := by decide +kernel
def r18l15 : S := (0, [4012139918077785071, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l15Dead : optimized 5 r18l15.1 r18l15.2 = false := by decide +kernel
def r18l16 : S := (0, [3178626, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l16Dead : optimized 5 r18l16.1 r18l16.2 = false := by decide +kernel
def r18l17 : S := (0, [3541434242137355117, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l17Dead : optimized 5 r18l17.1 r18l17.2 = false := by decide +kernel
def r18l18 : S := (0, [146367331490070656, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l18Dead : optimized 5 r18l18.1 r18l18.2 = false := by decide +kernel
def r18l19 : S := (1, [3458324648250871778, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l19Dead : optimized 5 r18l19.1 r18l19.2 = false := by decide +kernel
def r18l20 : S := (0, [3458324648250871778, wireWord27, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l20Dead : optimized 5 r18l20.1 r18l20.2 = false := by decide +kernel
def r18l21 : S := (0, [3458324648250871778, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l21Dead : optimized 5 r18l21.1 r18l21.2 = false := by decide +kernel
def r18l22 : S := (0, [324338344450359298, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l22Dead : optimized 5 r18l22.1 r18l22.2 = false := by decide +kernel
def r18l23 : S := (1, [2987618972310441824, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l23Dead : optimized 5 r18l23.1 r18l23.2 = false := by decide +kernel
def r18l24 : S := (0, [2987618972310441824, wireWord27, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l24Dead : optimized 5 r18l24.1 r18l24.2 = false := by decide +kernel
def r18l25 : S := (0, [2987618972310441824, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l25Dead : optimized 5 r18l25.1 r18l25.2 = false := by decide +kernel
def r18l26 : S := (0, [wireWord59, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l26Dead : optimized 5 r18l26.1 r18l26.2 = false := by decide +kernel
def r18l27 : S := (1, [4611683226681864322, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l27Dead : optimized 5 r18l27.1 r18l27.2 = false := by decide +kernel
def r18l28 : S := (0, [4611683226681864322, wireWord27, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l28Dead : optimized 5 r18l28.1 r18l28.2 = false := by decide +kernel
def r18l29 : S := (0, [4611683226681864322, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l29Dead : optimized 5 r18l29.1 r18l29.2 = false := by decide +kernel
def r18l30 : S := (0, [324259523210510466, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l30Dead : optimized 5 r18l30.1 r18l30.2 = false := by decide +kernel
def r18l31 : S := (1, [4140977550741434368, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l31Dead : optimized 5 r18l31.1 r18l31.2 = false := by decide +kernel
def r18l32 : S := (0, [4140977550741434368, wireWord27, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l32Dead : optimized 5 r18l32.1 r18l32.2 = false := by decide +kernel
def r18l33 : S := (0, [4140977550741434368, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l33Dead : optimized 5 r18l33.1 r18l33.2 = false := by decide +kernel
def r18l34 : S := (0, [wireWord19, wireWord3, wireWord27, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l34Dead : optimized 5 r18l34.1 r18l34.2 = false := by decide +kernel
def r18l35 : S := (0, [wireWord35, wireWord1, wireWord27, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l35Dead : optimized 5 r18l35.1 r18l35.2 = false := by decide +kernel
def r18l36 : S := (0, [wireWord20, wireWord1, wireWord27, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l36Dead : optimized 5 r18l36.1 r18l36.2 = false := by decide +kernel
def r18l37 : S := (0, [wireWord20, wireWord3, wireWord27, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l37Dead : optimized 5 r18l37.1 r18l37.2 = false := by decide +kernel
def r18l38 : S := (0, [wireWord32, wireWord0, wireWord27, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l38Dead : optimized 5 r18l38.1 r18l38.2 = false := by decide +kernel
def r18l39 : S := (0, [wireWord33, wireWord0, wireWord27, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l39Dead : optimized 5 r18l39.1 r18l39.2 = false := by decide +kernel
def r18l40 : S := (0, [wireWord14, wireWord4, wireWord27, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l40Dead : optimized 5 r18l40.1 r18l40.2 = false := by decide +kernel
def r18l41 : S := (0, [wireWord17, wireWord4, wireWord27, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r18l41Dead : optimized 5 r18l41.1 r18l41.2 = false := by decide +kernel
def r18l42 : S := (0, [wireWord5, wireWord2, wireWord27, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l42Dead : optimized 5 r18l42.1 r18l42.2 = false := by decide +kernel
def r18l43 : S := (0, [wireWord7, wireWord2, wireWord27, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r18l43Dead : optimized 5 r18l43.1 r18l43.2 = false := by decide +kernel
def r18l44 : S := (0, [wireWord6, wireWord2, wireWord27, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r18l44Dead : optimized 5 r18l44.1 r18l44.2 = false := by decide +kernel
def r18l45 : S := (0, [wireWord8, wireWord2, wireWord27, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r18l45Dead : optimized 5 r18l45.1 r18l45.2 = false := by decide +kernel
theorem rootCell18Dead : optimized 6 rootCell18.1 rootCell18.2 = false := by
  have kids : nexts (rootCell18.1, rootCell18.2) = [r18l0,r18l1,r18l2,r18l3,r18l4,r18l5,r18l6,r18l7,r18l8,r18l9,r18l10,r18l11,r18l12,r18l13,r18l14,r18l15,r18l16,r18l17,r18l18,r18l19,r18l20,r18l21,r18l22,r18l23,r18l24,r18l25,r18l26,r18l27,r18l28,r18l29,r18l30,r18l31,r18l32,r18l33,r18l34,r18l35,r18l36,r18l37,r18l38,r18l39,r18l40,r18l41,r18l42,r18l43,r18l44,r18l45] := by decide +kernel
  have stop : (rootCell18.2 == [goal] || rootCell18.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r18l0Dead, r18l1Dead, r18l2Dead, r18l3Dead, r18l4Dead, r18l5Dead, r18l6Dead, r18l7Dead, r18l8Dead, r18l9Dead, r18l10Dead, r18l11Dead, r18l12Dead, r18l13Dead, r18l14Dead, r18l15Dead, r18l16Dead, r18l17Dead, r18l18Dead, r18l19Dead, r18l20Dead, r18l21Dead, r18l22Dead, r18l23Dead, r18l24Dead, r18l25Dead, r18l26Dead, r18l27Dead, r18l28Dead, r18l29Dead, r18l30Dead, r18l31Dead, r18l32Dead, r18l33Dead, r18l34Dead, r18l35Dead, r18l36Dead, r18l37Dead, r18l38Dead, r18l39Dead, r18l40Dead, r18l41Dead, r18l42Dead, r18l43Dead, r18l44Dead, r18l45Dead]
def rootCell19 : S := (1, [wireWord20, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
def r19l0 : S := (0, [0, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l0Dead : optimized 5 r19l0.1 r19l0.2 = false := by decide +kernel
def r19l1 : S := (0, [wireWord35, wireWord20, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l1Dead : optimized 5 r19l1.1 r19l1.2 = false := by decide +kernel
def r19l2 : S := (0, [wireWord35, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l2Dead : optimized 5 r19l2.1 r19l2.2 = false := by decide +kernel
def r19l3 : S := (0, [wireWord20, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l3Dead : optimized 5 r19l3.1 r19l3.2 = false := by decide +kernel
def r19l4 : S := (1, [wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l4Dead : optimized 5 r19l4.1 r19l4.2 = false := by decide +kernel
def r19l5 : S := (0, [wireWord1, wireWord20, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l5Dead : optimized 5 r19l5.1 r19l5.2 = false := by decide +kernel
def r19l6 : S := (0, [wireWord1, wireWord1, wireWord3, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l6Dead : optimized 5 r19l6.1 r19l6.2 = false := by decide +kernel
def r19l7 : S := (0, [wireWord20, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l7Dead : optimized 5 r19l7.1 r19l7.2 = false := by decide +kernel
def r19l8 : S := (1, [wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l8Dead : optimized 5 r19l8.1 r19l8.2 = false := by decide +kernel
def r19l9 : S := (0, [wireWord3, wireWord20, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l9Dead : optimized 5 r19l9.1 r19l9.2 = false := by decide +kernel
def r19l10 : S := (0, [wireWord3, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l10Dead : optimized 5 r19l10.1 r19l10.2 = false := by decide +kernel
def r19l11 : S := (0, [0, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l11Dead : optimized 5 r19l11.1 r19l11.2 = false := by decide +kernel
def r19l12 : S := (0, [wireWord19, wireWord20, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l12Dead : optimized 5 r19l12.1 r19l12.2 = false := by decide +kernel
def r19l13 : S := (0, [wireWord19, wireWord3, wireWord1, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l13Dead : optimized 5 r19l13.1 r19l13.2 = false := by decide +kernel
def r19l14 : S := (0, [1234145744265413388, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l14Dead : optimized 5 r19l14.1 r19l14.2 = false := by decide +kernel
def r19l15 : S := (0, [4012139919160996717, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l15Dead : optimized 5 r19l15.1 r19l15.2 = false := by decide +kernel
def r19l16 : S := (0, [1086390272, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l16Dead : optimized 5 r19l16.1 r19l16.2 = false := by decide +kernel
def r19l17 : S := (0, [2777994173809193057, wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l17Dead : optimized 5 r19l17.1 r19l17.2 = false := by decide +kernel
def r19l18 : S := (0, [81065893890622208, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l18Dead : optimized 5 r19l18.1 r19l18.2 = false := by decide +kernel
def r19l19 : S := (1, [4287066155261693932, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l19Dead : optimized 5 r19l19.1 r19l19.2 = false := by decide +kernel
def r19l20 : S := (0, [4287066155261693932, wireWord20, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l20Dead : optimized 5 r19l20.1 r19l20.2 = false := by decide +kernel
def r19l21 : S := (0, [4287066155261693932, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l21Dead : optimized 5 r19l21.1 r19l21.2 = false := by decide +kernel
def r19l22 : S := (0, [1153079851461181452, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l22Dead : optimized 5 r19l22.1 r19l22.2 = false := by decide +kernel
def r19l23 : S := (1, [3052920409909890272, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l23Dead : optimized 5 r19l23.1 r19l23.2 = false := by decide +kernel
def r19l24 : S := (0, [3052920409909890272, wireWord20, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l24Dead : optimized 5 r19l24.1 r19l24.2 = false := by decide +kernel
def r19l25 : S := (0, [3052920409909890272, wireWord4, wireWord1, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l25Dead : optimized 5 r19l25.1 r19l25.2 = false := by decide +kernel
def r19l26 : S := (0, [wireWord60, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r19l26Dead : optimized 5 r19l26.1 r19l26.2 = false := by decide +kernel
def r19l27 : S := (0, [4287423703471354636, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r19l27Dead : optimized 5 r19l27.1 r19l27.2 = false := by decide +kernel
def r19l28 : S := (0, [780, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r19l28Dead : optimized 5 r19l28.1 r19l28.2 = false := by decide +kernel
def r19l29 : S := (0, [3053277958119550976, wireWord2, wireWord1, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r19l29Dead : optimized 5 r19l29.1 r19l29.2 = false := by decide +kernel
def r19l30 : S := (0, [wireWord19, wireWord1, wireWord20, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l30Dead : optimized 5 r19l30.1 r19l30.2 = false := by decide +kernel
def r19l31 : S := (0, [wireWord35, wireWord3, wireWord20, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l31Dead : optimized 5 r19l31.1 r19l31.2 = false := by decide +kernel
def r19l32 : S := (0, [wireWord27, wireWord1, wireWord20, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l32Dead : optimized 5 r19l32.1 r19l32.2 = false := by decide +kernel
def r19l33 : S := (0, [wireWord27, wireWord3, wireWord20, wireWord0, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l33Dead : optimized 5 r19l33.1 r19l33.2 = false := by decide +kernel
def r19l34 : S := (0, [wireWord9, wireWord0, wireWord20, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l34Dead : optimized 5 r19l34.1 r19l34.2 = false := by decide +kernel
def r19l35 : S := (0, [wireWord26, wireWord0, wireWord20, wireWord3, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l35Dead : optimized 5 r19l35.1 r19l35.2 = false := by decide +kernel
def r19l36 : S := (0, [wireWord23, wireWord0, wireWord20, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l36Dead : optimized 5 r19l36.1 r19l36.2 = false := by decide +kernel
def r19l37 : S := (0, [wireWord34, wireWord0, wireWord20, wireWord1, wireWord4, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l37Dead : optimized 5 r19l37.1 r19l37.2 = false := by decide +kernel
def r19l38 : S := (0, [wireWord15, wireWord4, wireWord20, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l38Dead : optimized 5 r19l38.1 r19l38.2 = false := by decide +kernel
def r19l39 : S := (0, [wireWord16, wireWord4, wireWord20, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r19l39Dead : optimized 5 r19l39.1 r19l39.2 = false := by decide +kernel
def r19l40 : S := (0, [wireWord5, wireWord2, wireWord20, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r19l40Dead : optimized 5 r19l40.1 r19l40.2 = false := by decide +kernel
def r19l41 : S := (0, [wireWord7, wireWord2, wireWord20, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r19l41Dead : optimized 5 r19l41.1 r19l41.2 = false := by decide +kernel
def r19l42 : S := (0, [wireWord6, wireWord2, wireWord20, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r19l42Dead : optimized 5 r19l42.1 r19l42.2 = false := by decide +kernel
def r19l43 : S := (0, [wireWord8, wireWord2, wireWord20, wireWord1, wireWord3, wireWord0])
set_option maxHeartbeats 0 in
theorem r19l43Dead : optimized 5 r19l43.1 r19l43.2 = false := by decide +kernel
theorem rootCell19Dead : optimized 6 rootCell19.1 rootCell19.2 = false := by
  have kids : nexts (rootCell19.1, rootCell19.2) = [r19l0,r19l1,r19l2,r19l3,r19l4,r19l5,r19l6,r19l7,r19l8,r19l9,r19l10,r19l11,r19l12,r19l13,r19l14,r19l15,r19l16,r19l17,r19l18,r19l19,r19l20,r19l21,r19l22,r19l23,r19l24,r19l25,r19l26,r19l27,r19l28,r19l29,r19l30,r19l31,r19l32,r19l33,r19l34,r19l35,r19l36,r19l37,r19l38,r19l39,r19l40,r19l41,r19l42,r19l43] := by decide +kernel
  have stop : (rootCell19.2 == [goal] || rootCell19.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r19l0Dead, r19l1Dead, r19l2Dead, r19l3Dead, r19l4Dead, r19l5Dead, r19l6Dead, r19l7Dead, r19l8Dead, r19l9Dead, r19l10Dead, r19l11Dead, r19l12Dead, r19l13Dead, r19l14Dead, r19l15Dead, r19l16Dead, r19l17Dead, r19l18Dead, r19l19Dead, r19l20Dead, r19l21Dead, r19l22Dead, r19l23Dead, r19l24Dead, r19l25Dead, r19l26Dead, r19l27Dead, r19l28Dead, r19l29Dead, r19l30Dead, r19l31Dead, r19l32Dead, r19l33Dead, r19l34Dead, r19l35Dead, r19l36Dead, r19l37Dead, r19l38Dead, r19l39Dead, r19l40Dead, r19l41Dead, r19l42Dead, r19l43Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell20 : S := (1, [wireWord21, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
def r20l0 : S := (0, [wireWord21, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l0Dead : optimized 5 r20l0.1 r20l0.2 = false := by decide +kernel
def r20l1 : S := (1, [wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l1Dead : optimized 5 r20l1.1 r20l1.2 = false := by decide +kernel
def r20l2 : S := (0, [wireWord1, wireWord21, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l2Dead : optimized 5 r20l2.1 r20l2.2 = false := by decide +kernel
def r20l3 : S := (0, [wireWord1, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l3Dead : optimized 5 r20l3.1 r20l3.2 = false := by decide +kernel
def r20l4 : S := (0, [0, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l4Dead : optimized 5 r20l4.1 r20l4.2 = false := by decide +kernel
def r20l5 : S := (0, [wireWord29, wireWord21, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l5Dead : optimized 5 r20l5.1 r20l5.2 = false := by decide +kernel
def r20l6 : S := (0, [wireWord29, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l6Dead : optimized 5 r20l6.1 r20l6.2 = false := by decide +kernel
def r20l7 : S := (0, [wireWord21, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l7Dead : optimized 5 r20l7.1 r20l7.2 = false := by decide +kernel
def r20l8 : S := (1, [wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l8Dead : optimized 5 r20l8.1 r20l8.2 = false := by decide +kernel
def r20l9 : S := (0, [wireWord4, wireWord21, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l9Dead : optimized 5 r20l9.1 r20l9.2 = false := by decide +kernel
def r20l10 : S := (0, [wireWord4, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l10Dead : optimized 5 r20l10.1 r20l10.2 = false := by decide +kernel
def r20l11 : S := (0, [0, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l11Dead : optimized 5 r20l11.1 r20l11.2 = false := by decide +kernel
def r20l12 : S := (0, [wireWord22, wireWord21, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l12Dead : optimized 5 r20l12.1 r20l12.2 = false := by decide +kernel
def r20l13 : S := (0, [wireWord22, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l13Dead : optimized 5 r20l13.1 r20l13.2 = false := by decide +kernel
def r20l14 : S := (0, [146370080265994240, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l14Dead : optimized 5 r20l14.1 r20l14.2 = false := by decide +kernel
def r20l15 : S := (0, [4611686016517963757, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l15Dead : optimized 5 r20l15.1 r20l15.2 = false := by decide +kernel
def r20l16 : S := (0, [599546098443357312, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l16Dead : optimized 5 r20l16.1 r20l16.2 = false := by decide +kernel
def r20l17 : S := (0, [3865769837808612205, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l17Dead : optimized 5 r20l17.1 r20l17.2 = false := by decide +kernel
def r20l18 : S := (0, [599548847219280896, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l18Dead : optimized 5 r20l18.1 r20l18.2 = false := by decide +kernel
def r20l19 : S := (0, [1980343442524802972, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l19Dead : optimized 5 r20l19.1 r20l19.2 = false := by decide +kernel
def r20l20 : S := (0, [146367331490070656, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l20Dead : optimized 5 r20l20.1 r20l20.2 = false := by decide +kernel
def r20l21 : S := (0, [1234427263815451420, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l21Dead : optimized 5 r20l21.1 r20l21.2 = false := by decide +kernel
def r20l22 : S := (0, [wireWord61, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r20l22Dead : optimized 5 r20l22.1 r20l22.2 = false := by decide +kernel
def r20l23 : S := (0, [4287426795847810176, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r20l23Dead : optimized 5 r20l23.1 r20l23.2 = false := by decide +kernel
def r20l24 : S := (0, [3092376456320, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r20l24Dead : optimized 5 r20l24.1 r20l24.2 = false := by decide +kernel
def r20l25 : S := (0, [3541510617138458624, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r20l25Dead : optimized 5 r20l25.1 r20l25.2 = false := by decide +kernel
def r20l26 : S := (1, [wireWord38, wireWord21, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l26Dead : optimized 5 r20l26.1 r20l26.2 = false := by decide +kernel
def r20l27 : S := (0, [wireWord38, wireWord1, wireWord21, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l27Dead : optimized 5 r20l27.1 r20l27.2 = false := by decide +kernel
def r20l28 : S := (0, [wireWord38, wireWord4, wireWord21, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l28Dead : optimized 5 r20l28.1 r20l28.2 = false := by decide +kernel
def r20l29 : S := (0, [wireWord29, wireWord4, wireWord21, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l29Dead : optimized 5 r20l29.1 r20l29.2 = false := by decide +kernel
def r20l30 : S := (0, [wireWord22, wireWord1, wireWord21, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l30Dead : optimized 5 r20l30.1 r20l30.2 = false := by decide +kernel
def r20l31 : S := (0, [wireWord9, wireWord0, wireWord21, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l31Dead : optimized 5 r20l31.1 r20l31.2 = false := by decide +kernel
def r20l32 : S := (0, [wireWord26, wireWord0, wireWord21, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l32Dead : optimized 5 r20l32.1 r20l32.2 = false := by decide +kernel
def r20l33 : S := (0, [wireWord28, wireWord0, wireWord21, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l33Dead : optimized 5 r20l33.1 r20l33.2 = false := by decide +kernel
def r20l34 : S := (0, [wireWord36, wireWord0, wireWord21, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l34Dead : optimized 5 r20l34.1 r20l34.2 = false := by decide +kernel
def r20l35 : S := (0, [wireWord14, wireWord3, wireWord21, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l35Dead : optimized 5 r20l35.1 r20l35.2 = false := by decide +kernel
def r20l36 : S := (0, [wireWord16, wireWord3, wireWord21, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r20l36Dead : optimized 5 r20l36.1 r20l36.2 = false := by decide +kernel
def r20l37 : S := (0, [wireWord6, wireWord2, wireWord21, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r20l37Dead : optimized 5 r20l37.1 r20l37.2 = false := by decide +kernel
def r20l38 : S := (0, [wireWord8, wireWord2, wireWord21, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r20l38Dead : optimized 5 r20l38.1 r20l38.2 = false := by decide +kernel
def r20l39 : S := (0, [wireWord5, wireWord2, wireWord21, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r20l39Dead : optimized 5 r20l39.1 r20l39.2 = false := by decide +kernel
def r20l40 : S := (0, [wireWord7, wireWord2, wireWord21, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r20l40Dead : optimized 5 r20l40.1 r20l40.2 = false := by decide +kernel
theorem rootCell20Dead : optimized 6 rootCell20.1 rootCell20.2 = false := by
  have kids : nexts (rootCell20.1, rootCell20.2) = [r20l0,r20l1,r20l2,r20l3,r20l4,r20l5,r20l6,r20l7,r20l8,r20l9,r20l10,r20l11,r20l12,r20l13,r20l14,r20l15,r20l16,r20l17,r20l18,r20l19,r20l20,r20l21,r20l22,r20l23,r20l24,r20l25,r20l26,r20l27,r20l28,r20l29,r20l30,r20l31,r20l32,r20l33,r20l34,r20l35,r20l36,r20l37,r20l38,r20l39,r20l40] := by decide +kernel
  have stop : (rootCell20.2 == [goal] || rootCell20.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r20l0Dead, r20l1Dead, r20l2Dead, r20l3Dead, r20l4Dead, r20l5Dead, r20l6Dead, r20l7Dead, r20l8Dead, r20l9Dead, r20l10Dead, r20l11Dead, r20l12Dead, r20l13Dead, r20l14Dead, r20l15Dead, r20l16Dead, r20l17Dead, r20l18Dead, r20l19Dead, r20l20Dead, r20l21Dead, r20l22Dead, r20l23Dead, r20l24Dead, r20l25Dead, r20l26Dead, r20l27Dead, r20l28Dead, r20l29Dead, r20l30Dead, r20l31Dead, r20l32Dead, r20l33Dead, r20l34Dead, r20l35Dead, r20l36Dead, r20l37Dead, r20l38Dead, r20l39Dead, r20l40Dead]
def rootCell21 : S := (1, [wireWord38, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
def r21l0 : S := (1, [wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l0Dead : optimized 5 r21l0.1 r21l0.2 = false := by decide +kernel
def r21l1 : S := (0, [wireWord1, wireWord38, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l1Dead : optimized 5 r21l1.1 r21l1.2 = false := by decide +kernel
def r21l2 : S := (0, [wireWord1, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l2Dead : optimized 5 r21l2.1 r21l2.2 = false := by decide +kernel
def r21l3 : S := (0, [wireWord38, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l3Dead : optimized 5 r21l3.1 r21l3.2 = false := by decide +kernel
def r21l4 : S := (0, [wireWord22, wireWord38, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l4Dead : optimized 5 r21l4.1 r21l4.2 = false := by decide +kernel
def r21l5 : S := (0, [wireWord22, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l5Dead : optimized 5 r21l5.1 r21l5.2 = false := by decide +kernel
def r21l6 : S := (0, [0, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l6Dead : optimized 5 r21l6.1 r21l6.2 = false := by decide +kernel
def r21l7 : S := (1, [wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l7Dead : optimized 5 r21l7.1 r21l7.2 = false := by decide +kernel
def r21l8 : S := (0, [wireWord4, wireWord38, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l8Dead : optimized 5 r21l8.1 r21l8.2 = false := by decide +kernel
def r21l9 : S := (0, [wireWord4, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l9Dead : optimized 5 r21l9.1 r21l9.2 = false := by decide +kernel
def r21l10 : S := (0, [wireWord38, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l10Dead : optimized 5 r21l10.1 r21l10.2 = false := by decide +kernel
def r21l11 : S := (0, [wireWord29, wireWord38, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l11Dead : optimized 5 r21l11.1 r21l11.2 = false := by decide +kernel
def r21l12 : S := (0, [wireWord29, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l12Dead : optimized 5 r21l12.1 r21l12.2 = false := by decide +kernel
def r21l13 : S := (0, [0, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l13Dead : optimized 5 r21l13.1 r21l13.2 = false := by decide +kernel
def r21l14 : S := (0, [2859060066378580832, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l14Dead : optimized 5 r21l14.1 r21l14.2 = false := by decide +kernel
def r21l15 : S := (0, [4611686018410545151, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l15Dead : optimized 5 r21l15.1 r21l15.2 = false := by decide +kernel
def r21l16 : S := (0, [599546100335938706, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l16Dead : optimized 5 r21l16.1 r21l16.2 = false := by decide +kernel
def r21l17 : S := (0, [1153079851696025613, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l17Dead : optimized 5 r21l17.1 r21l17.2 = false := by decide +kernel
def r21l18 : S := (0, [680896259573550864, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l18Dead : optimized 5 r21l18.1 r21l18.2 = false := by decide +kernel
def r21l19 : S := (0, [4611686018175700990, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l19Dead : optimized 5 r21l19.1 r21l19.2 = false := by decide +kernel
def r21l20 : S := (0, [2777709907140968674, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l20Dead : optimized 5 r21l20.1 r21l20.2 = false := by decide +kernel
def r21l21 : S := (0, [1153079851461181452, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l21Dead : optimized 5 r21l21.1 r21l21.2 = false := by decide +kernel
def r21l22 : S := (0, [3134343851775262720, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r21l22Dead : optimized 5 r21l22.1 r21l22.2 = false := by decide +kernel
def r21l23 : S := (0, [4611686018410610674, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r21l23Dead : optimized 5 r21l23.1 r21l23.2 = false := by decide +kernel
def r21l24 : S := (0, [324262314939256818, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r21l24Dead : optimized 5 r21l24.1 r21l24.2 = false := by decide +kernel
def r21l25 : S := (0, [wireWord62, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r21l25Dead : optimized 5 r21l25.1 r21l25.2 = false := by decide +kernel
def r21l26 : S := (1, [wireWord21, wireWord38, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l26Dead : optimized 5 r21l26.1 r21l26.2 = false := by decide +kernel
def r21l27 : S := (0, [wireWord21, wireWord1, wireWord38, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l27Dead : optimized 5 r21l27.1 r21l27.2 = false := by decide +kernel
def r21l28 : S := (0, [wireWord21, wireWord4, wireWord38, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l28Dead : optimized 5 r21l28.1 r21l28.2 = false := by decide +kernel
def r21l29 : S := (0, [wireWord29, wireWord1, wireWord38, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l29Dead : optimized 5 r21l29.1 r21l29.2 = false := by decide +kernel
def r21l30 : S := (0, [wireWord22, wireWord4, wireWord38, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l30Dead : optimized 5 r21l30.1 r21l30.2 = false := by decide +kernel
def r21l31 : S := (0, [wireWord18, wireWord0, wireWord38, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l31Dead : optimized 5 r21l31.1 r21l31.2 = false := by decide +kernel
def r21l32 : S := (0, [wireWord37, wireWord0, wireWord38, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l32Dead : optimized 5 r21l32.1 r21l32.2 = false := by decide +kernel
def r21l33 : S := (0, [wireWord15, wireWord3, wireWord38, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l33Dead : optimized 5 r21l33.1 r21l33.2 = false := by decide +kernel
def r21l34 : S := (0, [wireWord17, wireWord3, wireWord38, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r21l34Dead : optimized 5 r21l34.1 r21l34.2 = false := by decide +kernel
def r21l35 : S := (0, [wireWord6, wireWord2, wireWord38, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r21l35Dead : optimized 5 r21l35.1 r21l35.2 = false := by decide +kernel
def r21l36 : S := (0, [wireWord8, wireWord2, wireWord38, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r21l36Dead : optimized 5 r21l36.1 r21l36.2 = false := by decide +kernel
def r21l37 : S := (0, [wireWord5, wireWord2, wireWord38, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r21l37Dead : optimized 5 r21l37.1 r21l37.2 = false := by decide +kernel
def r21l38 : S := (0, [wireWord7, wireWord2, wireWord38, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r21l38Dead : optimized 5 r21l38.1 r21l38.2 = false := by decide +kernel
theorem rootCell21Dead : optimized 6 rootCell21.1 rootCell21.2 = false := by
  have kids : nexts (rootCell21.1, rootCell21.2) = [r21l0,r21l1,r21l2,r21l3,r21l4,r21l5,r21l6,r21l7,r21l8,r21l9,r21l10,r21l11,r21l12,r21l13,r21l14,r21l15,r21l16,r21l17,r21l18,r21l19,r21l20,r21l21,r21l22,r21l23,r21l24,r21l25,r21l26,r21l27,r21l28,r21l29,r21l30,r21l31,r21l32,r21l33,r21l34,r21l35,r21l36,r21l37,r21l38] := by decide +kernel
  have stop : (rootCell21.2 == [goal] || rootCell21.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r21l0Dead, r21l1Dead, r21l2Dead, r21l3Dead, r21l4Dead, r21l5Dead, r21l6Dead, r21l7Dead, r21l8Dead, r21l9Dead, r21l10Dead, r21l11Dead, r21l12Dead, r21l13Dead, r21l14Dead, r21l15Dead, r21l16Dead, r21l17Dead, r21l18Dead, r21l19Dead, r21l20Dead, r21l21Dead, r21l22Dead, r21l23Dead, r21l24Dead, r21l25Dead, r21l26Dead, r21l27Dead, r21l28Dead, r21l29Dead, r21l30Dead, r21l31Dead, r21l32Dead, r21l33Dead, r21l34Dead, r21l35Dead, r21l36Dead, r21l37Dead, r21l38Dead]
def rootCell22 : S := (1, [wireWord29, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
def r22l0 : S := (0, [wireWord29, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l0Dead : optimized 5 r22l0.1 r22l0.2 = false := by decide +kernel
def r22l1 : S := (1, [wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l1Dead : optimized 5 r22l1.1 r22l1.2 = false := by decide +kernel
def r22l2 : S := (0, [wireWord1, wireWord29, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l2Dead : optimized 5 r22l2.1 r22l2.2 = false := by decide +kernel
def r22l3 : S := (0, [wireWord1, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l3Dead : optimized 5 r22l3.1 r22l3.2 = false := by decide +kernel
def r22l4 : S := (0, [0, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l4Dead : optimized 5 r22l4.1 r22l4.2 = false := by decide +kernel
def r22l5 : S := (0, [wireWord21, wireWord29, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l5Dead : optimized 5 r22l5.1 r22l5.2 = false := by decide +kernel
def r22l6 : S := (0, [wireWord21, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l6Dead : optimized 5 r22l6.1 r22l6.2 = false := by decide +kernel
def r22l7 : S := (0, [0, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l7Dead : optimized 5 r22l7.1 r22l7.2 = false := by decide +kernel
def r22l8 : S := (0, [wireWord38, wireWord29, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l8Dead : optimized 5 r22l8.1 r22l8.2 = false := by decide +kernel
def r22l9 : S := (0, [wireWord38, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l9Dead : optimized 5 r22l9.1 r22l9.2 = false := by decide +kernel
def r22l10 : S := (0, [wireWord29, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l10Dead : optimized 5 r22l10.1 r22l10.2 = false := by decide +kernel
def r22l11 : S := (1, [wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l11Dead : optimized 5 r22l11.1 r22l11.2 = false := by decide +kernel
def r22l12 : S := (0, [wireWord4, wireWord29, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l12Dead : optimized 5 r22l12.1 r22l12.2 = false := by decide +kernel
def r22l13 : S := (0, [wireWord4, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l13Dead : optimized 5 r22l13.1 r22l13.2 = false := by decide +kernel
def r22l14 : S := (0, [324619862376710144, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l14Dead : optimized 5 r22l14.1 r22l14.2 = false := by decide +kernel
def r22l15 : S := (0, [4012139918611903359, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l15Dead : optimized 5 r22l15.1 r22l15.2 = false := by decide +kernel
def r22l16 : S := (0, [537296914, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l16Dead : optimized 5 r22l16.1 r22l16.2 = false := by decide +kernel
def r22l17 : S := (0, [3687520055697896301, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l17Dead : optimized 5 r22l17.1 r22l17.2 = false := by decide +kernel
def r22l18 : S := (0, [281518463647760, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l18Dead : optimized 5 r22l18.1 r22l18.2 = false := by decide +kernel
def r22l19 : S := (1, [2158314455485091614, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l19Dead : optimized 5 r22l19.1 r22l19.2 = false := by decide +kernel
def r22l20 : S := (0, [2158314455485091614, wireWord29, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l20Dead : optimized 5 r22l20.1 r22l20.2 = false := by decide +kernel
def r22l21 : S := (0, [2158314455485091614, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l21Dead : optimized 5 r22l21.1 r22l21.2 = false := by decide +kernel
def r22l22 : S := (0, [324338344450359298, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l22Dead : optimized 5 r22l22.1 r22l22.2 = false := by decide +kernel
def r22l23 : S := (1, [1833694592571084556, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l23Dead : optimized 5 r22l23.1 r22l23.2 = false := by decide +kernel
def r22l24 : S := (0, [1833694592571084556, wireWord29, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l24Dead : optimized 5 r22l24.1 r22l24.2 = false := by decide +kernel
def r22l25 : S := (0, [1833694592571084556, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l25Dead : optimized 5 r22l25.1 r22l25.2 = false := by decide +kernel
def r22l26 : S := (0, [wireWord63, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l26Dead : optimized 5 r22l26.1 r22l26.2 = false := by decide +kernel
def r22l27 : S := (1, [4611682926034153490, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l27Dead : optimized 5 r22l27.1 r22l27.2 = false := by decide +kernel
def r22l28 : S := (0, [4611682926034153490, wireWord29, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l28Dead : optimized 5 r22l28.1 r22l28.2 = false := by decide +kernel
def r22l29 : S := (0, [4611682926034153490, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l29Dead : optimized 5 r22l29.1 r22l29.2 = false := by decide +kernel
def r22l30 : S := (0, [324259222562799634, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l30Dead : optimized 5 r22l30.1 r22l30.2 = false := by decide +kernel
def r22l31 : S := (1, [4287063063120146432, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l31Dead : optimized 5 r22l31.1 r22l31.2 = false := by decide +kernel
def r22l32 : S := (0, [4287063063120146432, wireWord29, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l32Dead : optimized 5 r22l32.1 r22l32.2 = false := by decide +kernel
def r22l33 : S := (0, [4287063063120146432, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l33Dead : optimized 5 r22l33.1 r22l33.2 = false := by decide +kernel
def r22l34 : S := (0, [wireWord21, wireWord4, wireWord29, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l34Dead : optimized 5 r22l34.1 r22l34.2 = false := by decide +kernel
def r22l35 : S := (0, [wireWord38, wireWord1, wireWord29, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l35Dead : optimized 5 r22l35.1 r22l35.2 = false := by decide +kernel
def r22l36 : S := (0, [wireWord22, wireWord1, wireWord29, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l36Dead : optimized 5 r22l36.1 r22l36.2 = false := by decide +kernel
def r22l37 : S := (0, [wireWord22, wireWord4, wireWord29, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l37Dead : optimized 5 r22l37.1 r22l37.2 = false := by decide +kernel
def r22l38 : S := (0, [wireWord28, wireWord0, wireWord29, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l38Dead : optimized 5 r22l38.1 r22l38.2 = false := by decide +kernel
def r22l39 : S := (0, [wireWord36, wireWord0, wireWord29, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l39Dead : optimized 5 r22l39.1 r22l39.2 = false := by decide +kernel
def r22l40 : S := (0, [wireWord14, wireWord3, wireWord29, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l40Dead : optimized 5 r22l40.1 r22l40.2 = false := by decide +kernel
def r22l41 : S := (0, [wireWord16, wireWord3, wireWord29, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r22l41Dead : optimized 5 r22l41.1 r22l41.2 = false := by decide +kernel
def r22l42 : S := (0, [wireWord6, wireWord2, wireWord29, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l42Dead : optimized 5 r22l42.1 r22l42.2 = false := by decide +kernel
def r22l43 : S := (0, [wireWord8, wireWord2, wireWord29, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r22l43Dead : optimized 5 r22l43.1 r22l43.2 = false := by decide +kernel
def r22l44 : S := (0, [wireWord5, wireWord2, wireWord29, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r22l44Dead : optimized 5 r22l44.1 r22l44.2 = false := by decide +kernel
def r22l45 : S := (0, [wireWord7, wireWord2, wireWord29, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r22l45Dead : optimized 5 r22l45.1 r22l45.2 = false := by decide +kernel
theorem rootCell22Dead : optimized 6 rootCell22.1 rootCell22.2 = false := by
  have kids : nexts (rootCell22.1, rootCell22.2) = [r22l0,r22l1,r22l2,r22l3,r22l4,r22l5,r22l6,r22l7,r22l8,r22l9,r22l10,r22l11,r22l12,r22l13,r22l14,r22l15,r22l16,r22l17,r22l18,r22l19,r22l20,r22l21,r22l22,r22l23,r22l24,r22l25,r22l26,r22l27,r22l28,r22l29,r22l30,r22l31,r22l32,r22l33,r22l34,r22l35,r22l36,r22l37,r22l38,r22l39,r22l40,r22l41,r22l42,r22l43,r22l44,r22l45] := by decide +kernel
  have stop : (rootCell22.2 == [goal] || rootCell22.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r22l0Dead, r22l1Dead, r22l2Dead, r22l3Dead, r22l4Dead, r22l5Dead, r22l6Dead, r22l7Dead, r22l8Dead, r22l9Dead, r22l10Dead, r22l11Dead, r22l12Dead, r22l13Dead, r22l14Dead, r22l15Dead, r22l16Dead, r22l17Dead, r22l18Dead, r22l19Dead, r22l20Dead, r22l21Dead, r22l22Dead, r22l23Dead, r22l24Dead, r22l25Dead, r22l26Dead, r22l27Dead, r22l28Dead, r22l29Dead, r22l30Dead, r22l31Dead, r22l32Dead, r22l33Dead, r22l34Dead, r22l35Dead, r22l36Dead, r22l37Dead, r22l38Dead, r22l39Dead, r22l40Dead, r22l41Dead, r22l42Dead, r22l43Dead, r22l44Dead, r22l45Dead]
def rootCell23 : S := (1, [wireWord22, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
def r23l0 : S := (0, [0, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l0Dead : optimized 5 r23l0.1 r23l0.2 = false := by decide +kernel
def r23l1 : S := (0, [wireWord38, wireWord22, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l1Dead : optimized 5 r23l1.1 r23l1.2 = false := by decide +kernel
def r23l2 : S := (0, [wireWord38, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l2Dead : optimized 5 r23l2.1 r23l2.2 = false := by decide +kernel
def r23l3 : S := (0, [wireWord22, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l3Dead : optimized 5 r23l3.1 r23l3.2 = false := by decide +kernel
def r23l4 : S := (1, [wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l4Dead : optimized 5 r23l4.1 r23l4.2 = false := by decide +kernel
def r23l5 : S := (0, [wireWord1, wireWord22, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l5Dead : optimized 5 r23l5.1 r23l5.2 = false := by decide +kernel
def r23l6 : S := (0, [wireWord1, wireWord1, wireWord4, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l6Dead : optimized 5 r23l6.1 r23l6.2 = false := by decide +kernel
def r23l7 : S := (0, [wireWord22, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l7Dead : optimized 5 r23l7.1 r23l7.2 = false := by decide +kernel
def r23l8 : S := (1, [wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l8Dead : optimized 5 r23l8.1 r23l8.2 = false := by decide +kernel
def r23l9 : S := (0, [wireWord4, wireWord22, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l9Dead : optimized 5 r23l9.1 r23l9.2 = false := by decide +kernel
def r23l10 : S := (0, [wireWord4, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l10Dead : optimized 5 r23l10.1 r23l10.2 = false := by decide +kernel
def r23l11 : S := (0, [0, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l11Dead : optimized 5 r23l11.1 r23l11.2 = false := by decide +kernel
def r23l12 : S := (0, [wireWord21, wireWord22, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l12Dead : optimized 5 r23l12.1 r23l12.2 = false := by decide +kernel
def r23l13 : S := (0, [wireWord21, wireWord4, wireWord1, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l13Dead : optimized 5 r23l13.1 r23l13.2 = false := by decide +kernel
def r23l14 : S := (0, [2388070123735876448, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l14Dead : optimized 5 r23l14.1 r23l14.2 = false := by decide +kernel
def r23l15 : S := (0, [4012139919429890925, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l15Dead : optimized 5 r23l15.1 r23l15.2 = false := by decide +kernel
def r23l16 : S := (0, [1355284480, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l16Dead : optimized 5 r23l16.1 r23l16.2 = false := by decide +kernel
def r23l17 : S := (0, [1624069794338729997, wireWord0, wireWord1, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l17Dead : optimized 5 r23l17.1 r23l17.2 = false := by decide +kernel
def r23l18 : S := (0, [81065893890622208, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l18Dead : optimized 5 r23l18.1 r23l18.2 = false := by decide +kernel
def r23l19 : S := (1, [4140980342235271036, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l19Dead : optimized 5 r23l19.1 r23l19.2 = false := by decide +kernel
def r23l20 : S := (0, [4140980342235271036, wireWord22, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l20Dead : optimized 5 r23l20.1 r23l20.2 = false := by decide +kernel
def r23l21 : S := (0, [4140980342235271036, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l21Dead : optimized 5 r23l21.1 r23l21.2 = false := by decide +kernel
def r23l22 : S := (0, [2307004231200538720, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l22Dead : optimized 5 r23l22.1 r23l22.2 = false := by decide +kernel
def r23l23 : S := (1, [1752910217144110108, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l23Dead : optimized 5 r23l23.1 r23l23.2 = false := by decide +kernel
def r23l24 : S := (0, [1752910217144110108, wireWord22, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l24Dead : optimized 5 r23l24.1 r23l24.2 = false := by decide +kernel
def r23l25 : S := (0, [1752910217144110108, wireWord3, wireWord1, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l25Dead : optimized 5 r23l25.1 r23l25.2 = false := by decide +kernel
def r23l26 : S := (0, [wireWord64, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r23l26Dead : optimized 5 r23l26.1 r23l26.2 = false := by decide +kernel
def r23l27 : S := (0, [4287423703471354720, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r23l27Dead : optimized 5 r23l27.1 r23l27.2 = false := by decide +kernel
def r23l28 : S := (0, [864, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r23l28Dead : optimized 5 r23l28.1 r23l28.2 = false := by decide +kernel
def r23l29 : S := (0, [1899353578380193792, wireWord2, wireWord1, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r23l29Dead : optimized 5 r23l29.1 r23l29.2 = false := by decide +kernel
def r23l30 : S := (0, [wireWord21, wireWord1, wireWord22, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l30Dead : optimized 5 r23l30.1 r23l30.2 = false := by decide +kernel
def r23l31 : S := (0, [wireWord38, wireWord4, wireWord22, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l31Dead : optimized 5 r23l31.1 r23l31.2 = false := by decide +kernel
def r23l32 : S := (0, [wireWord29, wireWord1, wireWord22, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l32Dead : optimized 5 r23l32.1 r23l32.2 = false := by decide +kernel
def r23l33 : S := (0, [wireWord29, wireWord4, wireWord22, wireWord0, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l33Dead : optimized 5 r23l33.1 r23l33.2 = false := by decide +kernel
def r23l34 : S := (0, [wireWord9, wireWord0, wireWord22, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l34Dead : optimized 5 r23l34.1 r23l34.2 = false := by decide +kernel
def r23l35 : S := (0, [wireWord26, wireWord0, wireWord22, wireWord4, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l35Dead : optimized 5 r23l35.1 r23l35.2 = false := by decide +kernel
def r23l36 : S := (0, [wireWord18, wireWord0, wireWord22, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l36Dead : optimized 5 r23l36.1 r23l36.2 = false := by decide +kernel
def r23l37 : S := (0, [wireWord37, wireWord0, wireWord22, wireWord1, wireWord3, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l37Dead : optimized 5 r23l37.1 r23l37.2 = false := by decide +kernel
def r23l38 : S := (0, [wireWord15, wireWord3, wireWord22, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l38Dead : optimized 5 r23l38.1 r23l38.2 = false := by decide +kernel
def r23l39 : S := (0, [wireWord17, wireWord3, wireWord22, wireWord1, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r23l39Dead : optimized 5 r23l39.1 r23l39.2 = false := by decide +kernel
def r23l40 : S := (0, [wireWord6, wireWord2, wireWord22, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r23l40Dead : optimized 5 r23l40.1 r23l40.2 = false := by decide +kernel
def r23l41 : S := (0, [wireWord8, wireWord2, wireWord22, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r23l41Dead : optimized 5 r23l41.1 r23l41.2 = false := by decide +kernel
def r23l42 : S := (0, [wireWord5, wireWord2, wireWord22, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r23l42Dead : optimized 5 r23l42.1 r23l42.2 = false := by decide +kernel
def r23l43 : S := (0, [wireWord7, wireWord2, wireWord22, wireWord1, wireWord4, wireWord0])
set_option maxHeartbeats 0 in
theorem r23l43Dead : optimized 5 r23l43.1 r23l43.2 = false := by decide +kernel
theorem rootCell23Dead : optimized 6 rootCell23.1 rootCell23.2 = false := by
  have kids : nexts (rootCell23.1, rootCell23.2) = [r23l0,r23l1,r23l2,r23l3,r23l4,r23l5,r23l6,r23l7,r23l8,r23l9,r23l10,r23l11,r23l12,r23l13,r23l14,r23l15,r23l16,r23l17,r23l18,r23l19,r23l20,r23l21,r23l22,r23l23,r23l24,r23l25,r23l26,r23l27,r23l28,r23l29,r23l30,r23l31,r23l32,r23l33,r23l34,r23l35,r23l36,r23l37,r23l38,r23l39,r23l40,r23l41,r23l42,r23l43] := by decide +kernel
  have stop : (rootCell23.2 == [goal] || rootCell23.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r23l0Dead, r23l1Dead, r23l2Dead, r23l3Dead, r23l4Dead, r23l5Dead, r23l6Dead, r23l7Dead, r23l8Dead, r23l9Dead, r23l10Dead, r23l11Dead, r23l12Dead, r23l13Dead, r23l14Dead, r23l15Dead, r23l16Dead, r23l17Dead, r23l18Dead, r23l19Dead, r23l20Dead, r23l21Dead, r23l22Dead, r23l23Dead, r23l24Dead, r23l25Dead, r23l26Dead, r23l27Dead, r23l28Dead, r23l29Dead, r23l30Dead, r23l31Dead, r23l32Dead, r23l33Dead, r23l34Dead, r23l35Dead, r23l36Dead, r23l37Dead, r23l38Dead, r23l39Dead, r23l40Dead, r23l41Dead, r23l42Dead, r23l43Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell24 : S := (1, [wireWord40, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
def r24l0 : S := (0, [wireWord40, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l0Dead : optimized 5 r24l0.1 r24l0.2 = false := by decide +kernel
def r24l1 : S := (1, [wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l1Dead : optimized 5 r24l1.1 r24l1.2 = false := by decide +kernel
def r24l2 : S := (0, [wireWord1, wireWord40, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l2Dead : optimized 5 r24l2.1 r24l2.2 = false := by decide +kernel
def r24l3 : S := (0, [wireWord1, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l3Dead : optimized 5 r24l3.1 r24l3.2 = false := by decide +kernel
def r24l4 : S := (0, [0, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l4Dead : optimized 5 r24l4.1 r24l4.2 = false := by decide +kernel
def r24l5 : S := (0, [wireWord39, wireWord40, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l5Dead : optimized 5 r24l5.1 r24l5.2 = false := by decide +kernel
def r24l6 : S := (0, [wireWord39, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l6Dead : optimized 5 r24l6.1 r24l6.2 = false := by decide +kernel
def r24l7 : S := (0, [wireWord40, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l7Dead : optimized 5 r24l7.1 r24l7.2 = false := by decide +kernel
def r24l8 : S := (1, [wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l8Dead : optimized 5 r24l8.1 r24l8.2 = false := by decide +kernel
def r24l9 : S := (0, [wireWord2, wireWord40, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l9Dead : optimized 5 r24l9.1 r24l9.2 = false := by decide +kernel
def r24l10 : S := (0, [wireWord2, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l10Dead : optimized 5 r24l10.1 r24l10.2 = false := by decide +kernel
def r24l11 : S := (0, [0, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l11Dead : optimized 5 r24l11.1 r24l11.2 = false := by decide +kernel
def r24l12 : S := (0, [wireWord11, wireWord40, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l12Dead : optimized 5 r24l12.1 r24l12.2 = false := by decide +kernel
def r24l13 : S := (0, [wireWord11, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l13Dead : optimized 5 r24l13.1 r24l13.2 = false := by decide +kernel
def r24l14 : S := (0, [146727627703451648, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l14Dead : optimized 5 r24l14.1 r24l14.2 = false := by decide +kernel
def r24l15 : S := (0, [4611686017055257453, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l15Dead : optimized 5 r24l15.1 r24l15.2 = false := by decide +kernel
def r24l16 : S := (0, [599546098980651008, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l16Dead : optimized 5 r24l16.1 r24l16.2 = false := by decide +kernel
def r24l17 : S := (0, [3865412290371154797, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l17Dead : optimized 5 r24l17.1 r24l17.2 = false := by decide +kernel
def r24l18 : S := (0, [wireWord57, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l18Dead : optimized 5 r24l18.1 r24l18.2 = false := by decide +kernel
def r24l19 : S := (0, [1980422263764651804, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l19Dead : optimized 5 r24l19.1 r24l19.2 = false := by decide +kernel
def r24l20 : S := (0, [wireWord59, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l20Dead : optimized 5 r24l20.1 r24l20.2 = false := by decide +kernel
def r24l21 : S := (0, [1234148537080549148, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l21Dead : optimized 5 r24l21.1 r24l21.2 = false := by decide +kernel
def r24l22 : S := (0, [wireWord61, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r24l22Dead : optimized 5 r24l22.1 r24l22.2 = false := by decide +kernel
def r24l23 : S := (0, [3134346944151719904, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r24l23Dead : optimized 5 r24l23.1 r24l23.2 = false := by decide +kernel
def r24l24 : S := (0, [wireWord63, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r24l24Dead : optimized 5 r24l24.1 r24l24.2 = false := by decide +kernel
def r24l25 : S := (0, [2388073217467617248, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r24l25Dead : optimized 5 r24l25.1 r24l25.2 = false := by decide +kernel
def r24l26 : S := (0, [wireWord13, wireWord1, wireWord40, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l26Dead : optimized 5 r24l26.1 r24l26.2 = false := by decide +kernel
def r24l27 : S := (0, [wireWord13, wireWord2, wireWord40, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l27Dead : optimized 5 r24l27.1 r24l27.2 = false := by decide +kernel
def r24l28 : S := (0, [wireWord39, wireWord2, wireWord40, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l28Dead : optimized 5 r24l28.1 r24l28.2 = false := by decide +kernel
def r24l29 : S := (0, [wireWord11, wireWord1, wireWord40, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l29Dead : optimized 5 r24l29.1 r24l29.2 = false := by decide +kernel
def r24l30 : S := (0, [wireWord9, wireWord0, wireWord40, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l30Dead : optimized 5 r24l30.1 r24l30.2 = false := by decide +kernel
def r24l31 : S := (0, [wireWord26, wireWord0, wireWord40, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l31Dead : optimized 5 r24l31.1 r24l31.2 = false := by decide +kernel
def r24l32 : S := (0, [wireWord10, wireWord0, wireWord40, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l32Dead : optimized 5 r24l32.1 r24l32.2 = false := by decide +kernel
def r24l33 : S := (0, [wireWord12, wireWord0, wireWord40, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l33Dead : optimized 5 r24l33.1 r24l33.2 = false := by decide +kernel
def r24l34 : S := (0, [wireWord5, wireWord2, wireWord40, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l34Dead : optimized 5 r24l34.1 r24l34.2 = false := by decide +kernel
def r24l35 : S := (0, [wireWord7, wireWord2, wireWord40, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r24l35Dead : optimized 5 r24l35.1 r24l35.2 = false := by decide +kernel
def r24l36 : S := (0, [wireWord6, wireWord2, wireWord40, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r24l36Dead : optimized 5 r24l36.1 r24l36.2 = false := by decide +kernel
def r24l37 : S := (0, [wireWord8, wireWord2, wireWord40, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r24l37Dead : optimized 5 r24l37.1 r24l37.2 = false := by decide +kernel
theorem rootCell24Dead : optimized 6 rootCell24.1 rootCell24.2 = false := by
  have kids : nexts (rootCell24.1, rootCell24.2) = [r24l0,r24l1,r24l2,r24l3,r24l4,r24l5,r24l6,r24l7,r24l8,r24l9,r24l10,r24l11,r24l12,r24l13,r24l14,r24l15,r24l16,r24l17,r24l18,r24l19,r24l20,r24l21,r24l22,r24l23,r24l24,r24l25,r24l26,r24l27,r24l28,r24l29,r24l30,r24l31,r24l32,r24l33,r24l34,r24l35,r24l36,r24l37] := by decide +kernel
  have stop : (rootCell24.2 == [goal] || rootCell24.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r24l0Dead, r24l1Dead, r24l2Dead, r24l3Dead, r24l4Dead, r24l5Dead, r24l6Dead, r24l7Dead, r24l8Dead, r24l9Dead, r24l10Dead, r24l11Dead, r24l12Dead, r24l13Dead, r24l14Dead, r24l15Dead, r24l16Dead, r24l17Dead, r24l18Dead, r24l19Dead, r24l20Dead, r24l21Dead, r24l22Dead, r24l23Dead, r24l24Dead, r24l25Dead, r24l26Dead, r24l27Dead, r24l28Dead, r24l29Dead, r24l30Dead, r24l31Dead, r24l32Dead, r24l33Dead, r24l34Dead, r24l35Dead, r24l36Dead, r24l37Dead]
def rootCell25 : S := (1, [wireWord13, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
def r25l0 : S := (1, [wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l0Dead : optimized 5 r25l0.1 r25l0.2 = false := by decide +kernel
def r25l1 : S := (0, [wireWord1, wireWord13, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l1Dead : optimized 5 r25l1.1 r25l1.2 = false := by decide +kernel
def r25l2 : S := (0, [wireWord1, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l2Dead : optimized 5 r25l2.1 r25l2.2 = false := by decide +kernel
def r25l3 : S := (0, [wireWord13, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l3Dead : optimized 5 r25l3.1 r25l3.2 = false := by decide +kernel
def r25l4 : S := (0, [wireWord11, wireWord13, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l4Dead : optimized 5 r25l4.1 r25l4.2 = false := by decide +kernel
def r25l5 : S := (0, [wireWord11, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l5Dead : optimized 5 r25l5.1 r25l5.2 = false := by decide +kernel
def r25l6 : S := (0, [0, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l6Dead : optimized 5 r25l6.1 r25l6.2 = false := by decide +kernel
def r25l7 : S := (1, [wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l7Dead : optimized 5 r25l7.1 r25l7.2 = false := by decide +kernel
def r25l8 : S := (0, [wireWord2, wireWord13, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l8Dead : optimized 5 r25l8.1 r25l8.2 = false := by decide +kernel
def r25l9 : S := (0, [wireWord2, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l9Dead : optimized 5 r25l9.1 r25l9.2 = false := by decide +kernel
def r25l10 : S := (0, [wireWord13, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l10Dead : optimized 5 r25l10.1 r25l10.2 = false := by decide +kernel
def r25l11 : S := (0, [wireWord39, wireWord13, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l11Dead : optimized 5 r25l11.1 r25l11.2 = false := by decide +kernel
def r25l12 : S := (0, [wireWord39, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l12Dead : optimized 5 r25l12.1 r25l12.2 = false := by decide +kernel
def r25l13 : S := (0, [0, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l13Dead : optimized 5 r25l13.1 r25l13.2 = false := by decide +kernel
def r25l14 : S := (1, [4012139918074605568, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l14Dead : optimized 5 r25l14.1 r25l14.2 = false := by decide +kernel
def r25l15 : S := (0, [4012139918074605568, wireWord13, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l15Dead : optimized 5 r25l15.1 r25l15.2 = false := by decide +kernel
def r25l16 : S := (0, [4012139918074605568, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l16Dead : optimized 5 r25l16.1 r25l16.2 = false := by decide +kernel
def r25l17 : S := (0, [4611686018410610687, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l17Dead : optimized 5 r25l17.1 r25l17.2 = false := by decide +kernel
def r25l18 : S := (1, [599546100336004242, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l18Dead : optimized 5 r25l18.1 r25l18.2 = false := by decide +kernel
def r25l19 : S := (0, [599546100336004242, wireWord13, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l19Dead : optimized 5 r25l19.1 r25l19.2 = false := by decide +kernel
def r25l20 : S := (0, [599546100336004242, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l20Dead : optimized 5 r25l20.1 r25l20.2 = false := by decide +kernel
def r25l21 : S := (0, [877, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l21Dead : optimized 5 r25l21.1 r25l21.2 = false := by decide +kernel
def r25l22 : S := (1, [1833976111034731536, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l22Dead : optimized 5 r25l22.1 r25l22.2 = false := by decide +kernel
def r25l23 : S := (0, [1833976111034731536, wireWord13, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l23Dead : optimized 5 r25l23.1 r25l23.2 = false := by decide +kernel
def r25l24 : S := (0, [1833976111034731536, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l24Dead : optimized 5 r25l24.1 r25l24.2 = false := by decide +kernel
def r25l25 : S := (0, [4611686018410610590, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l25Dead : optimized 5 r25l25.1 r25l25.2 = false := by decide +kernel
def r25l26 : S := (1, [2777709907375878274, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l26Dead : optimized 5 r25l26.1 r25l26.2 = false := by decide +kernel
def r25l27 : S := (0, [2777709907375878274, wireWord13, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l27Dead : optimized 5 r25l27.1 r25l27.2 = false := by decide +kernel
def r25l28 : S := (0, [2777709907375878274, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l28Dead : optimized 5 r25l28.1 r25l28.2 = false := by decide +kernel
def r25l29 : S := (0, [780, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l29Dead : optimized 5 r25l29.1 r25l29.2 = false := by decide +kernel
def r25l30 : S := (1, [3133986303800511616, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l30Dead : optimized 5 r25l30.1 r25l30.2 = false := by decide +kernel
def r25l31 : S := (0, [3133986303800511616, wireWord13, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l31Dead : optimized 5 r25l31.1 r25l31.2 = false := by decide +kernel
def r25l32 : S := (0, [3133986303800511616, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l32Dead : optimized 5 r25l32.1 r25l32.2 = false := by decide +kernel
def r25l33 : S := (0, [4611686018410610674, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l33Dead : optimized 5 r25l33.1 r25l33.2 = false := by decide +kernel
def r25l34 : S := (1, [1477699714610098194, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l34Dead : optimized 5 r25l34.1 r25l34.2 = false := by decide +kernel
def r25l35 : S := (0, [1477699714610098194, wireWord13, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l35Dead : optimized 5 r25l35.1 r25l35.2 = false := by decide +kernel
def r25l36 : S := (0, [1477699714610098194, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l36Dead : optimized 5 r25l36.1 r25l36.2 = false := by decide +kernel
def r25l37 : S := (0, [864, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l37Dead : optimized 5 r25l37.1 r25l37.2 = false := by decide +kernel
def r25l38 : S := (0, [wireWord40, wireWord1, wireWord13, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l38Dead : optimized 5 r25l38.1 r25l38.2 = false := by decide +kernel
def r25l39 : S := (0, [wireWord40, wireWord2, wireWord13, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l39Dead : optimized 5 r25l39.1 r25l39.2 = false := by decide +kernel
def r25l40 : S := (0, [wireWord39, wireWord1, wireWord13, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l40Dead : optimized 5 r25l40.1 r25l40.2 = false := by decide +kernel
def r25l41 : S := (0, [wireWord11, wireWord2, wireWord13, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l41Dead : optimized 5 r25l41.1 r25l41.2 = false := by decide +kernel
def r25l42 : S := (0, [wireWord30, wireWord0, wireWord13, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l42Dead : optimized 5 r25l42.1 r25l42.2 = false := by decide +kernel
def r25l43 : S := (0, [wireWord31, wireWord0, wireWord13, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l43Dead : optimized 5 r25l43.1 r25l43.2 = false := by decide +kernel
def r25l44 : S := (1, [wireWord5, wireWord13, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l44Dead : optimized 5 r25l44.1 r25l44.2 = false := by decide +kernel
def r25l45 : S := (0, [wireWord5, wireWord2, wireWord13, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l45Dead : optimized 5 r25l45.1 r25l45.2 = false := by decide +kernel
def r25l46 : S := (0, [wireWord5, wireWord3, wireWord13, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l46Dead : optimized 5 r25l46.1 r25l46.2 = false := by decide +kernel
def r25l47 : S := (0, [wireWord7, wireWord2, wireWord13, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l47Dead : optimized 5 r25l47.1 r25l47.2 = false := by decide +kernel
def r25l48 : S := (0, [wireWord24, wireWord3, wireWord13, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r25l48Dead : optimized 5 r25l48.1 r25l48.2 = false := by decide +kernel
def r25l49 : S := (1, [wireWord6, wireWord13, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l49Dead : optimized 5 r25l49.1 r25l49.2 = false := by decide +kernel
def r25l50 : S := (0, [wireWord6, wireWord2, wireWord13, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l50Dead : optimized 5 r25l50.1 r25l50.2 = false := by decide +kernel
def r25l51 : S := (0, [wireWord6, wireWord4, wireWord13, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l51Dead : optimized 5 r25l51.1 r25l51.2 = false := by decide +kernel
def r25l52 : S := (0, [wireWord8, wireWord2, wireWord13, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l52Dead : optimized 5 r25l52.1 r25l52.2 = false := by decide +kernel
def r25l53 : S := (0, [wireWord25, wireWord4, wireWord13, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r25l53Dead : optimized 5 r25l53.1 r25l53.2 = false := by decide +kernel
theorem rootCell25Dead : optimized 6 rootCell25.1 rootCell25.2 = false := by
  have kids : nexts (rootCell25.1, rootCell25.2) = [r25l0,r25l1,r25l2,r25l3,r25l4,r25l5,r25l6,r25l7,r25l8,r25l9,r25l10,r25l11,r25l12,r25l13,r25l14,r25l15,r25l16,r25l17,r25l18,r25l19,r25l20,r25l21,r25l22,r25l23,r25l24,r25l25,r25l26,r25l27,r25l28,r25l29,r25l30,r25l31,r25l32,r25l33,r25l34,r25l35,r25l36,r25l37,r25l38,r25l39,r25l40,r25l41,r25l42,r25l43,r25l44,r25l45,r25l46,r25l47,r25l48,r25l49,r25l50,r25l51,r25l52,r25l53] := by decide +kernel
  have stop : (rootCell25.2 == [goal] || rootCell25.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r25l0Dead, r25l1Dead, r25l2Dead, r25l3Dead, r25l4Dead, r25l5Dead, r25l6Dead, r25l7Dead, r25l8Dead, r25l9Dead, r25l10Dead, r25l11Dead, r25l12Dead, r25l13Dead, r25l14Dead, r25l15Dead, r25l16Dead, r25l17Dead, r25l18Dead, r25l19Dead, r25l20Dead, r25l21Dead, r25l22Dead, r25l23Dead, r25l24Dead, r25l25Dead, r25l26Dead, r25l27Dead, r25l28Dead, r25l29Dead, r25l30Dead, r25l31Dead, r25l32Dead, r25l33Dead, r25l34Dead, r25l35Dead, r25l36Dead, r25l37Dead, r25l38Dead, r25l39Dead, r25l40Dead, r25l41Dead, r25l42Dead, r25l43Dead, r25l44Dead, r25l45Dead, r25l46Dead, r25l47Dead, r25l48Dead, r25l49Dead, r25l50Dead, r25l51Dead, r25l52Dead, r25l53Dead]
def rootCell26 : S := (1, [wireWord39, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
def r26l0 : S := (0, [wireWord39, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l0Dead : optimized 5 r26l0.1 r26l0.2 = false := by decide +kernel
def r26l1 : S := (1, [wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l1Dead : optimized 5 r26l1.1 r26l1.2 = false := by decide +kernel
def r26l2 : S := (0, [wireWord1, wireWord39, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l2Dead : optimized 5 r26l2.1 r26l2.2 = false := by decide +kernel
def r26l3 : S := (0, [wireWord1, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l3Dead : optimized 5 r26l3.1 r26l3.2 = false := by decide +kernel
def r26l4 : S := (0, [0, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l4Dead : optimized 5 r26l4.1 r26l4.2 = false := by decide +kernel
def r26l5 : S := (0, [wireWord40, wireWord39, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l5Dead : optimized 5 r26l5.1 r26l5.2 = false := by decide +kernel
def r26l6 : S := (0, [wireWord40, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l6Dead : optimized 5 r26l6.1 r26l6.2 = false := by decide +kernel
def r26l7 : S := (0, [0, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l7Dead : optimized 5 r26l7.1 r26l7.2 = false := by decide +kernel
def r26l8 : S := (0, [wireWord13, wireWord39, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l8Dead : optimized 5 r26l8.1 r26l8.2 = false := by decide +kernel
def r26l9 : S := (0, [wireWord13, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l9Dead : optimized 5 r26l9.1 r26l9.2 = false := by decide +kernel
def r26l10 : S := (0, [wireWord39, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l10Dead : optimized 5 r26l10.1 r26l10.2 = false := by decide +kernel
def r26l11 : S := (1, [wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l11Dead : optimized 5 r26l11.1 r26l11.2 = false := by decide +kernel
def r26l12 : S := (0, [wireWord2, wireWord39, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l12Dead : optimized 5 r26l12.1 r26l12.2 = false := by decide +kernel
def r26l13 : S := (0, [wireWord2, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l13Dead : optimized 5 r26l13.1 r26l13.2 = false := by decide +kernel
def r26l14 : S := (0, [324262314939252736, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l14Dead : optimized 5 r26l14.1 r26l14.2 = false := by decide +kernel
def r26l15 : S := (0, [4012139918074609663, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l15Dead : optimized 5 r26l15.1 r26l15.2 = false := by decide +kernel
def r26l16 : S := (0, [3218, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l16Dead : optimized 5 r26l16.1 r26l16.2 = false := by decide +kernel
def r26l17 : S := (0, [3687877603135353709, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l17Dead : optimized 5 r26l17.1 r26l17.2 = false := by decide +kernel
def r26l18 : S := (0, [2791728745488, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l18Dead : optimized 5 r26l18.1 r26l18.2 = false := by decide +kernel
def r26l19 : S := (1, [2158235634245242782, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l19Dead : optimized 5 r26l19.1 r26l19.2 = false := by decide +kernel
def r26l20 : S := (0, [2158235634245242782, wireWord39, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l20Dead : optimized 5 r26l20.1 r26l20.2 = false := by decide +kernel
def r26l21 : S := (0, [2158235634245242782, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l21Dead : optimized 5 r26l21.1 r26l21.2 = false := by decide +kernel
def r26l22 : S := (0, [324259523210510466, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l22Dead : optimized 5 r26l22.1 r26l22.2 = false := by decide +kernel
def r26l23 : S := (1, [1833973319305986828, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l23Dead : optimized 5 r26l23.1 r26l23.2 = false := by decide +kernel
def r26l24 : S := (0, [1833973319305986828, wireWord39, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l24Dead : optimized 5 r26l24.1 r26l24.2 = false := by decide +kernel
def r26l25 : S := (0, [1833973319305986828, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l25Dead : optimized 5 r26l25.1 r26l25.2 = false := by decide +kernel
def r26l26 : S := (0, [3092376456320, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l26Dead : optimized 5 r26l26.1 r26l26.2 = false := by decide +kernel
def r26l27 : S := (1, [3458245526363312114, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l27Dead : optimized 5 r26l27.1 r26l27.2 = false := by decide +kernel
def r26l28 : S := (0, [3458245526363312114, wireWord39, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l28Dead : optimized 5 r26l28.1 r26l28.2 = false := by decide +kernel
def r26l29 : S := (0, [3458245526363312114, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l29Dead : optimized 5 r26l29.1 r26l29.2 = false := by decide +kernel
def r26l30 : S := (0, [324259222562799634, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l30Dead : optimized 5 r26l30.1 r26l30.2 = false := by decide +kernel
def r26l31 : S := (1, [3133983211424056160, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l31Dead : optimized 5 r26l31.1 r26l31.2 = false := by decide +kernel
def r26l32 : S := (0, [3133983211424056160, wireWord39, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l32Dead : optimized 5 r26l32.1 r26l32.2 = false := by decide +kernel
def r26l33 : S := (0, [3133983211424056160, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l33Dead : optimized 5 r26l33.1 r26l33.2 = false := by decide +kernel
def r26l34 : S := (0, [wireWord40, wireWord2, wireWord39, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l34Dead : optimized 5 r26l34.1 r26l34.2 = false := by decide +kernel
def r26l35 : S := (0, [wireWord13, wireWord1, wireWord39, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l35Dead : optimized 5 r26l35.1 r26l35.2 = false := by decide +kernel
def r26l36 : S := (1, [wireWord11, wireWord39, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l36Dead : optimized 5 r26l36.1 r26l36.2 = false := by decide +kernel
def r26l37 : S := (0, [wireWord11, wireWord1, wireWord39, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l37Dead : optimized 5 r26l37.1 r26l37.2 = false := by decide +kernel
def r26l38 : S := (0, [wireWord11, wireWord2, wireWord39, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l38Dead : optimized 5 r26l38.1 r26l38.2 = false := by decide +kernel
def r26l39 : S := (0, [wireWord10, wireWord0, wireWord39, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l39Dead : optimized 5 r26l39.1 r26l39.2 = false := by decide +kernel
def r26l40 : S := (0, [wireWord12, wireWord0, wireWord39, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l40Dead : optimized 5 r26l40.1 r26l40.2 = false := by decide +kernel
def r26l41 : S := (0, [wireWord5, wireWord2, wireWord39, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l41Dead : optimized 5 r26l41.1 r26l41.2 = false := by decide +kernel
def r26l42 : S := (0, [wireWord7, wireWord2, wireWord39, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r26l42Dead : optimized 5 r26l42.1 r26l42.2 = false := by decide +kernel
def r26l43 : S := (0, [wireWord6, wireWord2, wireWord39, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l43Dead : optimized 5 r26l43.1 r26l43.2 = false := by decide +kernel
def r26l44 : S := (0, [wireWord8, wireWord2, wireWord39, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r26l44Dead : optimized 5 r26l44.1 r26l44.2 = false := by decide +kernel
theorem rootCell26Dead : optimized 6 rootCell26.1 rootCell26.2 = false := by
  have kids : nexts (rootCell26.1, rootCell26.2) = [r26l0,r26l1,r26l2,r26l3,r26l4,r26l5,r26l6,r26l7,r26l8,r26l9,r26l10,r26l11,r26l12,r26l13,r26l14,r26l15,r26l16,r26l17,r26l18,r26l19,r26l20,r26l21,r26l22,r26l23,r26l24,r26l25,r26l26,r26l27,r26l28,r26l29,r26l30,r26l31,r26l32,r26l33,r26l34,r26l35,r26l36,r26l37,r26l38,r26l39,r26l40,r26l41,r26l42,r26l43,r26l44] := by decide +kernel
  have stop : (rootCell26.2 == [goal] || rootCell26.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r26l0Dead, r26l1Dead, r26l2Dead, r26l3Dead, r26l4Dead, r26l5Dead, r26l6Dead, r26l7Dead, r26l8Dead, r26l9Dead, r26l10Dead, r26l11Dead, r26l12Dead, r26l13Dead, r26l14Dead, r26l15Dead, r26l16Dead, r26l17Dead, r26l18Dead, r26l19Dead, r26l20Dead, r26l21Dead, r26l22Dead, r26l23Dead, r26l24Dead, r26l25Dead, r26l26Dead, r26l27Dead, r26l28Dead, r26l29Dead, r26l30Dead, r26l31Dead, r26l32Dead, r26l33Dead, r26l34Dead, r26l35Dead, r26l36Dead, r26l37Dead, r26l38Dead, r26l39Dead, r26l40Dead, r26l41Dead, r26l42Dead, r26l43Dead, r26l44Dead]
def rootCell27 : S := (1, [wireWord11, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
def r27l0 : S := (0, [0, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l0Dead : optimized 5 r27l0.1 r27l0.2 = false := by decide +kernel
def r27l1 : S := (0, [wireWord13, wireWord11, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l1Dead : optimized 5 r27l1.1 r27l1.2 = false := by decide +kernel
def r27l2 : S := (0, [wireWord13, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l2Dead : optimized 5 r27l2.1 r27l2.2 = false := by decide +kernel
def r27l3 : S := (0, [wireWord11, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l3Dead : optimized 5 r27l3.1 r27l3.2 = false := by decide +kernel
def r27l4 : S := (1, [wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l4Dead : optimized 5 r27l4.1 r27l4.2 = false := by decide +kernel
def r27l5 : S := (0, [wireWord1, wireWord11, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l5Dead : optimized 5 r27l5.1 r27l5.2 = false := by decide +kernel
def r27l6 : S := (0, [wireWord1, wireWord1, wireWord2, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l6Dead : optimized 5 r27l6.1 r27l6.2 = false := by decide +kernel
def r27l7 : S := (0, [wireWord11, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l7Dead : optimized 5 r27l7.1 r27l7.2 = false := by decide +kernel
def r27l8 : S := (1, [wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l8Dead : optimized 5 r27l8.1 r27l8.2 = false := by decide +kernel
def r27l9 : S := (0, [wireWord2, wireWord11, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l9Dead : optimized 5 r27l9.1 r27l9.2 = false := by decide +kernel
def r27l10 : S := (0, [wireWord2, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l10Dead : optimized 5 r27l10.1 r27l10.2 = false := by decide +kernel
def r27l11 : S := (0, [0, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l11Dead : optimized 5 r27l11.1 r27l11.2 = false := by decide +kernel
def r27l12 : S := (0, [wireWord40, wireWord11, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l12Dead : optimized 5 r27l12.1 r27l12.2 = false := by decide +kernel
def r27l13 : S := (0, [wireWord40, wireWord2, wireWord1, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l13Dead : optimized 5 r27l13.1 r27l13.2 = false := by decide +kernel
def r27l14 : S := (0, [3541149975431901184, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l14Dead : optimized 5 r27l14.1 r27l14.2 = false := by decide +kernel
def r27l15 : S := (0, [4012139919429956461, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l15Dead : optimized 5 r27l15.1 r27l15.2 = false := by decide +kernel
def r27l16 : S := (0, [1355350016, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l16Dead : optimized 5 r27l16.1 r27l16.2 = false := by decide +kernel
def r27l17 : S := (0, [470989942642705261, wireWord0, wireWord1, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l17Dead : optimized 5 r27l17.1 r27l17.2 = false := by decide +kernel
def r27l18 : S := (0, [wireWord60, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l18Dead : optimized 5 r27l18.1 r27l18.2 = false := by decide +kernel
def r27l19 : S := (0, [4140980342470180636, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l19Dead : optimized 5 r27l19.1 r27l19.2 = false := by decide +kernel
def r27l20 : S := (0, [wireWord58, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l20Dead : optimized 5 r27l20.1 r27l20.2 = false := by decide +kernel
def r27l21 : S := (0, [599830365682929436, wireWord3, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l21Dead : optimized 5 r27l21.1 r27l21.2 = false := by decide +kernel
def r27l22 : S := (0, [wireWord64, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l22Dead : optimized 5 r27l22.1 r27l22.2 = false := by decide +kernel
def r27l23 : S := (0, [4287066155496603616, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l23Dead : optimized 5 r27l23.1 r27l23.2 = false := by decide +kernel
def r27l24 : S := (0, [wireWord62, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l24Dead : optimized 5 r27l24.1 r27l24.2 = false := by decide +kernel
def r27l25 : S := (0, [745916178709352416, wireWord4, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l25Dead : optimized 5 r27l25.1 r27l25.2 = false := by decide +kernel
def r27l26 : S := (0, [wireWord40, wireWord1, wireWord11, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l26Dead : optimized 5 r27l26.1 r27l26.2 = false := by decide +kernel
def r27l27 : S := (0, [wireWord13, wireWord2, wireWord11, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l27Dead : optimized 5 r27l27.1 r27l27.2 = false := by decide +kernel
def r27l28 : S := (1, [wireWord39, wireWord11, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l28Dead : optimized 5 r27l28.1 r27l28.2 = false := by decide +kernel
def r27l29 : S := (0, [wireWord39, wireWord1, wireWord11, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l29Dead : optimized 5 r27l29.1 r27l29.2 = false := by decide +kernel
def r27l30 : S := (0, [wireWord39, wireWord2, wireWord11, wireWord0, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l30Dead : optimized 5 r27l30.1 r27l30.2 = false := by decide +kernel
def r27l31 : S := (0, [wireWord9, wireWord0, wireWord11, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l31Dead : optimized 5 r27l31.1 r27l31.2 = false := by decide +kernel
def r27l32 : S := (0, [wireWord26, wireWord0, wireWord11, wireWord2, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l32Dead : optimized 5 r27l32.1 r27l32.2 = false := by decide +kernel
def r27l33 : S := (0, [wireWord30, wireWord0, wireWord11, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l33Dead : optimized 5 r27l33.1 r27l33.2 = false := by decide +kernel
def r27l34 : S := (0, [wireWord31, wireWord0, wireWord11, wireWord1, wireWord3, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l34Dead : optimized 5 r27l34.1 r27l34.2 = false := by decide +kernel
def r27l35 : S := (1, [wireWord5, wireWord11, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l35Dead : optimized 5 r27l35.1 r27l35.2 = false := by decide +kernel
def r27l36 : S := (0, [wireWord5, wireWord2, wireWord11, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l36Dead : optimized 5 r27l36.1 r27l36.2 = false := by decide +kernel
def r27l37 : S := (0, [wireWord5, wireWord3, wireWord11, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l37Dead : optimized 5 r27l37.1 r27l37.2 = false := by decide +kernel
def r27l38 : S := (0, [wireWord7, wireWord2, wireWord11, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l38Dead : optimized 5 r27l38.1 r27l38.2 = false := by decide +kernel
def r27l39 : S := (0, [wireWord24, wireWord3, wireWord11, wireWord1, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r27l39Dead : optimized 5 r27l39.1 r27l39.2 = false := by decide +kernel
def r27l40 : S := (1, [wireWord6, wireWord11, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l40Dead : optimized 5 r27l40.1 r27l40.2 = false := by decide +kernel
def r27l41 : S := (0, [wireWord6, wireWord2, wireWord11, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l41Dead : optimized 5 r27l41.1 r27l41.2 = false := by decide +kernel
def r27l42 : S := (0, [wireWord6, wireWord4, wireWord11, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l42Dead : optimized 5 r27l42.1 r27l42.2 = false := by decide +kernel
def r27l43 : S := (0, [wireWord8, wireWord2, wireWord11, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l43Dead : optimized 5 r27l43.1 r27l43.2 = false := by decide +kernel
def r27l44 : S := (0, [wireWord25, wireWord4, wireWord11, wireWord1, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r27l44Dead : optimized 5 r27l44.1 r27l44.2 = false := by decide +kernel
theorem rootCell27Dead : optimized 6 rootCell27.1 rootCell27.2 = false := by
  have kids : nexts (rootCell27.1, rootCell27.2) = [r27l0,r27l1,r27l2,r27l3,r27l4,r27l5,r27l6,r27l7,r27l8,r27l9,r27l10,r27l11,r27l12,r27l13,r27l14,r27l15,r27l16,r27l17,r27l18,r27l19,r27l20,r27l21,r27l22,r27l23,r27l24,r27l25,r27l26,r27l27,r27l28,r27l29,r27l30,r27l31,r27l32,r27l33,r27l34,r27l35,r27l36,r27l37,r27l38,r27l39,r27l40,r27l41,r27l42,r27l43,r27l44] := by decide +kernel
  have stop : (rootCell27.2 == [goal] || rootCell27.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r27l0Dead, r27l1Dead, r27l2Dead, r27l3Dead, r27l4Dead, r27l5Dead, r27l6Dead, r27l7Dead, r27l8Dead, r27l9Dead, r27l10Dead, r27l11Dead, r27l12Dead, r27l13Dead, r27l14Dead, r27l15Dead, r27l16Dead, r27l17Dead, r27l18Dead, r27l19Dead, r27l20Dead, r27l21Dead, r27l22Dead, r27l23Dead, r27l24Dead, r27l25Dead, r27l26Dead, r27l27Dead, r27l28Dead, r27l29Dead, r27l30Dead, r27l31Dead, r27l32Dead, r27l33Dead, r27l34Dead, r27l35Dead, r27l36Dead, r27l37Dead, r27l38Dead, r27l39Dead, r27l40Dead, r27l41Dead, r27l42Dead, r27l43Dead, r27l44Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell28 : S := (1, [wireWord15, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
def r28l0 : S := (0, [wireWord15, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l0Dead : optimized 5 r28l0.1 r28l0.2 = false := by decide +kernel
def r28l1 : S := (1, [wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l1Dead : optimized 5 r28l1.1 r28l1.2 = false := by decide +kernel
def r28l2 : S := (0, [wireWord3, wireWord15, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l2Dead : optimized 5 r28l2.1 r28l2.2 = false := by decide +kernel
def r28l3 : S := (0, [wireWord3, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l3Dead : optimized 5 r28l3.1 r28l3.2 = false := by decide +kernel
def r28l4 : S := (0, [0, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l4Dead : optimized 5 r28l4.1 r28l4.2 = false := by decide +kernel
def r28l5 : S := (0, [wireWord17, wireWord15, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l5Dead : optimized 5 r28l5.1 r28l5.2 = false := by decide +kernel
def r28l6 : S := (0, [wireWord17, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l6Dead : optimized 5 r28l6.1 r28l6.2 = false := by decide +kernel
def r28l7 : S := (0, [wireWord15, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l7Dead : optimized 5 r28l7.1 r28l7.2 = false := by decide +kernel
def r28l8 : S := (1, [wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l8Dead : optimized 5 r28l8.1 r28l8.2 = false := by decide +kernel
def r28l9 : S := (0, [wireWord4, wireWord15, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l9Dead : optimized 5 r28l9.1 r28l9.2 = false := by decide +kernel
def r28l10 : S := (0, [wireWord4, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l10Dead : optimized 5 r28l10.1 r28l10.2 = false := by decide +kernel
def r28l11 : S := (0, [0, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l11Dead : optimized 5 r28l11.1 r28l11.2 = false := by decide +kernel
def r28l12 : S := (0, [wireWord16, wireWord15, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l12Dead : optimized 5 r28l12.1 r28l12.2 = false := by decide +kernel
def r28l13 : S := (0, [wireWord16, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l13Dead : optimized 5 r28l13.1 r28l13.2 = false := by decide +kernel
def r28l14 : S := (0, [81068641583366912, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l14Dead : optimized 5 r28l14.1 r28l14.2 = false := by decide +kernel
def r28l15 : S := (0, [4611686017601142637, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l15Dead : optimized 5 r28l15.1 r28l15.2 = false := by decide +kernel
def r28l16 : S := (0, [599546099526536192, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l16Dead : optimized 5 r28l16.1 r28l16.2 = false := by decide +kernel
def r28l17 : S := (0, [3931071276491239533, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l17Dead : optimized 5 r28l17.1 r28l17.2 = false := by decide +kernel
def r28l18 : S := (0, [599548847219280896, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l18Dead : optimized 5 r28l18.1 r28l18.2 = false := by decide +kernel
def r28l19 : S := (0, [1151601935513980818, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l19Dead : optimized 5 r28l19.1 r28l19.2 = false := by decide +kernel
def r28l20 : S := (0, [81065893890622208, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l20Dead : optimized 5 r28l20.1 r28l20.2 = false := by decide +kernel
def r28l21 : S := (0, [470987194404077714, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l21Dead : optimized 5 r28l21.1 r28l21.2 = false := by decide +kernel
def r28l22 : S := (0, [wireWord45, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l22Dead : optimized 5 r28l22.1 r28l22.2 = false := by decide +kernel
def r28l23 : S := (0, [4287426452250427136, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l23Dead : optimized 5 r28l23.1 r28l23.2 = false := by decide +kernel
def r28l24 : S := (0, [2748779073280, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l24Dead : optimized 5 r28l24.1 r28l24.2 = false := by decide +kernel
def r28l25 : S := (0, [3606811711140524032, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l25Dead : optimized 5 r28l25.1 r28l25.2 = false := by decide +kernel
def r28l26 : S := (1, [wireWord14, wireWord15, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l26Dead : optimized 5 r28l26.1 r28l26.2 = false := by decide +kernel
def r28l27 : S := (0, [wireWord14, wireWord3, wireWord15, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l27Dead : optimized 5 r28l27.1 r28l27.2 = false := by decide +kernel
def r28l28 : S := (0, [wireWord14, wireWord4, wireWord15, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l28Dead : optimized 5 r28l28.1 r28l28.2 = false := by decide +kernel
def r28l29 : S := (0, [wireWord17, wireWord4, wireWord15, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l29Dead : optimized 5 r28l29.1 r28l29.2 = false := by decide +kernel
def r28l30 : S := (0, [wireWord16, wireWord3, wireWord15, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l30Dead : optimized 5 r28l30.1 r28l30.2 = false := by decide +kernel
def r28l31 : S := (0, [wireWord32, wireWord0, wireWord15, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l31Dead : optimized 5 r28l31.1 r28l31.2 = false := by decide +kernel
def r28l32 : S := (0, [wireWord33, wireWord0, wireWord15, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l32Dead : optimized 5 r28l32.1 r28l32.2 = false := by decide +kernel
def r28l33 : S := (0, [wireWord35, wireWord1, wireWord15, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l33Dead : optimized 5 r28l33.1 r28l33.2 = false := by decide +kernel
def r28l34 : S := (0, [wireWord20, wireWord1, wireWord15, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l34Dead : optimized 5 r28l34.1 r28l34.2 = false := by decide +kernel
def r28l35 : S := (0, [wireWord5, wireWord2, wireWord15, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l35Dead : optimized 5 r28l35.1 r28l35.2 = false := by decide +kernel
def r28l36 : S := (0, [wireWord7, wireWord2, wireWord15, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l36Dead : optimized 5 r28l36.1 r28l36.2 = false := by decide +kernel
def r28l37 : S := (0, [wireWord28, wireWord0, wireWord15, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l37Dead : optimized 5 r28l37.1 r28l37.2 = false := by decide +kernel
def r28l38 : S := (0, [wireWord36, wireWord0, wireWord15, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l38Dead : optimized 5 r28l38.1 r28l38.2 = false := by decide +kernel
def r28l39 : S := (0, [wireWord38, wireWord1, wireWord15, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l39Dead : optimized 5 r28l39.1 r28l39.2 = false := by decide +kernel
def r28l40 : S := (0, [wireWord22, wireWord1, wireWord15, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r28l40Dead : optimized 5 r28l40.1 r28l40.2 = false := by decide +kernel
def r28l41 : S := (0, [wireWord6, wireWord2, wireWord15, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l41Dead : optimized 5 r28l41.1 r28l41.2 = false := by decide +kernel
def r28l42 : S := (0, [wireWord8, wireWord2, wireWord15, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r28l42Dead : optimized 5 r28l42.1 r28l42.2 = false := by decide +kernel
theorem rootCell28Dead : optimized 6 rootCell28.1 rootCell28.2 = false := by
  have kids : nexts (rootCell28.1, rootCell28.2) = [r28l0,r28l1,r28l2,r28l3,r28l4,r28l5,r28l6,r28l7,r28l8,r28l9,r28l10,r28l11,r28l12,r28l13,r28l14,r28l15,r28l16,r28l17,r28l18,r28l19,r28l20,r28l21,r28l22,r28l23,r28l24,r28l25,r28l26,r28l27,r28l28,r28l29,r28l30,r28l31,r28l32,r28l33,r28l34,r28l35,r28l36,r28l37,r28l38,r28l39,r28l40,r28l41,r28l42] := by decide +kernel
  have stop : (rootCell28.2 == [goal] || rootCell28.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r28l0Dead, r28l1Dead, r28l2Dead, r28l3Dead, r28l4Dead, r28l5Dead, r28l6Dead, r28l7Dead, r28l8Dead, r28l9Dead, r28l10Dead, r28l11Dead, r28l12Dead, r28l13Dead, r28l14Dead, r28l15Dead, r28l16Dead, r28l17Dead, r28l18Dead, r28l19Dead, r28l20Dead, r28l21Dead, r28l22Dead, r28l23Dead, r28l24Dead, r28l25Dead, r28l26Dead, r28l27Dead, r28l28Dead, r28l29Dead, r28l30Dead, r28l31Dead, r28l32Dead, r28l33Dead, r28l34Dead, r28l35Dead, r28l36Dead, r28l37Dead, r28l38Dead, r28l39Dead, r28l40Dead, r28l41Dead, r28l42Dead]
def rootCell29 : S := (1, [wireWord14, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
def r29l0 : S := (1, [wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l0Dead : optimized 5 r29l0.1 r29l0.2 = false := by decide +kernel
def r29l1 : S := (0, [wireWord3, wireWord14, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l1Dead : optimized 5 r29l1.1 r29l1.2 = false := by decide +kernel
def r29l2 : S := (0, [wireWord3, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l2Dead : optimized 5 r29l2.1 r29l2.2 = false := by decide +kernel
def r29l3 : S := (0, [wireWord14, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l3Dead : optimized 5 r29l3.1 r29l3.2 = false := by decide +kernel
def r29l4 : S := (0, [wireWord16, wireWord14, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l4Dead : optimized 5 r29l4.1 r29l4.2 = false := by decide +kernel
def r29l5 : S := (0, [wireWord16, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l5Dead : optimized 5 r29l5.1 r29l5.2 = false := by decide +kernel
def r29l6 : S := (0, [0, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l6Dead : optimized 5 r29l6.1 r29l6.2 = false := by decide +kernel
def r29l7 : S := (1, [wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l7Dead : optimized 5 r29l7.1 r29l7.2 = false := by decide +kernel
def r29l8 : S := (0, [wireWord4, wireWord14, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l8Dead : optimized 5 r29l8.1 r29l8.2 = false := by decide +kernel
def r29l9 : S := (0, [wireWord4, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l9Dead : optimized 5 r29l9.1 r29l9.2 = false := by decide +kernel
def r29l10 : S := (0, [wireWord14, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l10Dead : optimized 5 r29l10.1 r29l10.2 = false := by decide +kernel
def r29l11 : S := (0, [wireWord17, wireWord14, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l11Dead : optimized 5 r29l11.1 r29l11.2 = false := by decide +kernel
def r29l12 : S := (0, [wireWord17, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l12Dead : optimized 5 r29l12.1 r29l12.2 = false := by decide +kernel
def r29l13 : S := (0, [0, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l13Dead : optimized 5 r29l13.1 r29l13.2 = false := by decide +kernel
def r29l14 : S := (0, [3687801573389370220, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l14Dead : optimized 5 r29l14.1 r29l14.2 = false := by decide +kernel
def r29l15 : S := (0, [4611686018410577917, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l15Dead : optimized 5 r29l15.1 r29l15.2 = false := by decide +kernel
def r29l16 : S := (0, [599546100335971472, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l16Dead : optimized 5 r29l16.1 r29l16.2 = false := by decide +kernel
def r29l17 : S := (0, [324338344685236225, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l17Dead : optimized 5 r29l17.1 r29l17.2 = false := by decide +kernel
def r29l18 : S := (0, [746197697172999312, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l18Dead : optimized 5 r29l18.1 r29l18.2 = false := by decide +kernel
def r29l19 : S := (0, [4611686018175700990, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l19Dead : optimized 5 r29l19.1 r29l19.2 = false := by decide +kernel
def r29l20 : S := (0, [3541149976552342380, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l20Dead : optimized 5 r29l20.1 r29l20.2 = false := by decide +kernel
def r29l21 : S := (0, [324338344450359298, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l21Dead : optimized 5 r29l21.1 r29l21.2 = false := by decide +kernel
def r29l22 : S := (1, [4287344538399211520, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l22Dead : optimized 5 r29l22.1 r29l22.2 = false := by decide +kernel
def r29l23 : S := (0, [4287344538399211520, wireWord14, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l23Dead : optimized 5 r29l23.1 r29l23.2 = false := by decide +kernel
def r29l24 : S := (0, [4287344538399211520, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l24Dead : optimized 5 r29l24.1 r29l24.2 = false := by decide +kernel
def r29l25 : S := (0, [4287426838797484028, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l25Dead : optimized 5 r29l25.1 r29l25.2 = false := by decide +kernel
def r29l26 : S := (1, [3135326130172, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l26Dead : optimized 5 r29l26.1 r29l26.2 = false := by decide +kernel
def r29l27 : S := (0, [3135326130172, wireWord14, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l27Dead : optimized 5 r29l27.1 r29l27.2 = false := by decide +kernel
def r29l28 : S := (0, [3135326130172, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l28Dead : optimized 5 r29l28.1 r29l28.2 = false := by decide +kernel
def r29l29 : S := (0, [wireWord46, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l29Dead : optimized 5 r29l29.1 r29l29.2 = false := by decide +kernel
def r29l30 : S := (1, [wireWord15, wireWord14, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l30Dead : optimized 5 r29l30.1 r29l30.2 = false := by decide +kernel
def r29l31 : S := (0, [wireWord15, wireWord3, wireWord14, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l31Dead : optimized 5 r29l31.1 r29l31.2 = false := by decide +kernel
def r29l32 : S := (0, [wireWord15, wireWord4, wireWord14, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l32Dead : optimized 5 r29l32.1 r29l32.2 = false := by decide +kernel
def r29l33 : S := (0, [wireWord17, wireWord3, wireWord14, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l33Dead : optimized 5 r29l33.1 r29l33.2 = false := by decide +kernel
def r29l34 : S := (0, [wireWord16, wireWord4, wireWord14, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l34Dead : optimized 5 r29l34.1 r29l34.2 = false := by decide +kernel
def r29l35 : S := (0, [wireWord23, wireWord0, wireWord14, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l35Dead : optimized 5 r29l35.1 r29l35.2 = false := by decide +kernel
def r29l36 : S := (0, [wireWord34, wireWord0, wireWord14, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l36Dead : optimized 5 r29l36.1 r29l36.2 = false := by decide +kernel
def r29l37 : S := (0, [wireWord19, wireWord1, wireWord14, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l37Dead : optimized 5 r29l37.1 r29l37.2 = false := by decide +kernel
def r29l38 : S := (0, [wireWord27, wireWord1, wireWord14, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l38Dead : optimized 5 r29l38.1 r29l38.2 = false := by decide +kernel
def r29l39 : S := (0, [wireWord5, wireWord2, wireWord14, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l39Dead : optimized 5 r29l39.1 r29l39.2 = false := by decide +kernel
def r29l40 : S := (0, [wireWord7, wireWord2, wireWord14, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l40Dead : optimized 5 r29l40.1 r29l40.2 = false := by decide +kernel
def r29l41 : S := (0, [wireWord18, wireWord0, wireWord14, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l41Dead : optimized 5 r29l41.1 r29l41.2 = false := by decide +kernel
def r29l42 : S := (0, [wireWord37, wireWord0, wireWord14, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l42Dead : optimized 5 r29l42.1 r29l42.2 = false := by decide +kernel
def r29l43 : S := (0, [wireWord21, wireWord1, wireWord14, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l43Dead : optimized 5 r29l43.1 r29l43.2 = false := by decide +kernel
def r29l44 : S := (0, [wireWord29, wireWord1, wireWord14, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r29l44Dead : optimized 5 r29l44.1 r29l44.2 = false := by decide +kernel
def r29l45 : S := (0, [wireWord6, wireWord2, wireWord14, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l45Dead : optimized 5 r29l45.1 r29l45.2 = false := by decide +kernel
def r29l46 : S := (0, [wireWord8, wireWord2, wireWord14, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r29l46Dead : optimized 5 r29l46.1 r29l46.2 = false := by decide +kernel
theorem rootCell29Dead : optimized 6 rootCell29.1 rootCell29.2 = false := by
  have kids : nexts (rootCell29.1, rootCell29.2) = [r29l0,r29l1,r29l2,r29l3,r29l4,r29l5,r29l6,r29l7,r29l8,r29l9,r29l10,r29l11,r29l12,r29l13,r29l14,r29l15,r29l16,r29l17,r29l18,r29l19,r29l20,r29l21,r29l22,r29l23,r29l24,r29l25,r29l26,r29l27,r29l28,r29l29,r29l30,r29l31,r29l32,r29l33,r29l34,r29l35,r29l36,r29l37,r29l38,r29l39,r29l40,r29l41,r29l42,r29l43,r29l44,r29l45,r29l46] := by decide +kernel
  have stop : (rootCell29.2 == [goal] || rootCell29.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r29l0Dead, r29l1Dead, r29l2Dead, r29l3Dead, r29l4Dead, r29l5Dead, r29l6Dead, r29l7Dead, r29l8Dead, r29l9Dead, r29l10Dead, r29l11Dead, r29l12Dead, r29l13Dead, r29l14Dead, r29l15Dead, r29l16Dead, r29l17Dead, r29l18Dead, r29l19Dead, r29l20Dead, r29l21Dead, r29l22Dead, r29l23Dead, r29l24Dead, r29l25Dead, r29l26Dead, r29l27Dead, r29l28Dead, r29l29Dead, r29l30Dead, r29l31Dead, r29l32Dead, r29l33Dead, r29l34Dead, r29l35Dead, r29l36Dead, r29l37Dead, r29l38Dead, r29l39Dead, r29l40Dead, r29l41Dead, r29l42Dead, r29l43Dead, r29l44Dead, r29l45Dead, r29l46Dead]
def rootCell30 : S := (1, [wireWord17, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
def r30l0 : S := (0, [wireWord17, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l0Dead : optimized 5 r30l0.1 r30l0.2 = false := by decide +kernel
def r30l1 : S := (1, [wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l1Dead : optimized 5 r30l1.1 r30l1.2 = false := by decide +kernel
def r30l2 : S := (0, [wireWord3, wireWord17, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l2Dead : optimized 5 r30l2.1 r30l2.2 = false := by decide +kernel
def r30l3 : S := (0, [wireWord3, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l3Dead : optimized 5 r30l3.1 r30l3.2 = false := by decide +kernel
def r30l4 : S := (0, [0, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l4Dead : optimized 5 r30l4.1 r30l4.2 = false := by decide +kernel
def r30l5 : S := (0, [wireWord15, wireWord17, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l5Dead : optimized 5 r30l5.1 r30l5.2 = false := by decide +kernel
def r30l6 : S := (0, [wireWord15, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l6Dead : optimized 5 r30l6.1 r30l6.2 = false := by decide +kernel
def r30l7 : S := (0, [0, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l7Dead : optimized 5 r30l7.1 r30l7.2 = false := by decide +kernel
def r30l8 : S := (0, [wireWord14, wireWord17, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l8Dead : optimized 5 r30l8.1 r30l8.2 = false := by decide +kernel
def r30l9 : S := (0, [wireWord14, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l9Dead : optimized 5 r30l9.1 r30l9.2 = false := by decide +kernel
def r30l10 : S := (0, [wireWord17, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l10Dead : optimized 5 r30l10.1 r30l10.2 = false := by decide +kernel
def r30l11 : S := (1, [wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l11Dead : optimized 5 r30l11.1 r30l11.2 = false := by decide +kernel
def r30l12 : S := (0, [wireWord4, wireWord17, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l12Dead : optimized 5 r30l12.1 r30l12.2 = false := by decide +kernel
def r30l13 : S := (0, [wireWord4, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l13Dead : optimized 5 r30l13.1 r30l13.2 = false := by decide +kernel
def r30l14 : S := (0, [1153361369387499532, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l14Dead : optimized 5 r30l14.1 r30l14.2 = false := by decide +kernel
def r30l15 : S := (0, [4012139918611936125, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l15Dead : optimized 5 r30l15.1 r30l15.2 = false := by decide +kernel
def r30l16 : S := (0, [537329680, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l16Dead : optimized 5 r30l16.1 r30l16.2 = false := by decide +kernel
def r30l17 : S := (0, [2858778548687106913, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l17Dead : optimized 5 r30l17.1 r30l17.2 = false := by decide +kernel
def r30l18 : S := (0, [281518463647760, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l18Dead : optimized 5 r30l18.1 r30l18.2 = false := by decide +kernel
def r30l19 : S := (0, [2223615893084540062, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l19Dead : optimized 5 r30l19.1 r30l19.2 = false := by decide +kernel
def r30l20 : S := (0, [1153079851461181452, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l20Dead : optimized 5 r30l20.1 r30l20.2 = false := by decide +kernel
def r30l21 : S := (0, [1070254523159710850, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l21Dead : optimized 5 r30l21.1 r30l21.2 = false := by decide +kernel
def r30l22 : S := (0, [wireWord47, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l22Dead : optimized 5 r30l22.1 r30l22.2 = false := by decide +kernel
def r30l23 : S := (0, [4287423746421026844, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l23Dead : optimized 5 r30l23.1 r30l23.2 = false := by decide +kernel
def r30l24 : S := (0, [42949672988, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l24Dead : optimized 5 r30l24.1 r30l24.2 = false := by decide +kernel
def r30l25 : S := (0, [3134062376496197632, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l25Dead : optimized 5 r30l25.1 r30l25.2 = false := by decide +kernel
def r30l26 : S := (0, [wireWord15, wireWord4, wireWord17, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l26Dead : optimized 5 r30l26.1 r30l26.2 = false := by decide +kernel
def r30l27 : S := (0, [wireWord14, wireWord3, wireWord17, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l27Dead : optimized 5 r30l27.1 r30l27.2 = false := by decide +kernel
def r30l28 : S := (0, [wireWord16, wireWord3, wireWord17, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l28Dead : optimized 5 r30l28.1 r30l28.2 = false := by decide +kernel
def r30l29 : S := (0, [wireWord16, wireWord4, wireWord17, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l29Dead : optimized 5 r30l29.1 r30l29.2 = false := by decide +kernel
def r30l30 : S := (0, [wireWord23, wireWord0, wireWord17, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l30Dead : optimized 5 r30l30.1 r30l30.2 = false := by decide +kernel
def r30l31 : S := (0, [wireWord34, wireWord0, wireWord17, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l31Dead : optimized 5 r30l31.1 r30l31.2 = false := by decide +kernel
def r30l32 : S := (0, [wireWord19, wireWord1, wireWord17, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l32Dead : optimized 5 r30l32.1 r30l32.2 = false := by decide +kernel
def r30l33 : S := (0, [wireWord27, wireWord1, wireWord17, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l33Dead : optimized 5 r30l33.1 r30l33.2 = false := by decide +kernel
def r30l34 : S := (0, [wireWord5, wireWord2, wireWord17, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l34Dead : optimized 5 r30l34.1 r30l34.2 = false := by decide +kernel
def r30l35 : S := (0, [wireWord7, wireWord2, wireWord17, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l35Dead : optimized 5 r30l35.1 r30l35.2 = false := by decide +kernel
def r30l36 : S := (0, [wireWord28, wireWord0, wireWord17, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l36Dead : optimized 5 r30l36.1 r30l36.2 = false := by decide +kernel
def r30l37 : S := (0, [wireWord36, wireWord0, wireWord17, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l37Dead : optimized 5 r30l37.1 r30l37.2 = false := by decide +kernel
def r30l38 : S := (0, [wireWord38, wireWord1, wireWord17, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l38Dead : optimized 5 r30l38.1 r30l38.2 = false := by decide +kernel
def r30l39 : S := (0, [wireWord22, wireWord1, wireWord17, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r30l39Dead : optimized 5 r30l39.1 r30l39.2 = false := by decide +kernel
def r30l40 : S := (0, [wireWord6, wireWord2, wireWord17, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l40Dead : optimized 5 r30l40.1 r30l40.2 = false := by decide +kernel
def r30l41 : S := (0, [wireWord8, wireWord2, wireWord17, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r30l41Dead : optimized 5 r30l41.1 r30l41.2 = false := by decide +kernel
theorem rootCell30Dead : optimized 6 rootCell30.1 rootCell30.2 = false := by
  have kids : nexts (rootCell30.1, rootCell30.2) = [r30l0,r30l1,r30l2,r30l3,r30l4,r30l5,r30l6,r30l7,r30l8,r30l9,r30l10,r30l11,r30l12,r30l13,r30l14,r30l15,r30l16,r30l17,r30l18,r30l19,r30l20,r30l21,r30l22,r30l23,r30l24,r30l25,r30l26,r30l27,r30l28,r30l29,r30l30,r30l31,r30l32,r30l33,r30l34,r30l35,r30l36,r30l37,r30l38,r30l39,r30l40,r30l41] := by decide +kernel
  have stop : (rootCell30.2 == [goal] || rootCell30.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r30l0Dead, r30l1Dead, r30l2Dead, r30l3Dead, r30l4Dead, r30l5Dead, r30l6Dead, r30l7Dead, r30l8Dead, r30l9Dead, r30l10Dead, r30l11Dead, r30l12Dead, r30l13Dead, r30l14Dead, r30l15Dead, r30l16Dead, r30l17Dead, r30l18Dead, r30l19Dead, r30l20Dead, r30l21Dead, r30l22Dead, r30l23Dead, r30l24Dead, r30l25Dead, r30l26Dead, r30l27Dead, r30l28Dead, r30l29Dead, r30l30Dead, r30l31Dead, r30l32Dead, r30l33Dead, r30l34Dead, r30l35Dead, r30l36Dead, r30l37Dead, r30l38Dead, r30l39Dead, r30l40Dead, r30l41Dead]
def rootCell31 : S := (1, [wireWord16, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
def r31l0 : S := (0, [0, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l0Dead : optimized 5 r31l0.1 r31l0.2 = false := by decide +kernel
def r31l1 : S := (0, [wireWord14, wireWord16, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l1Dead : optimized 5 r31l1.1 r31l1.2 = false := by decide +kernel
def r31l2 : S := (0, [wireWord14, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l2Dead : optimized 5 r31l2.1 r31l2.2 = false := by decide +kernel
def r31l3 : S := (0, [wireWord16, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l3Dead : optimized 5 r31l3.1 r31l3.2 = false := by decide +kernel
def r31l4 : S := (1, [wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l4Dead : optimized 5 r31l4.1 r31l4.2 = false := by decide +kernel
def r31l5 : S := (0, [wireWord3, wireWord16, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l5Dead : optimized 5 r31l5.1 r31l5.2 = false := by decide +kernel
def r31l6 : S := (0, [wireWord3, wireWord3, wireWord4, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l6Dead : optimized 5 r31l6.1 r31l6.2 = false := by decide +kernel
def r31l7 : S := (0, [wireWord16, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l7Dead : optimized 5 r31l7.1 r31l7.2 = false := by decide +kernel
def r31l8 : S := (1, [wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l8Dead : optimized 5 r31l8.1 r31l8.2 = false := by decide +kernel
def r31l9 : S := (0, [wireWord4, wireWord16, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l9Dead : optimized 5 r31l9.1 r31l9.2 = false := by decide +kernel
def r31l10 : S := (0, [wireWord4, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l10Dead : optimized 5 r31l10.1 r31l10.2 = false := by decide +kernel
def r31l11 : S := (0, [0, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l11Dead : optimized 5 r31l11.1 r31l11.2 = false := by decide +kernel
def r31l12 : S := (0, [wireWord15, wireWord16, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l12Dead : optimized 5 r31l12.1 r31l12.2 = false := by decide +kernel
def r31l13 : S := (0, [wireWord15, wireWord4, wireWord3, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l13Dead : optimized 5 r31l13.1 r31l13.2 = false := by decide +kernel
def r31l14 : S := (0, [2453371562418503776, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l14Dead : optimized 5 r31l14.1 r31l14.2 = false := by decide +kernel
def r31l15 : S := (0, [4012139918346712045, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l15Dead : optimized 5 r31l15.1 r31l15.2 = false := by decide +kernel
def r31l16 : S := (0, [272105600, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l16Dead : optimized 5 r31l16.1 r31l16.2 = false := by decide +kernel
def r31l17 : S := (0, [1558768355656102669, wireWord0, wireWord3, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l17Dead : optimized 5 r31l17.1 r31l17.2 = false := by decide +kernel
def r31l18 : S := (0, [146367331490070656, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l18Dead : optimized 5 r31l18.1 r31l18.2 = false := by decide +kernel
def r31l19 : S := (0, [3377540272823897330, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l19Dead : optimized 5 r31l19.1 r31l19.2 = false := by decide +kernel
def r31l20 : S := (0, [2307004231200538720, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l20Dead : optimized 5 r31l20.1 r31l20.2 = false := by decide +kernel
def r31l21 : S := (0, [924168710133287954, wireWord1, wireWord3, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l21Dead : optimized 5 r31l21.1 r31l21.2 = false := by decide +kernel
def r31l22 : S := (0, [wireWord48, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l22Dead : optimized 5 r31l22.1 r31l22.2 = false := by decide +kernel
def r31l23 : S := (0, [4287424047068737760, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l23Dead : optimized 5 r31l23.1 r31l23.2 = false := by decide +kernel
def r31l24 : S := (0, [343597383904, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l24Dead : optimized 5 r31l24.1 r31l24.2 = false := by decide +kernel
def r31l25 : S := (0, [1834052484378128384, wireWord2, wireWord3, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l25Dead : optimized 5 r31l25.1 r31l25.2 = false := by decide +kernel
def r31l26 : S := (0, [wireWord15, wireWord3, wireWord16, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l26Dead : optimized 5 r31l26.1 r31l26.2 = false := by decide +kernel
def r31l27 : S := (0, [wireWord14, wireWord4, wireWord16, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l27Dead : optimized 5 r31l27.1 r31l27.2 = false := by decide +kernel
def r31l28 : S := (0, [wireWord17, wireWord3, wireWord16, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l28Dead : optimized 5 r31l28.1 r31l28.2 = false := by decide +kernel
def r31l29 : S := (0, [wireWord17, wireWord4, wireWord16, wireWord0, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l29Dead : optimized 5 r31l29.1 r31l29.2 = false := by decide +kernel
def r31l30 : S := (0, [wireWord32, wireWord0, wireWord16, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l30Dead : optimized 5 r31l30.1 r31l30.2 = false := by decide +kernel
def r31l31 : S := (0, [wireWord33, wireWord0, wireWord16, wireWord4, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l31Dead : optimized 5 r31l31.1 r31l31.2 = false := by decide +kernel
def r31l32 : S := (0, [wireWord35, wireWord1, wireWord16, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l32Dead : optimized 5 r31l32.1 r31l32.2 = false := by decide +kernel
def r31l33 : S := (0, [wireWord20, wireWord1, wireWord16, wireWord4, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l33Dead : optimized 5 r31l33.1 r31l33.2 = false := by decide +kernel
def r31l34 : S := (0, [wireWord5, wireWord2, wireWord16, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l34Dead : optimized 5 r31l34.1 r31l34.2 = false := by decide +kernel
def r31l35 : S := (0, [wireWord7, wireWord2, wireWord16, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l35Dead : optimized 5 r31l35.1 r31l35.2 = false := by decide +kernel
def r31l36 : S := (0, [wireWord18, wireWord0, wireWord16, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l36Dead : optimized 5 r31l36.1 r31l36.2 = false := by decide +kernel
def r31l37 : S := (0, [wireWord37, wireWord0, wireWord16, wireWord3, wireWord1, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l37Dead : optimized 5 r31l37.1 r31l37.2 = false := by decide +kernel
def r31l38 : S := (0, [wireWord21, wireWord1, wireWord16, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l38Dead : optimized 5 r31l38.1 r31l38.2 = false := by decide +kernel
def r31l39 : S := (0, [wireWord29, wireWord1, wireWord16, wireWord3, wireWord0, wireWord2])
set_option maxHeartbeats 0 in
theorem r31l39Dead : optimized 5 r31l39.1 r31l39.2 = false := by decide +kernel
def r31l40 : S := (0, [wireWord6, wireWord2, wireWord16, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l40Dead : optimized 5 r31l40.1 r31l40.2 = false := by decide +kernel
def r31l41 : S := (0, [wireWord8, wireWord2, wireWord16, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r31l41Dead : optimized 5 r31l41.1 r31l41.2 = false := by decide +kernel
theorem rootCell31Dead : optimized 6 rootCell31.1 rootCell31.2 = false := by
  have kids : nexts (rootCell31.1, rootCell31.2) = [r31l0,r31l1,r31l2,r31l3,r31l4,r31l5,r31l6,r31l7,r31l8,r31l9,r31l10,r31l11,r31l12,r31l13,r31l14,r31l15,r31l16,r31l17,r31l18,r31l19,r31l20,r31l21,r31l22,r31l23,r31l24,r31l25,r31l26,r31l27,r31l28,r31l29,r31l30,r31l31,r31l32,r31l33,r31l34,r31l35,r31l36,r31l37,r31l38,r31l39,r31l40,r31l41] := by decide +kernel
  have stop : (rootCell31.2 == [goal] || rootCell31.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r31l0Dead, r31l1Dead, r31l2Dead, r31l3Dead, r31l4Dead, r31l5Dead, r31l6Dead, r31l7Dead, r31l8Dead, r31l9Dead, r31l10Dead, r31l11Dead, r31l12Dead, r31l13Dead, r31l14Dead, r31l15Dead, r31l16Dead, r31l17Dead, r31l18Dead, r31l19Dead, r31l20Dead, r31l21Dead, r31l22Dead, r31l23Dead, r31l24Dead, r31l25Dead, r31l26Dead, r31l27Dead, r31l28Dead, r31l29Dead, r31l30Dead, r31l31Dead, r31l32Dead, r31l33Dead, r31l34Dead, r31l35Dead, r31l36Dead, r31l37Dead, r31l38Dead, r31l39Dead, r31l40Dead, r31l41Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell32 : S := (2, [wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
def r32l0 : S := (1, [wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l0Dead : optimized 5 r32l0.1 r32l0.2 = false := by decide +kernel
def r32l1 : S := (0, [wireWord5, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l1Dead : optimized 5 r32l1.1 r32l1.2 = false := by decide +kernel
def r32l2 : S := (1, [wireWord2, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l2Dead : optimized 5 r32l2.1 r32l2.2 = false := by decide +kernel
def r32l3 : S := (0, [wireWord2, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l3Dead : optimized 5 r32l3.1 r32l3.2 = false := by decide +kernel
def r32l4 : S := (0, [0, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l4Dead : optimized 5 r32l4.1 r32l4.2 = false := by decide +kernel
def r32l5 : S := (1, [wireWord7, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l5Dead : optimized 5 r32l5.1 r32l5.2 = false := by decide +kernel
def r32l6 : S := (1, [wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l6Dead : optimized 5 r32l6.1 r32l6.2 = false := by decide +kernel
def r32l7 : S := (0, [wireWord7, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l7Dead : optimized 5 r32l7.1 r32l7.2 = false := by decide +kernel
def r32l8 : S := (0, [wireWord49, wireWord5, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l8Dead : optimized 5 r32l8.1 r32l8.2 = false := by decide +kernel
def r32l9 : S := (0, [4611686018138469229, wireWord5, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l9Dead : optimized 5 r32l9.1 r32l9.2 = false := by decide +kernel
def r32l10 : S := (0, [wireWord52, wireWord5, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l10Dead : optimized 5 r32l10.1 r32l10.2 = false := by decide +kernel
def r32l11 : S := (0, [2777712698832483181, wireWord5, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l11Dead : optimized 5 r32l11.1 r32l11.2 = false := by decide +kernel
def r32l12 : S := (0, [wireWord57, wireWord5, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l12Dead : optimized 5 r32l12.1 r32l12.2 = false := by decide +kernel
def r32l13 : S := (0, [2304681786975161490, wireWord5, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l13Dead : optimized 5 r32l13.1 r32l13.2 = false := by decide +kernel
def r32l14 : S := (0, [wireWord60, wireWord5, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l14Dead : optimized 5 r32l14.1 r32l14.2 = false := by decide +kernel
def r32l15 : S := (0, [470708467669175442, wireWord5, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l15Dead : optimized 5 r32l15.1 r32l15.2 = false := by decide +kernel
def r32l16 : S := (0, [wireWord45, wireWord5, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l16Dead : optimized 5 r32l16.1 r32l16.2 = false := by decide +kernel
def r32l17 : S := (0, [4287347630775668704, wireWord5, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l17Dead : optimized 5 r32l17.1 r32l17.2 = false := by decide +kernel
def r32l18 : S := (0, [wireWord47, wireWord5, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l18Dead : optimized 5 r32l18.1 r32l18.2 = false := by decide +kernel
def r32l19 : S := (0, [2453374311469682656, wireWord5, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l19Dead : optimized 5 r32l19.1 r32l19.2 = false := by decide +kernel
def r32l20 : S := (1, [wireWord10, wireWord0, wireWord5, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l20Dead : optimized 5 r32l20.1 r32l20.2 = false := by decide +kernel
def r32l21 : S := (0, [wireWord10, wireWord2, wireWord0, wireWord5, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l21Dead : optimized 5 r32l21.1 r32l21.2 = false := by decide +kernel
def r32l22 : S := (0, [wireWord30, wireWord2, wireWord0, wireWord5, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l22Dead : optimized 5 r32l22.1 r32l22.2 = false := by decide +kernel
def r32l23 : S := (0, [wireWord31, wireWord2, wireWord0, wireWord5, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l23Dead : optimized 5 r32l23.1 r32l23.2 = false := by decide +kernel
def r32l24 : S := (1, [wireWord12, wireWord0, wireWord5, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l24Dead : optimized 5 r32l24.1 r32l24.2 = false := by decide +kernel
def r32l25 : S := (0, [wireWord12, wireWord2, wireWord0, wireWord5, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l25Dead : optimized 5 r32l25.1 r32l25.2 = false := by decide +kernel
def r32l26 : S := (0, [wireWord40, wireWord2, wireWord1, wireWord5, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l26Dead : optimized 5 r32l26.1 r32l26.2 = false := by decide +kernel
def r32l27 : S := (1, [wireWord13, wireWord1, wireWord5, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l27Dead : optimized 5 r32l27.1 r32l27.2 = false := by decide +kernel
def r32l28 : S := (0, [wireWord13, wireWord2, wireWord1, wireWord5, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l28Dead : optimized 5 r32l28.1 r32l28.2 = false := by decide +kernel
def r32l29 : S := (1, [wireWord11, wireWord1, wireWord5, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l29Dead : optimized 5 r32l29.1 r32l29.2 = false := by decide +kernel
def r32l30 : S := (0, [wireWord11, wireWord2, wireWord1, wireWord5, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l30Dead : optimized 5 r32l30.1 r32l30.2 = false := by decide +kernel
def r32l31 : S := (0, [wireWord39, wireWord2, wireWord1, wireWord5, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l31Dead : optimized 5 r32l31.1 r32l31.2 = false := by decide +kernel
def r32l32 : S := (2, [wireWord6, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l32Dead : optimized 5 r32l32.1 r32l32.2 = false := by decide +kernel
def r32l33 : S := (1, [wireWord6, wireWord2, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l33Dead : optimized 5 r32l33.1 r32l33.2 = false := by decide +kernel
def r32l34 : S := (1, [wireWord6, wireWord4, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l34Dead : optimized 5 r32l34.1 r32l34.2 = false := by decide +kernel
def r32l35 : S := (0, [wireWord6, wireWord2, wireWord4, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l35Dead : optimized 5 r32l35.1 r32l35.2 = false := by decide +kernel
def r32l36 : S := (0, [wireWord43, wireWord2, wireWord4, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l36Dead : optimized 5 r32l36.1 r32l36.2 = false := by decide +kernel
def r32l37 : S := (1, [wireWord8, wireWord2, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l37Dead : optimized 5 r32l37.1 r32l37.2 = false := by decide +kernel
def r32l38 : S := (0, [wireWord8, wireWord2, wireWord4, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l38Dead : optimized 5 r32l38.1 r32l38.2 = false := by decide +kernel
def r32l39 : S := (1, [wireWord25, wireWord4, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l39Dead : optimized 5 r32l39.1 r32l39.2 = false := by decide +kernel
def r32l40 : S := (0, [wireWord25, wireWord2, wireWord4, wireWord5, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l40Dead : optimized 5 r32l40.1 r32l40.2 = false := by decide +kernel
def r32l41 : S := (0, [wireWord9, wireWord0, wireWord1, wireWord5, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l41Dead : optimized 5 r32l41.1 r32l41.2 = false := by decide +kernel
def r32l42 : S := (0, [wireWord41, wireWord0, wireWord1, wireWord5, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l42Dead : optimized 5 r32l42.1 r32l42.2 = false := by decide +kernel
def r32l43 : S := (0, [wireWord26, wireWord0, wireWord1, wireWord5, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l43Dead : optimized 5 r32l43.1 r32l43.2 = false := by decide +kernel
def r32l44 : S := (0, [wireWord42, wireWord0, wireWord1, wireWord5, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r32l44Dead : optimized 5 r32l44.1 r32l44.2 = false := by decide +kernel
def r32l45 : S := (0, [wireWord28, wireWord0, wireWord4, wireWord5, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l45Dead : optimized 5 r32l45.1 r32l45.2 = false := by decide +kernel
def r32l46 : S := (0, [wireWord18, wireWord0, wireWord4, wireWord5, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l46Dead : optimized 5 r32l46.1 r32l46.2 = false := by decide +kernel
def r32l47 : S := (0, [wireWord36, wireWord0, wireWord4, wireWord5, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l47Dead : optimized 5 r32l47.1 r32l47.2 = false := by decide +kernel
def r32l48 : S := (0, [wireWord37, wireWord0, wireWord4, wireWord5, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r32l48Dead : optimized 5 r32l48.1 r32l48.2 = false := by decide +kernel
def r32l49 : S := (0, [wireWord21, wireWord1, wireWord4, wireWord5, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r32l49Dead : optimized 5 r32l49.1 r32l49.2 = false := by decide +kernel
def r32l50 : S := (0, [wireWord38, wireWord1, wireWord4, wireWord5, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r32l50Dead : optimized 5 r32l50.1 r32l50.2 = false := by decide +kernel
def r32l51 : S := (0, [wireWord29, wireWord1, wireWord4, wireWord5, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r32l51Dead : optimized 5 r32l51.1 r32l51.2 = false := by decide +kernel
def r32l52 : S := (0, [wireWord22, wireWord1, wireWord4, wireWord5, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r32l52Dead : optimized 5 r32l52.1 r32l52.2 = false := by decide +kernel
theorem rootCell32Dead : optimized 6 rootCell32.1 rootCell32.2 = false := by
  have kids : nexts (rootCell32.1, rootCell32.2) = [r32l0,r32l1,r32l2,r32l3,r32l4,r32l5,r32l6,r32l7,r32l8,r32l9,r32l10,r32l11,r32l12,r32l13,r32l14,r32l15,r32l16,r32l17,r32l18,r32l19,r32l20,r32l21,r32l22,r32l23,r32l24,r32l25,r32l26,r32l27,r32l28,r32l29,r32l30,r32l31,r32l32,r32l33,r32l34,r32l35,r32l36,r32l37,r32l38,r32l39,r32l40,r32l41,r32l42,r32l43,r32l44,r32l45,r32l46,r32l47,r32l48,r32l49,r32l50,r32l51,r32l52] := by decide +kernel
  have stop : (rootCell32.2 == [goal] || rootCell32.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r32l0Dead, r32l1Dead, r32l2Dead, r32l3Dead, r32l4Dead, r32l5Dead, r32l6Dead, r32l7Dead, r32l8Dead, r32l9Dead, r32l10Dead, r32l11Dead, r32l12Dead, r32l13Dead, r32l14Dead, r32l15Dead, r32l16Dead, r32l17Dead, r32l18Dead, r32l19Dead, r32l20Dead, r32l21Dead, r32l22Dead, r32l23Dead, r32l24Dead, r32l25Dead, r32l26Dead, r32l27Dead, r32l28Dead, r32l29Dead, r32l30Dead, r32l31Dead, r32l32Dead, r32l33Dead, r32l34Dead, r32l35Dead, r32l36Dead, r32l37Dead, r32l38Dead, r32l39Dead, r32l40Dead, r32l41Dead, r32l42Dead, r32l43Dead, r32l44Dead, r32l45Dead, r32l46Dead, r32l47Dead, r32l48Dead, r32l49Dead, r32l50Dead, r32l51Dead, r32l52Dead]
def rootCell33 : S := (1, [wireWord5, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
def r33l0 : S := (1, [wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l0Dead : optimized 5 r33l0.1 r33l0.2 = false := by decide +kernel
def r33l1 : S := (0, [wireWord5, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l1Dead : optimized 5 r33l1.1 r33l1.2 = false := by decide +kernel
def r33l2 : S := (0, [wireWord5, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l2Dead : optimized 5 r33l2.1 r33l2.2 = false := by decide +kernel
def r33l3 : S := (1, [wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l3Dead : optimized 5 r33l3.1 r33l3.2 = false := by decide +kernel
def r33l4 : S := (0, [wireWord3, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l4Dead : optimized 5 r33l4.1 r33l4.2 = false := by decide +kernel
def r33l5 : S := (0, [wireWord3, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l5Dead : optimized 5 r33l5.1 r33l5.2 = false := by decide +kernel
def r33l6 : S := (0, [0, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l6Dead : optimized 5 r33l6.1 r33l6.2 = false := by decide +kernel
def r33l7 : S := (0, [0, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l7Dead : optimized 5 r33l7.1 r33l7.2 = false := by decide +kernel
def r33l8 : S := (0, [wireWord24, wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l8Dead : optimized 5 r33l8.1 r33l8.2 = false := by decide +kernel
def r33l9 : S := (0, [wireWord24, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l9Dead : optimized 5 r33l9.1 r33l9.2 = false := by decide +kernel
def r33l10 : S := (0, [wireWord5, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l10Dead : optimized 5 r33l10.1 r33l10.2 = false := by decide +kernel
def r33l11 : S := (1, [wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l11Dead : optimized 5 r33l11.1 r33l11.2 = false := by decide +kernel
def r33l12 : S := (0, [wireWord2, wireWord5, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l12Dead : optimized 5 r33l12.1 r33l12.2 = false := by decide +kernel
def r33l13 : S := (0, [wireWord2, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l13Dead : optimized 5 r33l13.1 r33l13.2 = false := by decide +kernel
def r33l14 : S := (0, [0, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l14Dead : optimized 5 r33l14.1 r33l14.2 = false := by decide +kernel
def r33l15 : S := (0, [wireWord7, wireWord5, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l15Dead : optimized 5 r33l15.1 r33l15.2 = false := by decide +kernel
def r33l16 : S := (0, [wireWord7, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l16Dead : optimized 5 r33l16.1 r33l16.2 = false := by decide +kernel
def r33l17 : S := (0, [wireWord49, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l17Dead : optimized 5 r33l17.1 r33l17.2 = false := by decide +kernel
def r33l18 : S := (0, [4611686018138469229, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l18Dead : optimized 5 r33l18.1 r33l18.2 = false := by decide +kernel
def r33l19 : S := (0, [wireWord52, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l19Dead : optimized 5 r33l19.1 r33l19.2 = false := by decide +kernel
def r33l20 : S := (0, [2777712698832483181, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l20Dead : optimized 5 r33l20.1 r33l20.2 = false := by decide +kernel
def r33l21 : S := (0, [wireWord57, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l21Dead : optimized 5 r33l21.1 r33l21.2 = false := by decide +kernel
def r33l22 : S := (0, [2304681786975161490, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l22Dead : optimized 5 r33l22.1 r33l22.2 = false := by decide +kernel
def r33l23 : S := (0, [wireWord60, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l23Dead : optimized 5 r33l23.1 r33l23.2 = false := by decide +kernel
def r33l24 : S := (0, [470708467669175442, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l24Dead : optimized 5 r33l24.1 r33l24.2 = false := by decide +kernel
def r33l25 : S := (0, [wireWord45, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l25Dead : optimized 5 r33l25.1 r33l25.2 = false := by decide +kernel
def r33l26 : S := (0, [4287347630775668704, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l26Dead : optimized 5 r33l26.1 r33l26.2 = false := by decide +kernel
def r33l27 : S := (0, [wireWord47, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l27Dead : optimized 5 r33l27.1 r33l27.2 = false := by decide +kernel
def r33l28 : S := (0, [2453374311469682656, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l28Dead : optimized 5 r33l28.1 r33l28.2 = false := by decide +kernel
def r33l29 : S := (0, [wireWord5, wireWord2, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l29Dead : optimized 5 r33l29.1 r33l29.2 = false := by decide +kernel
def r33l30 : S := (1, [wireWord44, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l30Dead : optimized 5 r33l30.1 r33l30.2 = false := by decide +kernel
def r33l31 : S := (0, [wireWord44, wireWord3, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l31Dead : optimized 5 r33l31.1 r33l31.2 = false := by decide +kernel
def r33l32 : S := (0, [wireWord44, wireWord2, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l32Dead : optimized 5 r33l32.1 r33l32.2 = false := by decide +kernel
def r33l33 : S := (0, [wireWord24, wireWord2, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l33Dead : optimized 5 r33l33.1 r33l33.2 = false := by decide +kernel
def r33l34 : S := (1, [wireWord7, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l34Dead : optimized 5 r33l34.1 r33l34.2 = false := by decide +kernel
def r33l35 : S := (0, [wireWord7, wireWord3, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l35Dead : optimized 5 r33l35.1 r33l35.2 = false := by decide +kernel
def r33l36 : S := (0, [wireWord7, wireWord2, wireWord5, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l36Dead : optimized 5 r33l36.1 r33l36.2 = false := by decide +kernel
def r33l37 : S := (0, [wireWord32, wireWord0, wireWord5, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l37Dead : optimized 5 r33l37.1 r33l37.2 = false := by decide +kernel
def r33l38 : S := (0, [wireWord23, wireWord0, wireWord5, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l38Dead : optimized 5 r33l38.1 r33l38.2 = false := by decide +kernel
def r33l39 : S := (0, [wireWord34, wireWord0, wireWord5, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l39Dead : optimized 5 r33l39.1 r33l39.2 = false := by decide +kernel
def r33l40 : S := (0, [wireWord33, wireWord0, wireWord5, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l40Dead : optimized 5 r33l40.1 r33l40.2 = false := by decide +kernel
def r33l41 : S := (0, [wireWord19, wireWord1, wireWord5, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l41Dead : optimized 5 r33l41.1 r33l41.2 = false := by decide +kernel
def r33l42 : S := (0, [wireWord35, wireWord1, wireWord5, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l42Dead : optimized 5 r33l42.1 r33l42.2 = false := by decide +kernel
def r33l43 : S := (0, [wireWord20, wireWord1, wireWord5, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l43Dead : optimized 5 r33l43.1 r33l43.2 = false := by decide +kernel
def r33l44 : S := (0, [wireWord27, wireWord1, wireWord5, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l44Dead : optimized 5 r33l44.1 r33l44.2 = false := by decide +kernel
def r33l45 : S := (0, [wireWord15, wireWord4, wireWord5, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l45Dead : optimized 5 r33l45.1 r33l45.2 = false := by decide +kernel
def r33l46 : S := (0, [wireWord14, wireWord4, wireWord5, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l46Dead : optimized 5 r33l46.1 r33l46.2 = false := by decide +kernel
def r33l47 : S := (0, [wireWord17, wireWord4, wireWord5, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l47Dead : optimized 5 r33l47.1 r33l47.2 = false := by decide +kernel
def r33l48 : S := (0, [wireWord16, wireWord4, wireWord5, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l48Dead : optimized 5 r33l48.1 r33l48.2 = false := by decide +kernel
def r33l49 : S := (0, [wireWord10, wireWord0, wireWord5, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l49Dead : optimized 5 r33l49.1 r33l49.2 = false := by decide +kernel
def r33l50 : S := (0, [wireWord12, wireWord0, wireWord5, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l50Dead : optimized 5 r33l50.1 r33l50.2 = false := by decide +kernel
def r33l51 : S := (0, [wireWord13, wireWord1, wireWord5, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l51Dead : optimized 5 r33l51.1 r33l51.2 = false := by decide +kernel
def r33l52 : S := (0, [wireWord11, wireWord1, wireWord5, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r33l52Dead : optimized 5 r33l52.1 r33l52.2 = false := by decide +kernel
def r33l53 : S := (1, [wireWord6, wireWord5, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l53Dead : optimized 5 r33l53.1 r33l53.2 = false := by decide +kernel
def r33l54 : S := (0, [wireWord6, wireWord2, wireWord5, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l54Dead : optimized 5 r33l54.1 r33l54.2 = false := by decide +kernel
def r33l55 : S := (0, [wireWord6, wireWord4, wireWord5, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l55Dead : optimized 5 r33l55.1 r33l55.2 = false := by decide +kernel
def r33l56 : S := (0, [wireWord8, wireWord2, wireWord5, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l56Dead : optimized 5 r33l56.1 r33l56.2 = false := by decide +kernel
def r33l57 : S := (0, [wireWord25, wireWord4, wireWord5, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r33l57Dead : optimized 5 r33l57.1 r33l57.2 = false := by decide +kernel
theorem rootCell33Dead : optimized 6 rootCell33.1 rootCell33.2 = false := by
  have kids : nexts (rootCell33.1, rootCell33.2) = [r33l0,r33l1,r33l2,r33l3,r33l4,r33l5,r33l6,r33l7,r33l8,r33l9,r33l10,r33l11,r33l12,r33l13,r33l14,r33l15,r33l16,r33l17,r33l18,r33l19,r33l20,r33l21,r33l22,r33l23,r33l24,r33l25,r33l26,r33l27,r33l28,r33l29,r33l30,r33l31,r33l32,r33l33,r33l34,r33l35,r33l36,r33l37,r33l38,r33l39,r33l40,r33l41,r33l42,r33l43,r33l44,r33l45,r33l46,r33l47,r33l48,r33l49,r33l50,r33l51,r33l52,r33l53,r33l54,r33l55,r33l56,r33l57] := by decide +kernel
  have stop : (rootCell33.2 == [goal] || rootCell33.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r33l0Dead, r33l1Dead, r33l2Dead, r33l3Dead, r33l4Dead, r33l5Dead, r33l6Dead, r33l7Dead, r33l8Dead, r33l9Dead, r33l10Dead, r33l11Dead, r33l12Dead, r33l13Dead, r33l14Dead, r33l15Dead, r33l16Dead, r33l17Dead, r33l18Dead, r33l19Dead, r33l20Dead, r33l21Dead, r33l22Dead, r33l23Dead, r33l24Dead, r33l25Dead, r33l26Dead, r33l27Dead, r33l28Dead, r33l29Dead, r33l30Dead, r33l31Dead, r33l32Dead, r33l33Dead, r33l34Dead, r33l35Dead, r33l36Dead, r33l37Dead, r33l38Dead, r33l39Dead, r33l40Dead, r33l41Dead, r33l42Dead, r33l43Dead, r33l44Dead, r33l45Dead, r33l46Dead, r33l47Dead, r33l48Dead, r33l49Dead, r33l50Dead, r33l51Dead, r33l52Dead, r33l53Dead, r33l54Dead, r33l55Dead, r33l56Dead, r33l57Dead]
def rootCell34 : S := (1, [wireWord44, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
def r34l0 : S := (1, [wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l0Dead : optimized 5 r34l0.1 r34l0.2 = false := by decide +kernel
def r34l1 : S := (0, [wireWord3, wireWord44, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l1Dead : optimized 5 r34l1.1 r34l1.2 = false := by decide +kernel
def r34l2 : S := (0, [wireWord3, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l2Dead : optimized 5 r34l2.1 r34l2.2 = false := by decide +kernel
def r34l3 : S := (0, [wireWord44, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l3Dead : optimized 5 r34l3.1 r34l3.2 = false := by decide +kernel
def r34l4 : S := (1, [wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l4Dead : optimized 5 r34l4.1 r34l4.2 = false := by decide +kernel
def r34l5 : S := (0, [wireWord7, wireWord44, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l5Dead : optimized 5 r34l5.1 r34l5.2 = false := by decide +kernel
def r34l6 : S := (0, [wireWord7, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l6Dead : optimized 5 r34l6.1 r34l6.2 = false := by decide +kernel
def r34l7 : S := (0, [0, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l7Dead : optimized 5 r34l7.1 r34l7.2 = false := by decide +kernel
def r34l8 : S := (1, [wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l8Dead : optimized 5 r34l8.1 r34l8.2 = false := by decide +kernel
def r34l9 : S := (0, [wireWord2, wireWord44, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l9Dead : optimized 5 r34l9.1 r34l9.2 = false := by decide +kernel
def r34l10 : S := (0, [wireWord2, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l10Dead : optimized 5 r34l10.1 r34l10.2 = false := by decide +kernel
def r34l11 : S := (0, [wireWord44, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l11Dead : optimized 5 r34l11.1 r34l11.2 = false := by decide +kernel
def r34l12 : S := (0, [wireWord24, wireWord44, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l12Dead : optimized 5 r34l12.1 r34l12.2 = false := by decide +kernel
def r34l13 : S := (0, [wireWord24, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l13Dead : optimized 5 r34l13.1 r34l13.2 = false := by decide +kernel
def r34l14 : S := (0, [0, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l14Dead : optimized 5 r34l14.1 r34l14.2 = false := by decide +kernel
def r34l15 : S := (0, [3687880394864096012, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l15Dead : optimized 5 r34l15.1 r34l15.2 = false := by decide +kernel
def r34l16 : S := (0, [4611686018410610557, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l16Dead : optimized 5 r34l16.1 r34l16.2 = false := by decide +kernel
def r34l17 : S := (0, [599546100336004112, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l17Dead : optimized 5 r34l17.1 r34l17.2 = false := by decide +kernel
def r34l18 : S := (0, [324259523210510433, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l18Dead : optimized 5 r34l18.1 r34l18.2 = false := by decide +kernel
def r34l19 : S := (0, [746276518412848144, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l19Dead : optimized 5 r34l19.1 r34l19.2 = false := by decide +kernel
def r34l20 : S := (0, [4611686018410610590, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l20Dead : optimized 5 r34l20.1 r34l20.2 = false := by decide +kernel
def r34l21 : S := (0, [3541149976787251980, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l21Dead : optimized 5 r34l21.1 r34l21.2 = false := by decide +kernel
def r34l22 : S := (0, [324259523210510466, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l22Dead : optimized 5 r34l22.1 r34l22.2 = false := by decide +kernel
def r34l23 : S := (1, [3133985960203128576, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l23Dead : optimized 5 r34l23.1 r34l23.2 = false := by decide +kernel
def r34l24 : S := (0, [3133985960203128576, wireWord44, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l24Dead : optimized 5 r34l24.1 r34l24.2 = false := by decide +kernel
def r34l25 : S := (0, [3133985960203128576, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l25Dead : optimized 5 r34l25.1 r34l25.2 = false := by decide +kernel
def r34l26 : S := (0, [4287426838797484028, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l26Dead : optimized 5 r34l26.1 r34l26.2 = false := by decide +kernel
def r34l27 : S := (1, [1153440534996971548, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l27Dead : optimized 5 r34l27.1 r34l27.2 = false := by decide +kernel
def r34l28 : S := (0, [1153440534996971548, wireWord44, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l28Dead : optimized 5 r34l28.1 r34l28.2 = false := by decide +kernel
def r34l29 : S := (0, [1153440534996971548, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l29Dead : optimized 5 r34l29.1 r34l29.2 = false := by decide +kernel
def r34l30 : S := (0, [343597383904, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l30Dead : optimized 5 r34l30.1 r34l30.2 = false := by decide +kernel
def r34l31 : S := (1, [wireWord5, wireWord44, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l31Dead : optimized 5 r34l31.1 r34l31.2 = false := by decide +kernel
def r34l32 : S := (0, [wireWord5, wireWord3, wireWord44, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l32Dead : optimized 5 r34l32.1 r34l32.2 = false := by decide +kernel
def r34l33 : S := (0, [wireWord5, wireWord2, wireWord44, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l33Dead : optimized 5 r34l33.1 r34l33.2 = false := by decide +kernel
def r34l34 : S := (0, [wireWord24, wireWord3, wireWord44, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l34Dead : optimized 5 r34l34.1 r34l34.2 = false := by decide +kernel
def r34l35 : S := (0, [wireWord7, wireWord2, wireWord44, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r34l35Dead : optimized 5 r34l35.1 r34l35.2 = false := by decide +kernel
def r34l36 : S := (0, [wireWord6, wireWord2, wireWord44, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l36Dead : optimized 5 r34l36.1 r34l36.2 = false := by decide +kernel
def r34l37 : S := (0, [wireWord8, wireWord2, wireWord44, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r34l37Dead : optimized 5 r34l37.1 r34l37.2 = false := by decide +kernel
theorem rootCell34Dead : optimized 6 rootCell34.1 rootCell34.2 = false := by
  have kids : nexts (rootCell34.1, rootCell34.2) = [r34l0,r34l1,r34l2,r34l3,r34l4,r34l5,r34l6,r34l7,r34l8,r34l9,r34l10,r34l11,r34l12,r34l13,r34l14,r34l15,r34l16,r34l17,r34l18,r34l19,r34l20,r34l21,r34l22,r34l23,r34l24,r34l25,r34l26,r34l27,r34l28,r34l29,r34l30,r34l31,r34l32,r34l33,r34l34,r34l35,r34l36,r34l37] := by decide +kernel
  have stop : (rootCell34.2 == [goal] || rootCell34.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r34l0Dead, r34l1Dead, r34l2Dead, r34l3Dead, r34l4Dead, r34l5Dead, r34l6Dead, r34l7Dead, r34l8Dead, r34l9Dead, r34l10Dead, r34l11Dead, r34l12Dead, r34l13Dead, r34l14Dead, r34l15Dead, r34l16Dead, r34l17Dead, r34l18Dead, r34l19Dead, r34l20Dead, r34l21Dead, r34l22Dead, r34l23Dead, r34l24Dead, r34l25Dead, r34l26Dead, r34l27Dead, r34l28Dead, r34l29Dead, r34l30Dead, r34l31Dead, r34l32Dead, r34l33Dead, r34l34Dead, r34l35Dead, r34l36Dead, r34l37Dead]
def rootCell35 : S := (1, [wireWord24, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
def r35l0 : S := (0, [wireWord24, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l0Dead : optimized 5 r35l0.1 r35l0.2 = false := by decide +kernel
def r35l1 : S := (1, [wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l1Dead : optimized 5 r35l1.1 r35l1.2 = false := by decide +kernel
def r35l2 : S := (0, [wireWord3, wireWord24, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l2Dead : optimized 5 r35l2.1 r35l2.2 = false := by decide +kernel
def r35l3 : S := (0, [wireWord3, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l3Dead : optimized 5 r35l3.1 r35l3.2 = false := by decide +kernel
def r35l4 : S := (0, [0, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l4Dead : optimized 5 r35l4.1 r35l4.2 = false := by decide +kernel
def r35l5 : S := (1, [wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l5Dead : optimized 5 r35l5.1 r35l5.2 = false := by decide +kernel
def r35l6 : S := (0, [wireWord5, wireWord24, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l6Dead : optimized 5 r35l6.1 r35l6.2 = false := by decide +kernel
def r35l7 : S := (0, [wireWord5, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l7Dead : optimized 5 r35l7.1 r35l7.2 = false := by decide +kernel
def r35l8 : S := (0, [0, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l8Dead : optimized 5 r35l8.1 r35l8.2 = false := by decide +kernel
def r35l9 : S := (0, [wireWord44, wireWord24, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l9Dead : optimized 5 r35l9.1 r35l9.2 = false := by decide +kernel
def r35l10 : S := (0, [wireWord44, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l10Dead : optimized 5 r35l10.1 r35l10.2 = false := by decide +kernel
def r35l11 : S := (0, [wireWord24, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l11Dead : optimized 5 r35l11.1 r35l11.2 = false := by decide +kernel
def r35l12 : S := (1, [wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l12Dead : optimized 5 r35l12.1 r35l12.2 = false := by decide +kernel
def r35l13 : S := (0, [wireWord2, wireWord24, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l13Dead : optimized 5 r35l13.1 r35l13.2 = false := by decide +kernel
def r35l14 : S := (0, [wireWord2, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l14Dead : optimized 5 r35l14.1 r35l14.2 = false := by decide +kernel
def r35l15 : S := (0, [2791728743180, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l15Dead : optimized 5 r35l15.1 r35l15.2 = false := by decide +kernel
def r35l16 : S := (0, [4012139918074609533, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l16Dead : optimized 5 r35l16.1 r35l16.2 = false := by decide +kernel
def r35l17 : S := (0, [3088, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l17Dead : optimized 5 r35l17.1 r35l17.2 = false := by decide +kernel
def r35l18 : S := (0, [4012137126345863265, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l18Dead : optimized 5 r35l18.1 r35l18.2 = false := by decide +kernel
def r35l19 : S := (0, [2791728745488, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l19Dead : optimized 5 r35l19.1 r35l19.2 = false := by decide +kernel
def r35l20 : S := (0, [1070536041623359390, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l20Dead : optimized 5 r35l20.1 r35l20.2 = false := by decide +kernel
def r35l21 : S := (0, [780, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l21Dead : optimized 5 r35l21.1 r35l21.2 = false := by decide +kernel
def r35l22 : S := (0, [1070533249894613122, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l22Dead : optimized 5 r35l22.1 r35l22.2 = false := by decide +kernel
def r35l23 : S := (0, [2748779073280, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l23Dead : optimized 5 r35l23.1 r35l23.2 = false := by decide +kernel
def r35l24 : S := (1, [3133986346750185468, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l24Dead : optimized 5 r35l24.1 r35l24.2 = false := by decide +kernel
def r35l25 : S := (0, [3133986346750185468, wireWord24, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l25Dead : optimized 5 r35l25.1 r35l25.2 = false := by decide +kernel
def r35l26 : S := (0, [3133986346750185468, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l26Dead : optimized 5 r35l26.1 r35l26.2 = false := by decide +kernel
def r35l27 : S := (0, [42949672988, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l27Dead : optimized 5 r35l27.1 r35l27.2 = false := by decide +kernel
def r35l28 : S := (1, [3133983555021439200, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l28Dead : optimized 5 r35l28.1 r35l28.2 = false := by decide +kernel
def r35l29 : S := (0, [3133983555021439200, wireWord24, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l29Dead : optimized 5 r35l29.1 r35l29.2 = false := by decide +kernel
def r35l30 : S := (0, [3133983555021439200, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l30Dead : optimized 5 r35l30.1 r35l30.2 = false := by decide +kernel
def r35l31 : S := (0, [wireWord5, wireWord2, wireWord24, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l31Dead : optimized 5 r35l31.1 r35l31.2 = false := by decide +kernel
def r35l32 : S := (0, [wireWord44, wireWord3, wireWord24, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l32Dead : optimized 5 r35l32.1 r35l32.2 = false := by decide +kernel
def r35l33 : S := (1, [wireWord7, wireWord24, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l33Dead : optimized 5 r35l33.1 r35l33.2 = false := by decide +kernel
def r35l34 : S := (0, [wireWord7, wireWord3, wireWord24, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l34Dead : optimized 5 r35l34.1 r35l34.2 = false := by decide +kernel
def r35l35 : S := (0, [wireWord7, wireWord2, wireWord24, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l35Dead : optimized 5 r35l35.1 r35l35.2 = false := by decide +kernel
def r35l36 : S := (0, [wireWord10, wireWord0, wireWord24, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l36Dead : optimized 5 r35l36.1 r35l36.2 = false := by decide +kernel
def r35l37 : S := (0, [wireWord12, wireWord0, wireWord24, wireWord3, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l37Dead : optimized 5 r35l37.1 r35l37.2 = false := by decide +kernel
def r35l38 : S := (0, [wireWord13, wireWord1, wireWord24, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l38Dead : optimized 5 r35l38.1 r35l38.2 = false := by decide +kernel
def r35l39 : S := (0, [wireWord11, wireWord1, wireWord24, wireWord3, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r35l39Dead : optimized 5 r35l39.1 r35l39.2 = false := by decide +kernel
def r35l40 : S := (1, [wireWord6, wireWord24, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l40Dead : optimized 5 r35l40.1 r35l40.2 = false := by decide +kernel
def r35l41 : S := (0, [wireWord6, wireWord2, wireWord24, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l41Dead : optimized 5 r35l41.1 r35l41.2 = false := by decide +kernel
def r35l42 : S := (0, [wireWord6, wireWord4, wireWord24, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l42Dead : optimized 5 r35l42.1 r35l42.2 = false := by decide +kernel
def r35l43 : S := (0, [wireWord8, wireWord2, wireWord24, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l43Dead : optimized 5 r35l43.1 r35l43.2 = false := by decide +kernel
def r35l44 : S := (0, [wireWord25, wireWord4, wireWord24, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r35l44Dead : optimized 5 r35l44.1 r35l44.2 = false := by decide +kernel
theorem rootCell35Dead : optimized 6 rootCell35.1 rootCell35.2 = false := by
  have kids : nexts (rootCell35.1, rootCell35.2) = [r35l0,r35l1,r35l2,r35l3,r35l4,r35l5,r35l6,r35l7,r35l8,r35l9,r35l10,r35l11,r35l12,r35l13,r35l14,r35l15,r35l16,r35l17,r35l18,r35l19,r35l20,r35l21,r35l22,r35l23,r35l24,r35l25,r35l26,r35l27,r35l28,r35l29,r35l30,r35l31,r35l32,r35l33,r35l34,r35l35,r35l36,r35l37,r35l38,r35l39,r35l40,r35l41,r35l42,r35l43,r35l44] := by decide +kernel
  have stop : (rootCell35.2 == [goal] || rootCell35.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r35l0Dead, r35l1Dead, r35l2Dead, r35l3Dead, r35l4Dead, r35l5Dead, r35l6Dead, r35l7Dead, r35l8Dead, r35l9Dead, r35l10Dead, r35l11Dead, r35l12Dead, r35l13Dead, r35l14Dead, r35l15Dead, r35l16Dead, r35l17Dead, r35l18Dead, r35l19Dead, r35l20Dead, r35l21Dead, r35l22Dead, r35l23Dead, r35l24Dead, r35l25Dead, r35l26Dead, r35l27Dead, r35l28Dead, r35l29Dead, r35l30Dead, r35l31Dead, r35l32Dead, r35l33Dead, r35l34Dead, r35l35Dead, r35l36Dead, r35l37Dead, r35l38Dead, r35l39Dead, r35l40Dead, r35l41Dead, r35l42Dead, r35l43Dead, r35l44Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell36 : S := (2, [wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
def r36l0 : S := (1, [wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l0Dead : optimized 5 r36l0.1 r36l0.2 = false := by decide +kernel
def r36l1 : S := (0, [wireWord7, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l1Dead : optimized 5 r36l1.1 r36l1.2 = false := by decide +kernel
def r36l2 : S := (1, [wireWord2, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l2Dead : optimized 5 r36l2.1 r36l2.2 = false := by decide +kernel
def r36l3 : S := (0, [wireWord2, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l3Dead : optimized 5 r36l3.1 r36l3.2 = false := by decide +kernel
def r36l4 : S := (0, [0, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l4Dead : optimized 5 r36l4.1 r36l4.2 = false := by decide +kernel
def r36l5 : S := (1, [wireWord5, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l5Dead : optimized 5 r36l5.1 r36l5.2 = false := by decide +kernel
def r36l6 : S := (1, [wireWord5, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l6Dead : optimized 5 r36l6.1 r36l6.2 = false := by decide +kernel
def r36l7 : S := (0, [wireWord5, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l7Dead : optimized 5 r36l7.1 r36l7.2 = false := by decide +kernel
def r36l8 : S := (0, [wireWord51, wireWord7, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l8Dead : optimized 5 r36l8.1 r36l8.2 = false := by decide +kernel
def r36l9 : S := (0, [4012139918346744685, wireWord7, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l9Dead : optimized 5 r36l9.1 r36l9.2 = false := by decide +kernel
def r36l10 : S := (0, [wireWord50, wireWord7, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l10Dead : optimized 5 r36l10.1 r36l10.2 = false := by decide +kernel
def r36l11 : S := (0, [1558689534181376877, wireWord7, wireWord0, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l11Dead : optimized 5 r36l11.1 r36l11.2 = false := by decide +kernel
def r36l12 : S := (0, [wireWord59, wireWord7, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l12Dead : optimized 5 r36l12.1 r36l12.2 = false := by decide +kernel
def r36l13 : S := (0, [3377540273058806930, wireWord7, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l13Dead : optimized 5 r36l13.1 r36l13.2 = false := by decide +kernel
def r36l14 : S := (0, [wireWord58, wireWord7, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l14Dead : optimized 5 r36l14.1 r36l14.2 = false := by decide +kernel
def r36l15 : S := (0, [924089888893439122, wireWord7, wireWord1, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l15Dead : optimized 5 r36l15.1 r36l15.2 = false := by decide +kernel
def r36l16 : S := (0, [wireWord48, wireWord7, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l16Dead : optimized 5 r36l16.1 r36l16.2 = false := by decide +kernel
def r36l17 : S := (0, [3134065468872654816, wireWord7, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l17Dead : optimized 5 r36l17.1 r36l17.2 = false := by decide +kernel
def r36l18 : S := (0, [wireWord46, wireWord7, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l18Dead : optimized 5 r36l18.1 r36l18.2 = false := by decide +kernel
def r36l19 : S := (0, [680615084707287008, wireWord7, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l19Dead : optimized 5 r36l19.1 r36l19.2 = false := by decide +kernel
def r36l20 : S := (0, [wireWord10, wireWord2, wireWord0, wireWord7, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l20Dead : optimized 5 r36l20.1 r36l20.2 = false := by decide +kernel
def r36l21 : S := (0, [wireWord30, wireWord2, wireWord0, wireWord7, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l21Dead : optimized 5 r36l21.1 r36l21.2 = false := by decide +kernel
def r36l22 : S := (0, [wireWord31, wireWord2, wireWord0, wireWord7, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l22Dead : optimized 5 r36l22.1 r36l22.2 = false := by decide +kernel
def r36l23 : S := (0, [wireWord12, wireWord2, wireWord0, wireWord7, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l23Dead : optimized 5 r36l23.1 r36l23.2 = false := by decide +kernel
def r36l24 : S := (0, [wireWord40, wireWord2, wireWord1, wireWord7, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l24Dead : optimized 5 r36l24.1 r36l24.2 = false := by decide +kernel
def r36l25 : S := (0, [wireWord13, wireWord2, wireWord1, wireWord7, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l25Dead : optimized 5 r36l25.1 r36l25.2 = false := by decide +kernel
def r36l26 : S := (0, [wireWord11, wireWord2, wireWord1, wireWord7, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l26Dead : optimized 5 r36l26.1 r36l26.2 = false := by decide +kernel
def r36l27 : S := (0, [wireWord39, wireWord2, wireWord1, wireWord7, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l27Dead : optimized 5 r36l27.1 r36l27.2 = false := by decide +kernel
def r36l28 : S := (1, [wireWord6, wireWord2, wireWord7, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l28Dead : optimized 5 r36l28.1 r36l28.2 = false := by decide +kernel
def r36l29 : S := (0, [wireWord6, wireWord2, wireWord4, wireWord7, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l29Dead : optimized 5 r36l29.1 r36l29.2 = false := by decide +kernel
def r36l30 : S := (0, [wireWord43, wireWord2, wireWord4, wireWord7, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l30Dead : optimized 5 r36l30.1 r36l30.2 = false := by decide +kernel
def r36l31 : S := (1, [wireWord8, wireWord2, wireWord7, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l31Dead : optimized 5 r36l31.1 r36l31.2 = false := by decide +kernel
def r36l32 : S := (0, [wireWord8, wireWord2, wireWord4, wireWord7, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l32Dead : optimized 5 r36l32.1 r36l32.2 = false := by decide +kernel
def r36l33 : S := (0, [wireWord25, wireWord2, wireWord4, wireWord7, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l33Dead : optimized 5 r36l33.1 r36l33.2 = false := by decide +kernel
def r36l34 : S := (0, [wireWord9, wireWord0, wireWord1, wireWord7, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l34Dead : optimized 5 r36l34.1 r36l34.2 = false := by decide +kernel
def r36l35 : S := (0, [wireWord41, wireWord0, wireWord1, wireWord7, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l35Dead : optimized 5 r36l35.1 r36l35.2 = false := by decide +kernel
def r36l36 : S := (0, [wireWord26, wireWord0, wireWord1, wireWord7, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l36Dead : optimized 5 r36l36.1 r36l36.2 = false := by decide +kernel
def r36l37 : S := (0, [wireWord42, wireWord0, wireWord1, wireWord7, wireWord2, wireWord4])
set_option maxHeartbeats 0 in
theorem r36l37Dead : optimized 5 r36l37.1 r36l37.2 = false := by decide +kernel
def r36l38 : S := (0, [wireWord28, wireWord0, wireWord4, wireWord7, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l38Dead : optimized 5 r36l38.1 r36l38.2 = false := by decide +kernel
def r36l39 : S := (0, [wireWord18, wireWord0, wireWord4, wireWord7, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l39Dead : optimized 5 r36l39.1 r36l39.2 = false := by decide +kernel
def r36l40 : S := (0, [wireWord36, wireWord0, wireWord4, wireWord7, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l40Dead : optimized 5 r36l40.1 r36l40.2 = false := by decide +kernel
def r36l41 : S := (0, [wireWord37, wireWord0, wireWord4, wireWord7, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r36l41Dead : optimized 5 r36l41.1 r36l41.2 = false := by decide +kernel
def r36l42 : S := (0, [wireWord21, wireWord1, wireWord4, wireWord7, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r36l42Dead : optimized 5 r36l42.1 r36l42.2 = false := by decide +kernel
def r36l43 : S := (0, [wireWord38, wireWord1, wireWord4, wireWord7, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r36l43Dead : optimized 5 r36l43.1 r36l43.2 = false := by decide +kernel
def r36l44 : S := (0, [wireWord29, wireWord1, wireWord4, wireWord7, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r36l44Dead : optimized 5 r36l44.1 r36l44.2 = false := by decide +kernel
def r36l45 : S := (0, [wireWord22, wireWord1, wireWord4, wireWord7, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r36l45Dead : optimized 5 r36l45.1 r36l45.2 = false := by decide +kernel
theorem rootCell36Dead : optimized 6 rootCell36.1 rootCell36.2 = false := by
  have kids : nexts (rootCell36.1, rootCell36.2) = [r36l0,r36l1,r36l2,r36l3,r36l4,r36l5,r36l6,r36l7,r36l8,r36l9,r36l10,r36l11,r36l12,r36l13,r36l14,r36l15,r36l16,r36l17,r36l18,r36l19,r36l20,r36l21,r36l22,r36l23,r36l24,r36l25,r36l26,r36l27,r36l28,r36l29,r36l30,r36l31,r36l32,r36l33,r36l34,r36l35,r36l36,r36l37,r36l38,r36l39,r36l40,r36l41,r36l42,r36l43,r36l44,r36l45] := by decide +kernel
  have stop : (rootCell36.2 == [goal] || rootCell36.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r36l0Dead, r36l1Dead, r36l2Dead, r36l3Dead, r36l4Dead, r36l5Dead, r36l6Dead, r36l7Dead, r36l8Dead, r36l9Dead, r36l10Dead, r36l11Dead, r36l12Dead, r36l13Dead, r36l14Dead, r36l15Dead, r36l16Dead, r36l17Dead, r36l18Dead, r36l19Dead, r36l20Dead, r36l21Dead, r36l22Dead, r36l23Dead, r36l24Dead, r36l25Dead, r36l26Dead, r36l27Dead, r36l28Dead, r36l29Dead, r36l30Dead, r36l31Dead, r36l32Dead, r36l33Dead, r36l34Dead, r36l35Dead, r36l36Dead, r36l37Dead, r36l38Dead, r36l39Dead, r36l40Dead, r36l41Dead, r36l42Dead, r36l43Dead, r36l44Dead, r36l45Dead]
def rootCell37 : S := (1, [wireWord7, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
def r37l0 : S := (0, [0, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l0Dead : optimized 5 r37l0.1 r37l0.2 = false := by decide +kernel
def r37l1 : S := (0, [0, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l1Dead : optimized 5 r37l1.1 r37l1.2 = false := by decide +kernel
def r37l2 : S := (0, [wireWord44, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l2Dead : optimized 5 r37l2.1 r37l2.2 = false := by decide +kernel
def r37l3 : S := (0, [wireWord44, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l3Dead : optimized 5 r37l3.1 r37l3.2 = false := by decide +kernel
def r37l4 : S := (1, [wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l4Dead : optimized 5 r37l4.1 r37l4.2 = false := by decide +kernel
def r37l5 : S := (0, [wireWord7, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l5Dead : optimized 5 r37l5.1 r37l5.2 = false := by decide +kernel
def r37l6 : S := (0, [wireWord7, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l6Dead : optimized 5 r37l6.1 r37l6.2 = false := by decide +kernel
def r37l7 : S := (1, [wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l7Dead : optimized 5 r37l7.1 r37l7.2 = false := by decide +kernel
def r37l8 : S := (0, [wireWord3, wireWord7, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l8Dead : optimized 5 r37l8.1 r37l8.2 = false := by decide +kernel
def r37l9 : S := (0, [wireWord3, wireWord3, wireWord2, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l9Dead : optimized 5 r37l9.1 r37l9.2 = false := by decide +kernel
def r37l10 : S := (0, [wireWord7, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l10Dead : optimized 5 r37l10.1 r37l10.2 = false := by decide +kernel
def r37l11 : S := (1, [wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l11Dead : optimized 5 r37l11.1 r37l11.2 = false := by decide +kernel
def r37l12 : S := (0, [wireWord2, wireWord7, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l12Dead : optimized 5 r37l12.1 r37l12.2 = false := by decide +kernel
def r37l13 : S := (0, [wireWord2, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l13Dead : optimized 5 r37l13.1 r37l13.2 = false := by decide +kernel
def r37l14 : S := (0, [0, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l14Dead : optimized 5 r37l14.1 r37l14.2 = false := by decide +kernel
def r37l15 : S := (0, [wireWord5, wireWord7, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l15Dead : optimized 5 r37l15.1 r37l15.2 = false := by decide +kernel
def r37l16 : S := (0, [wireWord5, wireWord2, wireWord3, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l16Dead : optimized 5 r37l16.1 r37l16.2 = false := by decide +kernel
def r37l17 : S := (0, [wireWord51, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l17Dead : optimized 5 r37l17.1 r37l17.2 = false := by decide +kernel
def r37l18 : S := (0, [4012139918346744685, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l18Dead : optimized 5 r37l18.1 r37l18.2 = false := by decide +kernel
def r37l19 : S := (0, [wireWord50, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l19Dead : optimized 5 r37l19.1 r37l19.2 = false := by decide +kernel
def r37l20 : S := (0, [1558689534181376877, wireWord0, wireWord3, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l20Dead : optimized 5 r37l20.1 r37l20.2 = false := by decide +kernel
def r37l21 : S := (0, [wireWord59, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l21Dead : optimized 5 r37l21.1 r37l21.2 = false := by decide +kernel
def r37l22 : S := (0, [3377540273058806930, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l22Dead : optimized 5 r37l22.1 r37l22.2 = false := by decide +kernel
def r37l23 : S := (0, [wireWord58, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l23Dead : optimized 5 r37l23.1 r37l23.2 = false := by decide +kernel
def r37l24 : S := (0, [924089888893439122, wireWord1, wireWord3, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l24Dead : optimized 5 r37l24.1 r37l24.2 = false := by decide +kernel
def r37l25 : S := (0, [wireWord48, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l25Dead : optimized 5 r37l25.1 r37l25.2 = false := by decide +kernel
def r37l26 : S := (0, [3134065468872654816, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l26Dead : optimized 5 r37l26.1 r37l26.2 = false := by decide +kernel
def r37l27 : S := (0, [wireWord46, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l27Dead : optimized 5 r37l27.1 r37l27.2 = false := by decide +kernel
def r37l28 : S := (0, [680615084707287008, wireWord4, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l28Dead : optimized 5 r37l28.1 r37l28.2 = false := by decide +kernel
def r37l29 : S := (1, [wireWord5, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l29Dead : optimized 5 r37l29.1 r37l29.2 = false := by decide +kernel
def r37l30 : S := (0, [wireWord5, wireWord3, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l30Dead : optimized 5 r37l30.1 r37l30.2 = false := by decide +kernel
def r37l31 : S := (0, [wireWord5, wireWord2, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l31Dead : optimized 5 r37l31.1 r37l31.2 = false := by decide +kernel
def r37l32 : S := (0, [wireWord44, wireWord2, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l32Dead : optimized 5 r37l32.1 r37l32.2 = false := by decide +kernel
def r37l33 : S := (1, [wireWord24, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l33Dead : optimized 5 r37l33.1 r37l33.2 = false := by decide +kernel
def r37l34 : S := (0, [wireWord24, wireWord3, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l34Dead : optimized 5 r37l34.1 r37l34.2 = false := by decide +kernel
def r37l35 : S := (0, [wireWord24, wireWord2, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l35Dead : optimized 5 r37l35.1 r37l35.2 = false := by decide +kernel
def r37l36 : S := (0, [wireWord7, wireWord2, wireWord7, wireWord0, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l36Dead : optimized 5 r37l36.1 r37l36.2 = false := by decide +kernel
def r37l37 : S := (0, [wireWord32, wireWord0, wireWord7, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l37Dead : optimized 5 r37l37.1 r37l37.2 = false := by decide +kernel
def r37l38 : S := (0, [wireWord23, wireWord0, wireWord7, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l38Dead : optimized 5 r37l38.1 r37l38.2 = false := by decide +kernel
def r37l39 : S := (0, [wireWord34, wireWord0, wireWord7, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l39Dead : optimized 5 r37l39.1 r37l39.2 = false := by decide +kernel
def r37l40 : S := (0, [wireWord33, wireWord0, wireWord7, wireWord2, wireWord1, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l40Dead : optimized 5 r37l40.1 r37l40.2 = false := by decide +kernel
def r37l41 : S := (0, [wireWord19, wireWord1, wireWord7, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l41Dead : optimized 5 r37l41.1 r37l41.2 = false := by decide +kernel
def r37l42 : S := (0, [wireWord35, wireWord1, wireWord7, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l42Dead : optimized 5 r37l42.1 r37l42.2 = false := by decide +kernel
def r37l43 : S := (0, [wireWord20, wireWord1, wireWord7, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l43Dead : optimized 5 r37l43.1 r37l43.2 = false := by decide +kernel
def r37l44 : S := (0, [wireWord27, wireWord1, wireWord7, wireWord2, wireWord0, wireWord4])
set_option maxHeartbeats 0 in
theorem r37l44Dead : optimized 5 r37l44.1 r37l44.2 = false := by decide +kernel
def r37l45 : S := (0, [wireWord15, wireWord4, wireWord7, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l45Dead : optimized 5 r37l45.1 r37l45.2 = false := by decide +kernel
def r37l46 : S := (0, [wireWord14, wireWord4, wireWord7, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l46Dead : optimized 5 r37l46.1 r37l46.2 = false := by decide +kernel
def r37l47 : S := (0, [wireWord17, wireWord4, wireWord7, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l47Dead : optimized 5 r37l47.1 r37l47.2 = false := by decide +kernel
def r37l48 : S := (0, [wireWord16, wireWord4, wireWord7, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l48Dead : optimized 5 r37l48.1 r37l48.2 = false := by decide +kernel
def r37l49 : S := (0, [wireWord6, wireWord2, wireWord7, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l49Dead : optimized 5 r37l49.1 r37l49.2 = false := by decide +kernel
def r37l50 : S := (0, [wireWord8, wireWord2, wireWord7, wireWord3, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r37l50Dead : optimized 5 r37l50.1 r37l50.2 = false := by decide +kernel
theorem rootCell37Dead : optimized 6 rootCell37.1 rootCell37.2 = false := by
  have kids : nexts (rootCell37.1, rootCell37.2) = [r37l0,r37l1,r37l2,r37l3,r37l4,r37l5,r37l6,r37l7,r37l8,r37l9,r37l10,r37l11,r37l12,r37l13,r37l14,r37l15,r37l16,r37l17,r37l18,r37l19,r37l20,r37l21,r37l22,r37l23,r37l24,r37l25,r37l26,r37l27,r37l28,r37l29,r37l30,r37l31,r37l32,r37l33,r37l34,r37l35,r37l36,r37l37,r37l38,r37l39,r37l40,r37l41,r37l42,r37l43,r37l44,r37l45,r37l46,r37l47,r37l48,r37l49,r37l50] := by decide +kernel
  have stop : (rootCell37.2 == [goal] || rootCell37.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r37l0Dead, r37l1Dead, r37l2Dead, r37l3Dead, r37l4Dead, r37l5Dead, r37l6Dead, r37l7Dead, r37l8Dead, r37l9Dead, r37l10Dead, r37l11Dead, r37l12Dead, r37l13Dead, r37l14Dead, r37l15Dead, r37l16Dead, r37l17Dead, r37l18Dead, r37l19Dead, r37l20Dead, r37l21Dead, r37l22Dead, r37l23Dead, r37l24Dead, r37l25Dead, r37l26Dead, r37l27Dead, r37l28Dead, r37l29Dead, r37l30Dead, r37l31Dead, r37l32Dead, r37l33Dead, r37l34Dead, r37l35Dead, r37l36Dead, r37l37Dead, r37l38Dead, r37l39Dead, r37l40Dead, r37l41Dead, r37l42Dead, r37l43Dead, r37l44Dead, r37l45Dead, r37l46Dead, r37l47Dead, r37l48Dead, r37l49Dead, r37l50Dead]
def rootCell38 : S := (2, [wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
def r38l0 : S := (1, [wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l0Dead : optimized 5 r38l0.1 r38l0.2 = false := by decide +kernel
def r38l1 : S := (0, [wireWord6, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l1Dead : optimized 5 r38l1.1 r38l1.2 = false := by decide +kernel
def r38l2 : S := (1, [wireWord2, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l2Dead : optimized 5 r38l2.1 r38l2.2 = false := by decide +kernel
def r38l3 : S := (0, [wireWord2, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l3Dead : optimized 5 r38l3.1 r38l3.2 = false := by decide +kernel
def r38l4 : S := (0, [0, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l4Dead : optimized 5 r38l4.1 r38l4.2 = false := by decide +kernel
def r38l5 : S := (1, [wireWord8, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l5Dead : optimized 5 r38l5.1 r38l5.2 = false := by decide +kernel
def r38l6 : S := (1, [wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l6Dead : optimized 5 r38l6.1 r38l6.2 = false := by decide +kernel
def r38l7 : S := (0, [wireWord8, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l7Dead : optimized 5 r38l7.1 r38l7.2 = false := by decide +kernel
def r38l8 : S := (0, [wireWord53, wireWord6, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l8Dead : optimized 5 r38l8.1 r38l8.2 = false := by decide +kernel
def r38l9 : S := (0, [4611686017873245037, wireWord6, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l9Dead : optimized 5 r38l9.1 r38l9.2 = false := by decide +kernel
def r38l10 : S := (0, [wireWord56, wireWord6, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l10Dead : optimized 5 r38l10.1 r38l10.2 = false := by decide +kernel
def r38l11 : S := (0, [1477702806449189741, wireWord6, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l11Dead : optimized 5 r38l11.1 r38l11.2 = false := by decide +kernel
def r38l12 : S := (0, [wireWord61, wireWord6, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l12Dead : optimized 5 r38l12.1 r38l12.2 = false := by decide +kernel
def r38l13 : S := (0, [3458606166714518674, wireWord6, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l13Dead : optimized 5 r38l13.1 r38l13.2 = false := by decide +kernel
def r38l14 : S := (0, [wireWord64, wireWord6, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l14Dead : optimized 5 r38l14.1 r38l14.2 = false := by decide +kernel
def r38l15 : S := (0, [324622955290463378, wireWord6, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l15Dead : optimized 5 r38l15.1 r38l15.2 = false := by decide +kernel
def r38l16 : S := (0, [wireWord45, wireWord6, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l16Dead : optimized 5 r38l16.1 r38l16.2 = false := by decide +kernel
def r38l17 : S := (0, [4287347330127957788, wireWord6, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l17Dead : optimized 5 r38l17.1 r38l17.2 = false := by decide +kernel
def r38l18 : S := (0, [wireWord48, wireWord6, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l18Dead : optimized 5 r38l18.1 r38l18.2 = false := by decide +kernel
def r38l19 : S := (0, [1153364118703902492, wireWord6, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l19Dead : optimized 5 r38l19.1 r38l19.2 = false := by decide +kernel
def r38l20 : S := (1, [wireWord10, wireWord0, wireWord6, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l20Dead : optimized 5 r38l20.1 r38l20.2 = false := by decide +kernel
def r38l21 : S := (0, [wireWord10, wireWord2, wireWord0, wireWord6, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l21Dead : optimized 5 r38l21.1 r38l21.2 = false := by decide +kernel
def r38l22 : S := (0, [wireWord30, wireWord2, wireWord0, wireWord6, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l22Dead : optimized 5 r38l22.1 r38l22.2 = false := by decide +kernel
def r38l23 : S := (0, [wireWord31, wireWord2, wireWord0, wireWord6, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l23Dead : optimized 5 r38l23.1 r38l23.2 = false := by decide +kernel
def r38l24 : S := (1, [wireWord12, wireWord0, wireWord6, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l24Dead : optimized 5 r38l24.1 r38l24.2 = false := by decide +kernel
def r38l25 : S := (0, [wireWord12, wireWord2, wireWord0, wireWord6, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l25Dead : optimized 5 r38l25.1 r38l25.2 = false := by decide +kernel
def r38l26 : S := (0, [wireWord40, wireWord2, wireWord1, wireWord6, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l26Dead : optimized 5 r38l26.1 r38l26.2 = false := by decide +kernel
def r38l27 : S := (1, [wireWord13, wireWord1, wireWord6, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l27Dead : optimized 5 r38l27.1 r38l27.2 = false := by decide +kernel
def r38l28 : S := (0, [wireWord13, wireWord2, wireWord1, wireWord6, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l28Dead : optimized 5 r38l28.1 r38l28.2 = false := by decide +kernel
def r38l29 : S := (1, [wireWord11, wireWord1, wireWord6, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l29Dead : optimized 5 r38l29.1 r38l29.2 = false := by decide +kernel
def r38l30 : S := (0, [wireWord11, wireWord2, wireWord1, wireWord6, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l30Dead : optimized 5 r38l30.1 r38l30.2 = false := by decide +kernel
def r38l31 : S := (0, [wireWord39, wireWord2, wireWord1, wireWord6, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l31Dead : optimized 5 r38l31.1 r38l31.2 = false := by decide +kernel
def r38l32 : S := (2, [wireWord5, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l32Dead : optimized 5 r38l32.1 r38l32.2 = false := by decide +kernel
def r38l33 : S := (1, [wireWord5, wireWord2, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l33Dead : optimized 5 r38l33.1 r38l33.2 = false := by decide +kernel
def r38l34 : S := (1, [wireWord5, wireWord3, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l34Dead : optimized 5 r38l34.1 r38l34.2 = false := by decide +kernel
def r38l35 : S := (0, [wireWord5, wireWord2, wireWord3, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l35Dead : optimized 5 r38l35.1 r38l35.2 = false := by decide +kernel
def r38l36 : S := (0, [wireWord44, wireWord2, wireWord3, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l36Dead : optimized 5 r38l36.1 r38l36.2 = false := by decide +kernel
def r38l37 : S := (1, [wireWord7, wireWord2, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l37Dead : optimized 5 r38l37.1 r38l37.2 = false := by decide +kernel
def r38l38 : S := (0, [wireWord7, wireWord2, wireWord3, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l38Dead : optimized 5 r38l38.1 r38l38.2 = false := by decide +kernel
def r38l39 : S := (1, [wireWord24, wireWord3, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l39Dead : optimized 5 r38l39.1 r38l39.2 = false := by decide +kernel
def r38l40 : S := (0, [wireWord24, wireWord2, wireWord3, wireWord6, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l40Dead : optimized 5 r38l40.1 r38l40.2 = false := by decide +kernel
def r38l41 : S := (0, [wireWord9, wireWord0, wireWord1, wireWord6, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l41Dead : optimized 5 r38l41.1 r38l41.2 = false := by decide +kernel
def r38l42 : S := (0, [wireWord41, wireWord0, wireWord1, wireWord6, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l42Dead : optimized 5 r38l42.1 r38l42.2 = false := by decide +kernel
def r38l43 : S := (0, [wireWord26, wireWord0, wireWord1, wireWord6, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l43Dead : optimized 5 r38l43.1 r38l43.2 = false := by decide +kernel
def r38l44 : S := (0, [wireWord42, wireWord0, wireWord1, wireWord6, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r38l44Dead : optimized 5 r38l44.1 r38l44.2 = false := by decide +kernel
def r38l45 : S := (0, [wireWord32, wireWord0, wireWord3, wireWord6, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l45Dead : optimized 5 r38l45.1 r38l45.2 = false := by decide +kernel
def r38l46 : S := (0, [wireWord23, wireWord0, wireWord3, wireWord6, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l46Dead : optimized 5 r38l46.1 r38l46.2 = false := by decide +kernel
def r38l47 : S := (0, [wireWord33, wireWord0, wireWord3, wireWord6, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l47Dead : optimized 5 r38l47.1 r38l47.2 = false := by decide +kernel
def r38l48 : S := (0, [wireWord34, wireWord0, wireWord3, wireWord6, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r38l48Dead : optimized 5 r38l48.1 r38l48.2 = false := by decide +kernel
def r38l49 : S := (0, [wireWord19, wireWord1, wireWord3, wireWord6, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r38l49Dead : optimized 5 r38l49.1 r38l49.2 = false := by decide +kernel
def r38l50 : S := (0, [wireWord35, wireWord1, wireWord3, wireWord6, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r38l50Dead : optimized 5 r38l50.1 r38l50.2 = false := by decide +kernel
def r38l51 : S := (0, [wireWord27, wireWord1, wireWord3, wireWord6, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r38l51Dead : optimized 5 r38l51.1 r38l51.2 = false := by decide +kernel
def r38l52 : S := (0, [wireWord20, wireWord1, wireWord3, wireWord6, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r38l52Dead : optimized 5 r38l52.1 r38l52.2 = false := by decide +kernel
theorem rootCell38Dead : optimized 6 rootCell38.1 rootCell38.2 = false := by
  have kids : nexts (rootCell38.1, rootCell38.2) = [r38l0,r38l1,r38l2,r38l3,r38l4,r38l5,r38l6,r38l7,r38l8,r38l9,r38l10,r38l11,r38l12,r38l13,r38l14,r38l15,r38l16,r38l17,r38l18,r38l19,r38l20,r38l21,r38l22,r38l23,r38l24,r38l25,r38l26,r38l27,r38l28,r38l29,r38l30,r38l31,r38l32,r38l33,r38l34,r38l35,r38l36,r38l37,r38l38,r38l39,r38l40,r38l41,r38l42,r38l43,r38l44,r38l45,r38l46,r38l47,r38l48,r38l49,r38l50,r38l51,r38l52] := by decide +kernel
  have stop : (rootCell38.2 == [goal] || rootCell38.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r38l0Dead, r38l1Dead, r38l2Dead, r38l3Dead, r38l4Dead, r38l5Dead, r38l6Dead, r38l7Dead, r38l8Dead, r38l9Dead, r38l10Dead, r38l11Dead, r38l12Dead, r38l13Dead, r38l14Dead, r38l15Dead, r38l16Dead, r38l17Dead, r38l18Dead, r38l19Dead, r38l20Dead, r38l21Dead, r38l22Dead, r38l23Dead, r38l24Dead, r38l25Dead, r38l26Dead, r38l27Dead, r38l28Dead, r38l29Dead, r38l30Dead, r38l31Dead, r38l32Dead, r38l33Dead, r38l34Dead, r38l35Dead, r38l36Dead, r38l37Dead, r38l38Dead, r38l39Dead, r38l40Dead, r38l41Dead, r38l42Dead, r38l43Dead, r38l44Dead, r38l45Dead, r38l46Dead, r38l47Dead, r38l48Dead, r38l49Dead, r38l50Dead, r38l51Dead, r38l52Dead]
def rootCell39 : S := (1, [wireWord6, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
def r39l0 : S := (1, [wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l0Dead : optimized 5 r39l0.1 r39l0.2 = false := by decide +kernel
def r39l1 : S := (0, [wireWord6, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l1Dead : optimized 5 r39l1.1 r39l1.2 = false := by decide +kernel
def r39l2 : S := (0, [wireWord6, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l2Dead : optimized 5 r39l2.1 r39l2.2 = false := by decide +kernel
def r39l3 : S := (1, [wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l3Dead : optimized 5 r39l3.1 r39l3.2 = false := by decide +kernel
def r39l4 : S := (0, [wireWord4, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l4Dead : optimized 5 r39l4.1 r39l4.2 = false := by decide +kernel
def r39l5 : S := (0, [wireWord4, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l5Dead : optimized 5 r39l5.1 r39l5.2 = false := by decide +kernel
def r39l6 : S := (0, [0, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l6Dead : optimized 5 r39l6.1 r39l6.2 = false := by decide +kernel
def r39l7 : S := (0, [0, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l7Dead : optimized 5 r39l7.1 r39l7.2 = false := by decide +kernel
def r39l8 : S := (0, [wireWord25, wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l8Dead : optimized 5 r39l8.1 r39l8.2 = false := by decide +kernel
def r39l9 : S := (0, [wireWord25, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l9Dead : optimized 5 r39l9.1 r39l9.2 = false := by decide +kernel
def r39l10 : S := (0, [wireWord6, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l10Dead : optimized 5 r39l10.1 r39l10.2 = false := by decide +kernel
def r39l11 : S := (1, [wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l11Dead : optimized 5 r39l11.1 r39l11.2 = false := by decide +kernel
def r39l12 : S := (0, [wireWord2, wireWord6, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l12Dead : optimized 5 r39l12.1 r39l12.2 = false := by decide +kernel
def r39l13 : S := (0, [wireWord2, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l13Dead : optimized 5 r39l13.1 r39l13.2 = false := by decide +kernel
def r39l14 : S := (0, [0, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l14Dead : optimized 5 r39l14.1 r39l14.2 = false := by decide +kernel
def r39l15 : S := (0, [wireWord8, wireWord6, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l15Dead : optimized 5 r39l15.1 r39l15.2 = false := by decide +kernel
def r39l16 : S := (0, [wireWord8, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l16Dead : optimized 5 r39l16.1 r39l16.2 = false := by decide +kernel
def r39l17 : S := (0, [wireWord53, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l17Dead : optimized 5 r39l17.1 r39l17.2 = false := by decide +kernel
def r39l18 : S := (0, [4611686017873245037, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l18Dead : optimized 5 r39l18.1 r39l18.2 = false := by decide +kernel
def r39l19 : S := (0, [wireWord56, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l19Dead : optimized 5 r39l19.1 r39l19.2 = false := by decide +kernel
def r39l20 : S := (0, [1477702806449189741, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l20Dead : optimized 5 r39l20.1 r39l20.2 = false := by decide +kernel
def r39l21 : S := (0, [wireWord61, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l21Dead : optimized 5 r39l21.1 r39l21.2 = false := by decide +kernel
def r39l22 : S := (0, [3458606166714518674, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l22Dead : optimized 5 r39l22.1 r39l22.2 = false := by decide +kernel
def r39l23 : S := (0, [wireWord64, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l23Dead : optimized 5 r39l23.1 r39l23.2 = false := by decide +kernel
def r39l24 : S := (0, [324622955290463378, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l24Dead : optimized 5 r39l24.1 r39l24.2 = false := by decide +kernel
def r39l25 : S := (0, [wireWord45, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l25Dead : optimized 5 r39l25.1 r39l25.2 = false := by decide +kernel
def r39l26 : S := (0, [4287347330127957788, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l26Dead : optimized 5 r39l26.1 r39l26.2 = false := by decide +kernel
def r39l27 : S := (0, [wireWord48, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l27Dead : optimized 5 r39l27.1 r39l27.2 = false := by decide +kernel
def r39l28 : S := (0, [1153364118703902492, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l28Dead : optimized 5 r39l28.1 r39l28.2 = false := by decide +kernel
def r39l29 : S := (0, [wireWord6, wireWord2, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l29Dead : optimized 5 r39l29.1 r39l29.2 = false := by decide +kernel
def r39l30 : S := (1, [wireWord43, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l30Dead : optimized 5 r39l30.1 r39l30.2 = false := by decide +kernel
def r39l31 : S := (0, [wireWord43, wireWord4, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l31Dead : optimized 5 r39l31.1 r39l31.2 = false := by decide +kernel
def r39l32 : S := (0, [wireWord43, wireWord2, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l32Dead : optimized 5 r39l32.1 r39l32.2 = false := by decide +kernel
def r39l33 : S := (0, [wireWord25, wireWord2, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l33Dead : optimized 5 r39l33.1 r39l33.2 = false := by decide +kernel
def r39l34 : S := (1, [wireWord8, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l34Dead : optimized 5 r39l34.1 r39l34.2 = false := by decide +kernel
def r39l35 : S := (0, [wireWord8, wireWord4, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l35Dead : optimized 5 r39l35.1 r39l35.2 = false := by decide +kernel
def r39l36 : S := (0, [wireWord8, wireWord2, wireWord6, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l36Dead : optimized 5 r39l36.1 r39l36.2 = false := by decide +kernel
def r39l37 : S := (0, [wireWord28, wireWord0, wireWord6, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l37Dead : optimized 5 r39l37.1 r39l37.2 = false := by decide +kernel
def r39l38 : S := (0, [wireWord18, wireWord0, wireWord6, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l38Dead : optimized 5 r39l38.1 r39l38.2 = false := by decide +kernel
def r39l39 : S := (0, [wireWord37, wireWord0, wireWord6, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l39Dead : optimized 5 r39l39.1 r39l39.2 = false := by decide +kernel
def r39l40 : S := (0, [wireWord36, wireWord0, wireWord6, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l40Dead : optimized 5 r39l40.1 r39l40.2 = false := by decide +kernel
def r39l41 : S := (0, [wireWord21, wireWord1, wireWord6, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l41Dead : optimized 5 r39l41.1 r39l41.2 = false := by decide +kernel
def r39l42 : S := (0, [wireWord38, wireWord1, wireWord6, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l42Dead : optimized 5 r39l42.1 r39l42.2 = false := by decide +kernel
def r39l43 : S := (0, [wireWord22, wireWord1, wireWord6, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l43Dead : optimized 5 r39l43.1 r39l43.2 = false := by decide +kernel
def r39l44 : S := (0, [wireWord29, wireWord1, wireWord6, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l44Dead : optimized 5 r39l44.1 r39l44.2 = false := by decide +kernel
def r39l45 : S := (0, [wireWord15, wireWord3, wireWord6, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l45Dead : optimized 5 r39l45.1 r39l45.2 = false := by decide +kernel
def r39l46 : S := (0, [wireWord14, wireWord3, wireWord6, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l46Dead : optimized 5 r39l46.1 r39l46.2 = false := by decide +kernel
def r39l47 : S := (0, [wireWord16, wireWord3, wireWord6, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l47Dead : optimized 5 r39l47.1 r39l47.2 = false := by decide +kernel
def r39l48 : S := (0, [wireWord17, wireWord3, wireWord6, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l48Dead : optimized 5 r39l48.1 r39l48.2 = false := by decide +kernel
def r39l49 : S := (0, [wireWord10, wireWord0, wireWord6, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l49Dead : optimized 5 r39l49.1 r39l49.2 = false := by decide +kernel
def r39l50 : S := (0, [wireWord12, wireWord0, wireWord6, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l50Dead : optimized 5 r39l50.1 r39l50.2 = false := by decide +kernel
def r39l51 : S := (0, [wireWord13, wireWord1, wireWord6, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l51Dead : optimized 5 r39l51.1 r39l51.2 = false := by decide +kernel
def r39l52 : S := (0, [wireWord11, wireWord1, wireWord6, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r39l52Dead : optimized 5 r39l52.1 r39l52.2 = false := by decide +kernel
def r39l53 : S := (1, [wireWord5, wireWord6, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l53Dead : optimized 5 r39l53.1 r39l53.2 = false := by decide +kernel
def r39l54 : S := (0, [wireWord5, wireWord2, wireWord6, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l54Dead : optimized 5 r39l54.1 r39l54.2 = false := by decide +kernel
def r39l55 : S := (0, [wireWord5, wireWord3, wireWord6, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l55Dead : optimized 5 r39l55.1 r39l55.2 = false := by decide +kernel
def r39l56 : S := (0, [wireWord7, wireWord2, wireWord6, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l56Dead : optimized 5 r39l56.1 r39l56.2 = false := by decide +kernel
def r39l57 : S := (0, [wireWord24, wireWord3, wireWord6, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r39l57Dead : optimized 5 r39l57.1 r39l57.2 = false := by decide +kernel
theorem rootCell39Dead : optimized 6 rootCell39.1 rootCell39.2 = false := by
  have kids : nexts (rootCell39.1, rootCell39.2) = [r39l0,r39l1,r39l2,r39l3,r39l4,r39l5,r39l6,r39l7,r39l8,r39l9,r39l10,r39l11,r39l12,r39l13,r39l14,r39l15,r39l16,r39l17,r39l18,r39l19,r39l20,r39l21,r39l22,r39l23,r39l24,r39l25,r39l26,r39l27,r39l28,r39l29,r39l30,r39l31,r39l32,r39l33,r39l34,r39l35,r39l36,r39l37,r39l38,r39l39,r39l40,r39l41,r39l42,r39l43,r39l44,r39l45,r39l46,r39l47,r39l48,r39l49,r39l50,r39l51,r39l52,r39l53,r39l54,r39l55,r39l56,r39l57] := by decide +kernel
  have stop : (rootCell39.2 == [goal] || rootCell39.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r39l0Dead, r39l1Dead, r39l2Dead, r39l3Dead, r39l4Dead, r39l5Dead, r39l6Dead, r39l7Dead, r39l8Dead, r39l9Dead, r39l10Dead, r39l11Dead, r39l12Dead, r39l13Dead, r39l14Dead, r39l15Dead, r39l16Dead, r39l17Dead, r39l18Dead, r39l19Dead, r39l20Dead, r39l21Dead, r39l22Dead, r39l23Dead, r39l24Dead, r39l25Dead, r39l26Dead, r39l27Dead, r39l28Dead, r39l29Dead, r39l30Dead, r39l31Dead, r39l32Dead, r39l33Dead, r39l34Dead, r39l35Dead, r39l36Dead, r39l37Dead, r39l38Dead, r39l39Dead, r39l40Dead, r39l41Dead, r39l42Dead, r39l43Dead, r39l44Dead, r39l45Dead, r39l46Dead, r39l47Dead, r39l48Dead, r39l49Dead, r39l50Dead, r39l51Dead, r39l52Dead, r39l53Dead, r39l54Dead, r39l55Dead, r39l56Dead, r39l57Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def rootCell40 : S := (1, [wireWord43, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
def r40l0 : S := (1, [wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l0Dead : optimized 5 r40l0.1 r40l0.2 = false := by decide +kernel
def r40l1 : S := (0, [wireWord4, wireWord43, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l1Dead : optimized 5 r40l1.1 r40l1.2 = false := by decide +kernel
def r40l2 : S := (0, [wireWord4, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l2Dead : optimized 5 r40l2.1 r40l2.2 = false := by decide +kernel
def r40l3 : S := (0, [wireWord43, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l3Dead : optimized 5 r40l3.1 r40l3.2 = false := by decide +kernel
def r40l4 : S := (1, [wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l4Dead : optimized 5 r40l4.1 r40l4.2 = false := by decide +kernel
def r40l5 : S := (0, [wireWord8, wireWord43, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l5Dead : optimized 5 r40l5.1 r40l5.2 = false := by decide +kernel
def r40l6 : S := (0, [wireWord8, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l6Dead : optimized 5 r40l6.1 r40l6.2 = false := by decide +kernel
def r40l7 : S := (0, [0, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l7Dead : optimized 5 r40l7.1 r40l7.2 = false := by decide +kernel
def r40l8 : S := (1, [wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l8Dead : optimized 5 r40l8.1 r40l8.2 = false := by decide +kernel
def r40l9 : S := (0, [wireWord2, wireWord43, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l9Dead : optimized 5 r40l9.1 r40l9.2 = false := by decide +kernel
def r40l10 : S := (0, [wireWord2, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l10Dead : optimized 5 r40l10.1 r40l10.2 = false := by decide +kernel
def r40l11 : S := (0, [wireWord43, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l11Dead : optimized 5 r40l11.1 r40l11.2 = false := by decide +kernel
def r40l12 : S := (0, [wireWord25, wireWord43, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l12Dead : optimized 5 r40l12.1 r40l12.2 = false := by decide +kernel
def r40l13 : S := (0, [wireWord25, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l13Dead : optimized 5 r40l13.1 r40l13.2 = false := by decide +kernel
def r40l14 : S := (0, [0, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l14Dead : optimized 5 r40l14.1 r40l14.2 = false := by decide +kernel
def r40l15 : S := (0, [3687880695511806816, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l15Dead : optimized 5 r40l15.1 r40l15.2 = false := by decide +kernel
def r40l16 : S := (0, [4611686018410610669, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l16Dead : optimized 5 r40l16.1 r40l16.2 = false := by decide +kernel
def r40l17 : S := (0, [599546100336004224, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l17Dead : optimized 5 r40l17.1 r40l17.2 = false := by decide +kernel
def r40l18 : S := (0, [324259222562799629, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l18Dead : optimized 5 r40l18.1 r40l18.2 = false := by decide +kernel
def r40l19 : S := (0, [746276819060558976, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l19Dead : optimized 5 r40l19.1 r40l19.2 = false := by decide +kernel
def r40l20 : S := (0, [4611686018410610674, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l20Dead : optimized 5 r40l20.1 r40l20.2 = false := by decide +kernel
def r40l21 : S := (0, [3541149976787252064, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l21Dead : optimized 5 r40l21.1 r40l21.2 = false := by decide +kernel
def r40l22 : S := (0, [324259222562799634, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l22Dead : optimized 5 r40l22.1 r40l22.2 = false := by decide +kernel
def r40l23 : S := (1, [1833976068085059328, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l23Dead : optimized 5 r40l23.1 r40l23.2 = false := by decide +kernel
def r40l24 : S := (0, [1833976068085059328, wireWord43, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l24Dead : optimized 5 r40l24.1 r40l24.2 = false := by decide +kernel
def r40l25 : S := (0, [1833976068085059328, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l25Dead : optimized 5 r40l25.1 r40l25.2 = false := by decide +kernel
def r40l26 : S := (0, [4287426838797484028, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l26Dead : optimized 5 r40l26.1 r40l26.2 = false := by decide +kernel
def r40l27 : S := (1, [2453450727762751712, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l27Dead : optimized 5 r40l27.1 r40l27.2 = false := by decide +kernel
def r40l28 : S := (0, [2453450727762751712, wireWord43, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l28Dead : optimized 5 r40l28.1 r40l28.2 = false := by decide +kernel
def r40l29 : S := (0, [2453450727762751712, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l29Dead : optimized 5 r40l29.1 r40l29.2 = false := by decide +kernel
def r40l30 : S := (0, [42949672988, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l30Dead : optimized 5 r40l30.1 r40l30.2 = false := by decide +kernel
def r40l31 : S := (1, [wireWord6, wireWord43, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l31Dead : optimized 5 r40l31.1 r40l31.2 = false := by decide +kernel
def r40l32 : S := (0, [wireWord6, wireWord4, wireWord43, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l32Dead : optimized 5 r40l32.1 r40l32.2 = false := by decide +kernel
def r40l33 : S := (0, [wireWord6, wireWord2, wireWord43, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l33Dead : optimized 5 r40l33.1 r40l33.2 = false := by decide +kernel
def r40l34 : S := (0, [wireWord25, wireWord4, wireWord43, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l34Dead : optimized 5 r40l34.1 r40l34.2 = false := by decide +kernel
def r40l35 : S := (0, [wireWord8, wireWord2, wireWord43, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r40l35Dead : optimized 5 r40l35.1 r40l35.2 = false := by decide +kernel
def r40l36 : S := (0, [wireWord5, wireWord2, wireWord43, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l36Dead : optimized 5 r40l36.1 r40l36.2 = false := by decide +kernel
def r40l37 : S := (0, [wireWord7, wireWord2, wireWord43, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r40l37Dead : optimized 5 r40l37.1 r40l37.2 = false := by decide +kernel
theorem rootCell40Dead : optimized 6 rootCell40.1 rootCell40.2 = false := by
  have kids : nexts (rootCell40.1, rootCell40.2) = [r40l0,r40l1,r40l2,r40l3,r40l4,r40l5,r40l6,r40l7,r40l8,r40l9,r40l10,r40l11,r40l12,r40l13,r40l14,r40l15,r40l16,r40l17,r40l18,r40l19,r40l20,r40l21,r40l22,r40l23,r40l24,r40l25,r40l26,r40l27,r40l28,r40l29,r40l30,r40l31,r40l32,r40l33,r40l34,r40l35,r40l36,r40l37] := by decide +kernel
  have stop : (rootCell40.2 == [goal] || rootCell40.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r40l0Dead, r40l1Dead, r40l2Dead, r40l3Dead, r40l4Dead, r40l5Dead, r40l6Dead, r40l7Dead, r40l8Dead, r40l9Dead, r40l10Dead, r40l11Dead, r40l12Dead, r40l13Dead, r40l14Dead, r40l15Dead, r40l16Dead, r40l17Dead, r40l18Dead, r40l19Dead, r40l20Dead, r40l21Dead, r40l22Dead, r40l23Dead, r40l24Dead, r40l25Dead, r40l26Dead, r40l27Dead, r40l28Dead, r40l29Dead, r40l30Dead, r40l31Dead, r40l32Dead, r40l33Dead, r40l34Dead, r40l35Dead, r40l36Dead, r40l37Dead]
def rootCell41 : S := (1, [wireWord25, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
def r41l0 : S := (0, [wireWord25, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l0Dead : optimized 5 r41l0.1 r41l0.2 = false := by decide +kernel
def r41l1 : S := (1, [wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l1Dead : optimized 5 r41l1.1 r41l1.2 = false := by decide +kernel
def r41l2 : S := (0, [wireWord4, wireWord25, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l2Dead : optimized 5 r41l2.1 r41l2.2 = false := by decide +kernel
def r41l3 : S := (0, [wireWord4, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l3Dead : optimized 5 r41l3.1 r41l3.2 = false := by decide +kernel
def r41l4 : S := (0, [0, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l4Dead : optimized 5 r41l4.1 r41l4.2 = false := by decide +kernel
def r41l5 : S := (1, [wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l5Dead : optimized 5 r41l5.1 r41l5.2 = false := by decide +kernel
def r41l6 : S := (0, [wireWord6, wireWord25, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l6Dead : optimized 5 r41l6.1 r41l6.2 = false := by decide +kernel
def r41l7 : S := (0, [wireWord6, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l7Dead : optimized 5 r41l7.1 r41l7.2 = false := by decide +kernel
def r41l8 : S := (0, [0, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l8Dead : optimized 5 r41l8.1 r41l8.2 = false := by decide +kernel
def r41l9 : S := (0, [wireWord43, wireWord25, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l9Dead : optimized 5 r41l9.1 r41l9.2 = false := by decide +kernel
def r41l10 : S := (0, [wireWord43, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l10Dead : optimized 5 r41l10.1 r41l10.2 = false := by decide +kernel
def r41l11 : S := (0, [wireWord25, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l11Dead : optimized 5 r41l11.1 r41l11.2 = false := by decide +kernel
def r41l12 : S := (1, [wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l12Dead : optimized 5 r41l12.1 r41l12.2 = false := by decide +kernel
def r41l13 : S := (0, [wireWord2, wireWord25, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l13Dead : optimized 5 r41l13.1 r41l13.2 = false := by decide +kernel
def r41l14 : S := (0, [wireWord2, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l14Dead : optimized 5 r41l14.1 r41l14.2 = false := by decide +kernel
def r41l15 : S := (0, [3092376453984, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l15Dead : optimized 5 r41l15.1 r41l15.2 = false := by decide +kernel
def r41l16 : S := (0, [4012139918074609645, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l16Dead : optimized 5 r41l16.1 r41l16.2 = false := by decide +kernel
def r41l17 : S := (0, [3200, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l17Dead : optimized 5 r41l17.1 r41l17.2 = false := by decide +kernel
def r41l18 : S := (0, [4012136825698152461, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l18Dead : optimized 5 r41l18.1 r41l18.2 = false := by decide +kernel
def r41l19 : S := (0, [3092376456320, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l19Dead : optimized 5 r41l19.1 r41l19.2 = false := by decide +kernel
def r41l20 : S := (0, [1070536041623359474, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l20Dead : optimized 5 r41l20.1 r41l20.2 = false := by decide +kernel
def r41l21 : S := (0, [864, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l21Dead : optimized 5 r41l21.1 r41l21.2 = false := by decide +kernel
def r41l22 : S := (0, [1070532949246902290, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l22Dead : optimized 5 r41l22.1 r41l22.2 = false := by decide +kernel
def r41l23 : S := (0, [2748779073280, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l23Dead : optimized 5 r41l23.1 r41l23.2 = false := by decide +kernel
def r41l24 : S := (1, [1833976454632116220, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l24Dead : optimized 5 r41l24.1 r41l24.2 = false := by decide +kernel
def r41l25 : S := (0, [1833976454632116220, wireWord25, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l25Dead : optimized 5 r41l25.1 r41l25.2 = false := by decide +kernel
def r41l26 : S := (0, [1833976454632116220, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l26Dead : optimized 5 r41l26.1 r41l26.2 = false := by decide +kernel
def r41l27 : S := (0, [343597383904, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l27Dead : optimized 5 r41l27.1 r41l27.2 = false := by decide +kernel
def r41l28 : S := (1, [1833973362255659036, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l28Dead : optimized 5 r41l28.1 r41l28.2 = false := by decide +kernel
def r41l29 : S := (0, [1833973362255659036, wireWord25, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l29Dead : optimized 5 r41l29.1 r41l29.2 = false := by decide +kernel
def r41l30 : S := (0, [1833973362255659036, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l30Dead : optimized 5 r41l30.1 r41l30.2 = false := by decide +kernel
def r41l31 : S := (0, [wireWord6, wireWord2, wireWord25, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l31Dead : optimized 5 r41l31.1 r41l31.2 = false := by decide +kernel
def r41l32 : S := (0, [wireWord43, wireWord4, wireWord25, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l32Dead : optimized 5 r41l32.1 r41l32.2 = false := by decide +kernel
def r41l33 : S := (1, [wireWord8, wireWord25, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l33Dead : optimized 5 r41l33.1 r41l33.2 = false := by decide +kernel
def r41l34 : S := (0, [wireWord8, wireWord4, wireWord25, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l34Dead : optimized 5 r41l34.1 r41l34.2 = false := by decide +kernel
def r41l35 : S := (0, [wireWord8, wireWord2, wireWord25, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l35Dead : optimized 5 r41l35.1 r41l35.2 = false := by decide +kernel
def r41l36 : S := (0, [wireWord10, wireWord0, wireWord25, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l36Dead : optimized 5 r41l36.1 r41l36.2 = false := by decide +kernel
def r41l37 : S := (0, [wireWord12, wireWord0, wireWord25, wireWord4, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l37Dead : optimized 5 r41l37.1 r41l37.2 = false := by decide +kernel
def r41l38 : S := (0, [wireWord13, wireWord1, wireWord25, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l38Dead : optimized 5 r41l38.1 r41l38.2 = false := by decide +kernel
def r41l39 : S := (0, [wireWord11, wireWord1, wireWord25, wireWord4, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r41l39Dead : optimized 5 r41l39.1 r41l39.2 = false := by decide +kernel
def r41l40 : S := (1, [wireWord5, wireWord25, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l40Dead : optimized 5 r41l40.1 r41l40.2 = false := by decide +kernel
def r41l41 : S := (0, [wireWord5, wireWord2, wireWord25, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l41Dead : optimized 5 r41l41.1 r41l41.2 = false := by decide +kernel
def r41l42 : S := (0, [wireWord5, wireWord3, wireWord25, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l42Dead : optimized 5 r41l42.1 r41l42.2 = false := by decide +kernel
def r41l43 : S := (0, [wireWord7, wireWord2, wireWord25, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l43Dead : optimized 5 r41l43.1 r41l43.2 = false := by decide +kernel
def r41l44 : S := (0, [wireWord24, wireWord3, wireWord25, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r41l44Dead : optimized 5 r41l44.1 r41l44.2 = false := by decide +kernel
theorem rootCell41Dead : optimized 6 rootCell41.1 rootCell41.2 = false := by
  have kids : nexts (rootCell41.1, rootCell41.2) = [r41l0,r41l1,r41l2,r41l3,r41l4,r41l5,r41l6,r41l7,r41l8,r41l9,r41l10,r41l11,r41l12,r41l13,r41l14,r41l15,r41l16,r41l17,r41l18,r41l19,r41l20,r41l21,r41l22,r41l23,r41l24,r41l25,r41l26,r41l27,r41l28,r41l29,r41l30,r41l31,r41l32,r41l33,r41l34,r41l35,r41l36,r41l37,r41l38,r41l39,r41l40,r41l41,r41l42,r41l43,r41l44] := by decide +kernel
  have stop : (rootCell41.2 == [goal] || rootCell41.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r41l0Dead, r41l1Dead, r41l2Dead, r41l3Dead, r41l4Dead, r41l5Dead, r41l6Dead, r41l7Dead, r41l8Dead, r41l9Dead, r41l10Dead, r41l11Dead, r41l12Dead, r41l13Dead, r41l14Dead, r41l15Dead, r41l16Dead, r41l17Dead, r41l18Dead, r41l19Dead, r41l20Dead, r41l21Dead, r41l22Dead, r41l23Dead, r41l24Dead, r41l25Dead, r41l26Dead, r41l27Dead, r41l28Dead, r41l29Dead, r41l30Dead, r41l31Dead, r41l32Dead, r41l33Dead, r41l34Dead, r41l35Dead, r41l36Dead, r41l37Dead, r41l38Dead, r41l39Dead, r41l40Dead, r41l41Dead, r41l42Dead, r41l43Dead, r41l44Dead]
def rootCell42 : S := (2, [wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
def r42l0 : S := (1, [wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l0Dead : optimized 5 r42l0.1 r42l0.2 = false := by decide +kernel
def r42l1 : S := (0, [wireWord8, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l1Dead : optimized 5 r42l1.1 r42l1.2 = false := by decide +kernel
def r42l2 : S := (1, [wireWord2, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l2Dead : optimized 5 r42l2.1 r42l2.2 = false := by decide +kernel
def r42l3 : S := (0, [wireWord2, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l3Dead : optimized 5 r42l3.1 r42l3.2 = false := by decide +kernel
def r42l4 : S := (0, [0, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l4Dead : optimized 5 r42l4.1 r42l4.2 = false := by decide +kernel
def r42l5 : S := (1, [wireWord6, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l5Dead : optimized 5 r42l5.1 r42l5.2 = false := by decide +kernel
def r42l6 : S := (1, [wireWord6, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l6Dead : optimized 5 r42l6.1 r42l6.2 = false := by decide +kernel
def r42l7 : S := (0, [wireWord6, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l7Dead : optimized 5 r42l7.1 r42l7.2 = false := by decide +kernel
def r42l8 : S := (0, [wireWord55, wireWord8, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l8Dead : optimized 5 r42l8.1 r42l8.2 = false := by decide +kernel
def r42l9 : S := (0, [4012139918611968877, wireWord8, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l9Dead : optimized 5 r42l9.1 r42l9.2 = false := by decide +kernel
def r42l10 : S := (0, [wireWord54, wireWord8, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l10Dead : optimized 5 r42l10.1 r42l10.2 = false := by decide +kernel
def r42l11 : S := (0, [2858699426564670317, wireWord8, wireWord0, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l11Dead : optimized 5 r42l11.1 r42l11.2 = false := by decide +kernel
def r42l12 : S := (0, [wireWord63, wireWord8, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l12Dead : optimized 5 r42l12.1 r42l12.2 = false := by decide +kernel
def r42l13 : S := (0, [2223615893319449746, wireWord8, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l13Dead : optimized 5 r42l13.1 r42l13.2 = false := by decide +kernel
def r42l14 : S := (0, [wireWord62, wireWord8, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l14Dead : optimized 5 r42l14.1 r42l14.2 = false := by decide +kernel
def r42l15 : S := (0, [1070175401272151186, wireWord8, wireWord1, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l15Dead : optimized 5 r42l15.1 r42l15.2 = false := by decide +kernel
def r42l16 : S := (0, [wireWord47, wireWord8, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l16Dead : optimized 5 r42l16.1 r42l16.2 = false := by decide +kernel
def r42l17 : S := (0, [1834055276106874652, wireWord8, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l17Dead : optimized 5 r42l17.1 r42l17.2 = false := by decide +kernel
def r42l18 : S := (0, [wireWord46, wireWord8, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l18Dead : optimized 5 r42l18.1 r42l18.2 = false := by decide +kernel
def r42l19 : S := (0, [680614784059576092, wireWord8, wireWord3, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l19Dead : optimized 5 r42l19.1 r42l19.2 = false := by decide +kernel
def r42l20 : S := (0, [wireWord10, wireWord2, wireWord0, wireWord8, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l20Dead : optimized 5 r42l20.1 r42l20.2 = false := by decide +kernel
def r42l21 : S := (0, [wireWord30, wireWord2, wireWord0, wireWord8, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l21Dead : optimized 5 r42l21.1 r42l21.2 = false := by decide +kernel
def r42l22 : S := (0, [wireWord31, wireWord2, wireWord0, wireWord8, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l22Dead : optimized 5 r42l22.1 r42l22.2 = false := by decide +kernel
def r42l23 : S := (0, [wireWord12, wireWord2, wireWord0, wireWord8, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l23Dead : optimized 5 r42l23.1 r42l23.2 = false := by decide +kernel
def r42l24 : S := (0, [wireWord40, wireWord2, wireWord1, wireWord8, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l24Dead : optimized 5 r42l24.1 r42l24.2 = false := by decide +kernel
def r42l25 : S := (0, [wireWord13, wireWord2, wireWord1, wireWord8, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l25Dead : optimized 5 r42l25.1 r42l25.2 = false := by decide +kernel
def r42l26 : S := (0, [wireWord11, wireWord2, wireWord1, wireWord8, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l26Dead : optimized 5 r42l26.1 r42l26.2 = false := by decide +kernel
def r42l27 : S := (0, [wireWord39, wireWord2, wireWord1, wireWord8, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l27Dead : optimized 5 r42l27.1 r42l27.2 = false := by decide +kernel
def r42l28 : S := (1, [wireWord5, wireWord2, wireWord8, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l28Dead : optimized 5 r42l28.1 r42l28.2 = false := by decide +kernel
def r42l29 : S := (0, [wireWord5, wireWord2, wireWord3, wireWord8, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l29Dead : optimized 5 r42l29.1 r42l29.2 = false := by decide +kernel
def r42l30 : S := (0, [wireWord44, wireWord2, wireWord3, wireWord8, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l30Dead : optimized 5 r42l30.1 r42l30.2 = false := by decide +kernel
def r42l31 : S := (1, [wireWord7, wireWord2, wireWord8, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l31Dead : optimized 5 r42l31.1 r42l31.2 = false := by decide +kernel
def r42l32 : S := (0, [wireWord7, wireWord2, wireWord3, wireWord8, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l32Dead : optimized 5 r42l32.1 r42l32.2 = false := by decide +kernel
def r42l33 : S := (0, [wireWord24, wireWord2, wireWord3, wireWord8, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l33Dead : optimized 5 r42l33.1 r42l33.2 = false := by decide +kernel
def r42l34 : S := (0, [wireWord9, wireWord0, wireWord1, wireWord8, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l34Dead : optimized 5 r42l34.1 r42l34.2 = false := by decide +kernel
def r42l35 : S := (0, [wireWord41, wireWord0, wireWord1, wireWord8, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l35Dead : optimized 5 r42l35.1 r42l35.2 = false := by decide +kernel
def r42l36 : S := (0, [wireWord26, wireWord0, wireWord1, wireWord8, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l36Dead : optimized 5 r42l36.1 r42l36.2 = false := by decide +kernel
def r42l37 : S := (0, [wireWord42, wireWord0, wireWord1, wireWord8, wireWord2, wireWord3])
set_option maxHeartbeats 0 in
theorem r42l37Dead : optimized 5 r42l37.1 r42l37.2 = false := by decide +kernel
def r42l38 : S := (0, [wireWord32, wireWord0, wireWord3, wireWord8, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l38Dead : optimized 5 r42l38.1 r42l38.2 = false := by decide +kernel
def r42l39 : S := (0, [wireWord23, wireWord0, wireWord3, wireWord8, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l39Dead : optimized 5 r42l39.1 r42l39.2 = false := by decide +kernel
def r42l40 : S := (0, [wireWord33, wireWord0, wireWord3, wireWord8, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l40Dead : optimized 5 r42l40.1 r42l40.2 = false := by decide +kernel
def r42l41 : S := (0, [wireWord34, wireWord0, wireWord3, wireWord8, wireWord2, wireWord1])
set_option maxHeartbeats 0 in
theorem r42l41Dead : optimized 5 r42l41.1 r42l41.2 = false := by decide +kernel
def r42l42 : S := (0, [wireWord19, wireWord1, wireWord3, wireWord8, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r42l42Dead : optimized 5 r42l42.1 r42l42.2 = false := by decide +kernel
def r42l43 : S := (0, [wireWord35, wireWord1, wireWord3, wireWord8, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r42l43Dead : optimized 5 r42l43.1 r42l43.2 = false := by decide +kernel
def r42l44 : S := (0, [wireWord27, wireWord1, wireWord3, wireWord8, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r42l44Dead : optimized 5 r42l44.1 r42l44.2 = false := by decide +kernel
def r42l45 : S := (0, [wireWord20, wireWord1, wireWord3, wireWord8, wireWord2, wireWord0])
set_option maxHeartbeats 0 in
theorem r42l45Dead : optimized 5 r42l45.1 r42l45.2 = false := by decide +kernel
theorem rootCell42Dead : optimized 6 rootCell42.1 rootCell42.2 = false := by
  have kids : nexts (rootCell42.1, rootCell42.2) = [r42l0,r42l1,r42l2,r42l3,r42l4,r42l5,r42l6,r42l7,r42l8,r42l9,r42l10,r42l11,r42l12,r42l13,r42l14,r42l15,r42l16,r42l17,r42l18,r42l19,r42l20,r42l21,r42l22,r42l23,r42l24,r42l25,r42l26,r42l27,r42l28,r42l29,r42l30,r42l31,r42l32,r42l33,r42l34,r42l35,r42l36,r42l37,r42l38,r42l39,r42l40,r42l41,r42l42,r42l43,r42l44,r42l45] := by decide +kernel
  have stop : (rootCell42.2 == [goal] || rootCell42.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r42l0Dead, r42l1Dead, r42l2Dead, r42l3Dead, r42l4Dead, r42l5Dead, r42l6Dead, r42l7Dead, r42l8Dead, r42l9Dead, r42l10Dead, r42l11Dead, r42l12Dead, r42l13Dead, r42l14Dead, r42l15Dead, r42l16Dead, r42l17Dead, r42l18Dead, r42l19Dead, r42l20Dead, r42l21Dead, r42l22Dead, r42l23Dead, r42l24Dead, r42l25Dead, r42l26Dead, r42l27Dead, r42l28Dead, r42l29Dead, r42l30Dead, r42l31Dead, r42l32Dead, r42l33Dead, r42l34Dead, r42l35Dead, r42l36Dead, r42l37Dead, r42l38Dead, r42l39Dead, r42l40Dead, r42l41Dead, r42l42Dead, r42l43Dead, r42l44Dead, r42l45Dead]
def rootCell43 : S := (1, [wireWord8, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
def r43l0 : S := (0, [0, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l0Dead : optimized 5 r43l0.1 r43l0.2 = false := by decide +kernel
def r43l1 : S := (0, [0, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l1Dead : optimized 5 r43l1.1 r43l1.2 = false := by decide +kernel
def r43l2 : S := (0, [wireWord43, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l2Dead : optimized 5 r43l2.1 r43l2.2 = false := by decide +kernel
def r43l3 : S := (0, [wireWord43, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l3Dead : optimized 5 r43l3.1 r43l3.2 = false := by decide +kernel
def r43l4 : S := (1, [wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l4Dead : optimized 5 r43l4.1 r43l4.2 = false := by decide +kernel
def r43l5 : S := (0, [wireWord8, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l5Dead : optimized 5 r43l5.1 r43l5.2 = false := by decide +kernel
def r43l6 : S := (0, [wireWord8, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l6Dead : optimized 5 r43l6.1 r43l6.2 = false := by decide +kernel
def r43l7 : S := (1, [wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l7Dead : optimized 5 r43l7.1 r43l7.2 = false := by decide +kernel
def r43l8 : S := (0, [wireWord4, wireWord8, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l8Dead : optimized 5 r43l8.1 r43l8.2 = false := by decide +kernel
def r43l9 : S := (0, [wireWord4, wireWord4, wireWord2, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l9Dead : optimized 5 r43l9.1 r43l9.2 = false := by decide +kernel
def r43l10 : S := (0, [wireWord8, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l10Dead : optimized 5 r43l10.1 r43l10.2 = false := by decide +kernel
def r43l11 : S := (1, [wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l11Dead : optimized 5 r43l11.1 r43l11.2 = false := by decide +kernel
def r43l12 : S := (0, [wireWord2, wireWord8, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l12Dead : optimized 5 r43l12.1 r43l12.2 = false := by decide +kernel
def r43l13 : S := (0, [wireWord2, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l13Dead : optimized 5 r43l13.1 r43l13.2 = false := by decide +kernel
def r43l14 : S := (0, [0, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l14Dead : optimized 5 r43l14.1 r43l14.2 = false := by decide +kernel
def r43l15 : S := (0, [wireWord6, wireWord8, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l15Dead : optimized 5 r43l15.1 r43l15.2 = false := by decide +kernel
def r43l16 : S := (0, [wireWord6, wireWord2, wireWord4, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l16Dead : optimized 5 r43l16.1 r43l16.2 = false := by decide +kernel
def r43l17 : S := (0, [wireWord55, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l17Dead : optimized 5 r43l17.1 r43l17.2 = false := by decide +kernel
def r43l18 : S := (0, [4012139918611968877, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l18Dead : optimized 5 r43l18.1 r43l18.2 = false := by decide +kernel
def r43l19 : S := (0, [wireWord54, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l19Dead : optimized 5 r43l19.1 r43l19.2 = false := by decide +kernel
def r43l20 : S := (0, [2858699426564670317, wireWord0, wireWord4, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l20Dead : optimized 5 r43l20.1 r43l20.2 = false := by decide +kernel
def r43l21 : S := (0, [wireWord63, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l21Dead : optimized 5 r43l21.1 r43l21.2 = false := by decide +kernel
def r43l22 : S := (0, [2223615893319449746, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l22Dead : optimized 5 r43l22.1 r43l22.2 = false := by decide +kernel
def r43l23 : S := (0, [wireWord62, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l23Dead : optimized 5 r43l23.1 r43l23.2 = false := by decide +kernel
def r43l24 : S := (0, [1070175401272151186, wireWord1, wireWord4, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l24Dead : optimized 5 r43l24.1 r43l24.2 = false := by decide +kernel
def r43l25 : S := (0, [wireWord47, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l25Dead : optimized 5 r43l25.1 r43l25.2 = false := by decide +kernel
def r43l26 : S := (0, [1834055276106874652, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l26Dead : optimized 5 r43l26.1 r43l26.2 = false := by decide +kernel
def r43l27 : S := (0, [wireWord46, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l27Dead : optimized 5 r43l27.1 r43l27.2 = false := by decide +kernel
def r43l28 : S := (0, [680614784059576092, wireWord3, wireWord4, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l28Dead : optimized 5 r43l28.1 r43l28.2 = false := by decide +kernel
def r43l29 : S := (1, [wireWord6, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l29Dead : optimized 5 r43l29.1 r43l29.2 = false := by decide +kernel
def r43l30 : S := (0, [wireWord6, wireWord4, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l30Dead : optimized 5 r43l30.1 r43l30.2 = false := by decide +kernel
def r43l31 : S := (0, [wireWord6, wireWord2, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l31Dead : optimized 5 r43l31.1 r43l31.2 = false := by decide +kernel
def r43l32 : S := (0, [wireWord43, wireWord2, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l32Dead : optimized 5 r43l32.1 r43l32.2 = false := by decide +kernel
def r43l33 : S := (1, [wireWord25, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l33Dead : optimized 5 r43l33.1 r43l33.2 = false := by decide +kernel
def r43l34 : S := (0, [wireWord25, wireWord4, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l34Dead : optimized 5 r43l34.1 r43l34.2 = false := by decide +kernel
def r43l35 : S := (0, [wireWord25, wireWord2, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l35Dead : optimized 5 r43l35.1 r43l35.2 = false := by decide +kernel
def r43l36 : S := (0, [wireWord8, wireWord2, wireWord8, wireWord0, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l36Dead : optimized 5 r43l36.1 r43l36.2 = false := by decide +kernel
def r43l37 : S := (0, [wireWord28, wireWord0, wireWord8, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l37Dead : optimized 5 r43l37.1 r43l37.2 = false := by decide +kernel
def r43l38 : S := (0, [wireWord18, wireWord0, wireWord8, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l38Dead : optimized 5 r43l38.1 r43l38.2 = false := by decide +kernel
def r43l39 : S := (0, [wireWord37, wireWord0, wireWord8, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l39Dead : optimized 5 r43l39.1 r43l39.2 = false := by decide +kernel
def r43l40 : S := (0, [wireWord36, wireWord0, wireWord8, wireWord2, wireWord1, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l40Dead : optimized 5 r43l40.1 r43l40.2 = false := by decide +kernel
def r43l41 : S := (0, [wireWord21, wireWord1, wireWord8, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l41Dead : optimized 5 r43l41.1 r43l41.2 = false := by decide +kernel
def r43l42 : S := (0, [wireWord38, wireWord1, wireWord8, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l42Dead : optimized 5 r43l42.1 r43l42.2 = false := by decide +kernel
def r43l43 : S := (0, [wireWord22, wireWord1, wireWord8, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l43Dead : optimized 5 r43l43.1 r43l43.2 = false := by decide +kernel
def r43l44 : S := (0, [wireWord29, wireWord1, wireWord8, wireWord2, wireWord0, wireWord3])
set_option maxHeartbeats 0 in
theorem r43l44Dead : optimized 5 r43l44.1 r43l44.2 = false := by decide +kernel
def r43l45 : S := (0, [wireWord15, wireWord3, wireWord8, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l45Dead : optimized 5 r43l45.1 r43l45.2 = false := by decide +kernel
def r43l46 : S := (0, [wireWord14, wireWord3, wireWord8, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l46Dead : optimized 5 r43l46.1 r43l46.2 = false := by decide +kernel
def r43l47 : S := (0, [wireWord16, wireWord3, wireWord8, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l47Dead : optimized 5 r43l47.1 r43l47.2 = false := by decide +kernel
def r43l48 : S := (0, [wireWord17, wireWord3, wireWord8, wireWord2, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l48Dead : optimized 5 r43l48.1 r43l48.2 = false := by decide +kernel
def r43l49 : S := (0, [wireWord5, wireWord2, wireWord8, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l49Dead : optimized 5 r43l49.1 r43l49.2 = false := by decide +kernel
def r43l50 : S := (0, [wireWord7, wireWord2, wireWord8, wireWord4, wireWord0, wireWord1])
set_option maxHeartbeats 0 in
theorem r43l50Dead : optimized 5 r43l50.1 r43l50.2 = false := by decide +kernel
theorem rootCell43Dead : optimized 6 rootCell43.1 rootCell43.2 = false := by
  have kids : nexts (rootCell43.1, rootCell43.2) = [r43l0,r43l1,r43l2,r43l3,r43l4,r43l5,r43l6,r43l7,r43l8,r43l9,r43l10,r43l11,r43l12,r43l13,r43l14,r43l15,r43l16,r43l17,r43l18,r43l19,r43l20,r43l21,r43l22,r43l23,r43l24,r43l25,r43l26,r43l27,r43l28,r43l29,r43l30,r43l31,r43l32,r43l33,r43l34,r43l35,r43l36,r43l37,r43l38,r43l39,r43l40,r43l41,r43l42,r43l43,r43l44,r43l45,r43l46,r43l47,r43l48,r43l49,r43l50] := by decide +kernel
  have stop : (rootCell43.2 == [goal] || rootCell43.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, r43l0Dead, r43l1Dead, r43l2Dead, r43l3Dead, r43l4Dead, r43l5Dead, r43l6Dead, r43l7Dead, r43l8Dead, r43l9Dead, r43l10Dead, r43l11Dead, r43l12Dead, r43l13Dead, r43l14Dead, r43l15Dead, r43l16Dead, r43l17Dead, r43l18Dead, r43l19Dead, r43l20Dead, r43l21Dead, r43l22Dead, r43l23Dead, r43l24Dead, r43l25Dead, r43l26Dead, r43l27Dead, r43l28Dead, r43l29Dead, r43l30Dead, r43l31Dead, r43l32Dead, r43l33Dead, r43l34Dead, r43l35Dead, r43l36Dead, r43l37Dead, r43l38Dead, r43l39Dead, r43l40Dead, r43l41Dead, r43l42Dead, r43l43Dead, r43l44Dead, r43l45Dead, r43l46Dead, r43l47Dead, r43l48Dead, r43l49Dead, r43l50Dead]
end PEqualNP.Outside.L_meta_16093_counterproof

namespace PEqualNP.Outside.L_meta_16093_counterproof
def initialCell : S := (3, [wireWord0, wireWord1, wireWord3, wireWord4, wireWord2])
theorem initialCellDead : optimized 7 initialCell.1 initialCell.2 = false := by
  have kids : nexts (initialCell.1, initialCell.2) = [rootCell0,rootCell1,rootCell2,rootCell3,rootCell4,rootCell5,rootCell6,rootCell7,rootCell8,rootCell9,rootCell10,rootCell11,rootCell12,rootCell13,rootCell14,rootCell15,rootCell16,rootCell17,rootCell18,rootCell19,rootCell20,rootCell21,rootCell22,rootCell23,rootCell24,rootCell25,rootCell26,rootCell27,rootCell28,rootCell29,rootCell30,rootCell31,rootCell32,rootCell33,rootCell34,rootCell35,rootCell36,rootCell37,rootCell38,rootCell39,rootCell40,rootCell41,rootCell42,rootCell43] := by decide +kernel
  have stop : (initialCell.2 == [goal] || initialCell.2 == [~~~goal]) = false := by decide +kernel
  rw [opt_next, stop, Bool.false_or, kids]
  simp only [List.any_cons, List.any_nil, Bool.or_self, rootCell0Dead, rootCell1Dead, rootCell2Dead, rootCell3Dead, rootCell4Dead, rootCell5Dead, rootCell6Dead, rootCell7Dead, rootCell8Dead, rootCell9Dead, rootCell10Dead, rootCell11Dead, rootCell12Dead, rootCell13Dead, rootCell14Dead, rootCell15Dead, rootCell16Dead, rootCell17Dead, rootCell18Dead, rootCell19Dead, rootCell20Dead, rootCell21Dead, rootCell22Dead, rootCell23Dead, rootCell24Dead, rootCell25Dead, rootCell26Dead, rootCell27Dead, rootCell28Dead, rootCell29Dead, rootCell30Dead, rootCell31Dead, rootCell32Dead, rootCell33Dead, rootCell34Dead, rootCell35Dead, rootCell36Dead, rootCell37Dead, rootCell38Dead, rootCell39Dead, rootCell40Dead, rootCell41Dead, rootCell42Dead, rootCell43Dead]
-- The sampled five-input function cannot be computed with seven binary gates.
theorem noSmallF : search 7 ins = false := by
  have filter_ok : ins.sublists.all (fun s => s == ins || cuts s != -1) = true := by decide +kernel
  have no_root : optimized 7 3 ins = false := initialCellDead
  unfold search
  apply List.any_eq_false.mpr
  intro s hs
  have h := (List.all_eq_true.mp filter_ok) s hs
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
  rcases h with rfl | h
  · change ¬ (_ && _ && optimized 7 3 ins) = true
    rw [no_root, Bool.and_false]
    decide
  · have hn : (cuts s == -1) = false := beq_eq_false_iff_ne.mpr h
    rw [hn, Bool.and_false, Bool.false_and]
    decide
end PEqualNP.Outside.L_meta_16093_counterproof
theorem PEqualNP.Outside.L_meta_16093_counterproof : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∧ C.size ≤ 9 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936938664 * 2 ^ 32 + 3936913544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :=
  PEqualNP.Outside.L_meta_16093_counterproof_closing PEqualNP.Outside.L_meta_16093_counterproof.noSmallF

#print axioms PEqualNP.Outside.L_meta_16093_counterproof
