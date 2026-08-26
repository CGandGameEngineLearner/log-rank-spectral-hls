import Mathlib

namespace AffineSectionLogRank

/-- A binary decision tree whose internal nodes query coordinates. -/
inductive CoordinateDecisionTree (ι : Type*) where
  | leaf : Bool → CoordinateDecisionTree ι
  | node : ι → CoordinateDecisionTree ι → CoordinateDecisionTree ι →
      CoordinateDecisionTree ι

namespace CoordinateDecisionTree

variable {ι : Type*}

def depth : CoordinateDecisionTree ι → ℕ
  | leaf _ => 0
  | node _ zero one => max zero.depth one.depth + 1

def nodeCount : CoordinateDecisionTree ι → ℕ
  | leaf _ => 0
  | node _ zero one => zero.nodeCount + one.nodeCount + 1

def eval : CoordinateDecisionTree ι → (ι → Bool) → Bool
  | leaf value, _ => value
  | node query zero one, x => if x query then one.eval x else zero.eval x

def relabel (π : ι ≃ ι) : CoordinateDecisionTree ι → CoordinateDecisionTree ι
  | leaf value => leaf value
  | node query zero one => node (π query) (zero.relabel π) (one.relabel π)

@[simp] theorem depth_relabel (π : ι ≃ ι) (tree : CoordinateDecisionTree ι) :
    (tree.relabel π).depth = tree.depth := by
  induction tree with
  | leaf value => rfl
  | node query zero one ihzero ihone =>
      simp [relabel, depth, ihzero, ihone]

@[simp] theorem nodeCount_relabel
    (π : ι ≃ ι) (tree : CoordinateDecisionTree ι) :
    (tree.relabel π).nodeCount = tree.nodeCount := by
  induction tree with
  | leaf value => rfl
  | node query zero one ihzero ihone =>
      simp [relabel, nodeCount, ihzero, ihone]

theorem eval_relabel (π : ι ≃ ι) (tree : CoordinateDecisionTree ι)
    (x : ι → Bool) :
    (tree.relabel π).eval x = tree.eval (fun i => x (π i)) := by
  induction tree with
  | leaf value => rfl
  | node query zero one ihzero ihone =>
      simp only [relabel, eval]
      rw [ihzero, ihone]

/-- The number of internal nodes is strictly smaller than `2^depth`. -/
theorem nodeCount_add_one_le_two_pow_depth (tree : CoordinateDecisionTree ι) :
    tree.nodeCount + 1 ≤ 2 ^ tree.depth := by
  induction tree with
  | leaf value => simp [nodeCount, depth]
  | node query zero one ihzero ihone =>
      let m := max zero.depth one.depth
      have hz : 2 ^ zero.depth ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have ho : 2 ^ one.depth ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      calc
        (node query zero one).nodeCount + 1 =
            (zero.nodeCount + 1) + (one.nodeCount + 1) := by
              simp [nodeCount]
              omega
        _ ≤ 2 ^ zero.depth + 2 ^ one.depth := Nat.add_le_add ihzero ihone
        _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add hz ho
        _ = 2 ^ (m + 1) := by rw [pow_succ]; omega
        _ = 2 ^ (node query zero one).depth := by simp [depth, m]

def support [DecidableEq ι] : CoordinateDecisionTree ι → Finset ι
  | leaf _ => ∅
  | node query zero one => insert query (zero.support ∪ one.support)

/-- A depth-`q` tree queries fewer than `2^q` distinct coordinates. -/
theorem support_card_le_nodeCount [DecidableEq ι]
    (tree : CoordinateDecisionTree ι) :
    tree.support.card ≤ tree.nodeCount := by
  induction tree with
  | leaf value => simp [support, nodeCount]
  | node query zero one ihzero ihone =>
      calc
        (node query zero one).support.card =
            (insert query (zero.support ∪ one.support)).card := rfl
        _ ≤ (zero.support ∪ one.support).card + 1 :=
          Finset.card_insert_le query (zero.support ∪ one.support)
        _ ≤ zero.support.card + one.support.card + 1 := by
          have hu := Finset.card_union_le zero.support one.support
          omega
        _ ≤ zero.nodeCount + one.nodeCount + 1 := by omega
        _ = (node query zero one).nodeCount := rfl

theorem support_card_lt_two_pow_depth [DecidableEq ι]
    (tree : CoordinateDecisionTree ι) :
    tree.support.card < 2 ^ tree.depth := by
  have hsupport := support_card_le_nodeCount tree
  have hnodes := nodeCount_add_one_le_two_pow_depth tree
  omega

/-- The union of supports of `r` trees of depth at most `q` has size at most
`r * 2^q`.  This is the finite support-counting input to rank-pooled query
transfer. -/
theorem card_biUnion_support_le_card_mul_two_pow
    {κ : Type*} [Fintype κ] [DecidableEq ι]
    (tree : κ → CoordinateDecisionTree ι) (q : ℕ)
    (hdepth : ∀ j, (tree j).depth ≤ q) :
    ((Finset.univ : Finset κ).biUnion fun j => (tree j).support).card ≤
      Fintype.card κ * 2 ^ q := by
  apply Finset.card_biUnion_le_card_mul
  intro j hj
  have hsupport := support_card_lt_two_pow_depth (tree j)
  have hpow : 2 ^ (tree j).depth ≤ 2 ^ q :=
    Nat.pow_le_pow_right (by omega) (hdepth j)
  omega

end CoordinateDecisionTree

end AffineSectionLogRank
