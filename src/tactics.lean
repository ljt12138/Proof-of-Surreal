import tactic defs single height

lemma branch_left : ∀ t, ⟨t⟩ → ⟨⟦t∣⟧⟩ :=
begin intros, apply is_branch.left_nl, assumption end

lemma branch_left_leaf : ∀ t, ⟨t⟩ → ⟨⟦t,●⟧⟩ := 
begin intros, apply is_branch.left_l, assumption end

lemma branch_right : ∀ t, ⟨t⟩ → ⟨⟦∣t⟧⟩ :=
begin intros, apply is_branch.right_nl, assumption end

lemma branch_right_leaf : ∀ t, ⟨t⟩ → ⟨⟦●,t⟧⟩ :=
begin intros, apply is_branch.right_l, assumption end 
  
meta def auto_branch_core : tactic unit := 
do
  h ← tactic.target,
  match h with 
  | `(is_branch %%b):= 
      match b with 
      | `(●)      := tactic.exact `(is_branch.single)
      | `(⟦%%t∣⟧) := do tactic.applyc `branch_left, auto_branch_core  
      | `(⟦∣%%t⟧) := do tactic.applyc `branch_right, auto_branch_core
      | `(⟦%%t,●⟧):= do tactic.applyc `branch_left_leaf,
                        auto_branch_core
      | `(⟦●,%%t⟧):= do tactic.applyc `branch_right_leaf,
                        auto_branch_core
      | _      := tactic.try (tactic.assumption <|> tactic.tautology)
      end
  | _ := tactic.fail "should not exists"
  end

meta def reduce_trivial_tree_core : list expr → tactic unit 
| [] := tactic.skip
| (h :: hs) := do t ← tactic.infer_type h, 
                  match t with 
                  | `(%%b ↣ ●) := tactic.replace h.to_string ``(single_grow %%b %%h)
                  | `(height %%b ≤ 1) := tactic.replace h.to_string ``(height_le1_single %%b %%h)
                  | _ := tactic.skip
                  end,
                  reduce_trivial_tree_core hs

meta def reduce_trivial_tree : tactic unit :=
do 
  h ← tactic.local_context,
  reduce_trivial_tree_core h
 
meta def rewrite_ci_core : list expr → tactic unit
| [] := tactic.skip
| (h :: hs) := do t ← tactic.infer_type h,
                  match t with
                  | `(%%b = ●) := tactic.try (tactic.subst h)
                  | _ := tactic.skip
                  end,
                  rewrite_ci_core hs

meta def rewrite_ci : tactic unit := 
do
  reduce_trivial_tree,
  h ← tactic.local_context,
  rewrite_ci_core h

meta def auto_grow_core : tactic unit := 
 do h ← tactic.target, 
   match h with 
   | `(grow %%t %%t') :=  
          match t, t' with 
          | `(●), _ := tactic.applyc `grow.single_grow
          | `(⟦%%u∣⟧), `(⟦%%u'∣⟧) := 
                       do tactic.applyc `grow.left_grow, 
                          auto_grow_core
          | `(⟦∣%%v⟧), `(⟦∣%%v'⟧) := 
                       do tactic.applyc `grow.right_grow,
                          auto_grow_core
          | `(⟦%%u, %%v⟧), `(⟦%%u', %%v'⟧) := 
                       do tactic.applyc `grow.full_grow,
                          auto_grow_core, 
                          auto_grow_core
          | _, _ := tactic.try (tactic.assumption <|> tactic.tautology)
          end
   | _ := tactic.fail "should not exists"
   end

meta def auto_grow : tactic unit := 
do
  rewrite_ci,
  auto_grow_core


meta def auto_branch : tactic unit := 
do
  rewrite_ci,
  auto_branch_core
