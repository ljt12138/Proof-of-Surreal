# Formal Proof of Surreal (NOI D2T2)

## Introduction

This is a formal proof (in lean theorem prover) of the main theorem for surreal (超现实数, in NOI 2020 D2T2), that is a set of tree is almost complete if and only if every sufficiently high tree can be growed from it. 

For more details of the problem, see https://loj.ac/problem/3343 (in Chinese) for statement and https://github.com/ljt12138/ljt12138.github.io/blob/master/files/problems/noi20_report.pdf (in Chinese) for solution containing an informal mathematical proof.  

## Theorem 

- `defs.lean` contains definitions of tree, branch, grow and almost complete. Most of the properties are inductively defined, and the correctness of definition is straightforward. 
- `single.lean` only contains two simple result of grow, which are used frequently. 
- `height.lean` contains important facts about height of tree and `height_bound` of list of trees. 
- `branch.lean` contains lemmas about branches, in which three lemmas are important
  - `grow_high_tree`: any branch can grow to an arbitrarily large branch. 
  - `branch_grow`: those trees that grows to a branch is also branches. 
  - `branch_prefix`: suppose two trees grows to the same branch (clearly they are branches by lemma branch_grow), then one of them grows to the other one.
- `grow.lean` mainly contains two key properties of grow, 
  - `grow_trans`: grow is transitive, 
  - `kernel_lemma`: for any tree and any integer `h` which is smaller or equals to its height, there exists a branch of height `h` growing to it. 
- `finite.lean` contains a counting argument, namely for any integer `h`, there are only finitely many trees with height smaller than or equals to `h`.
- `thm.lean` contains the proof of the main theorem. 

## Dependency

In order to build or use this proof, it is necessary to install `lean` and `mathlib`. See `https://leanprover-community.github.io/` for detail. 

If `mathlib` is not globally installed, you need to run `leanproject add-mathlib` to add mathlib to the project. You can use `leanproject build` to build the project and get `*.olean`.

