This repo is an AI-assisted Lean 4 formalization of the textbook _Measure-Theoretic Probability: With Applications to Statistics, Finance, and Engineering_  (Birkhauser, Compact Textbooks in Mathematics, [Publisher's webpage](https://link.springer.com/book/10.1007/978-3-031-49830-5)). This is a textbook for a second course in probability theory.
  
---
### Contributors 

This formalization project was developed by **Shuo Deng**, with assistance from ChatGPT and the ToyApollo project.

---

### Number of definitions and theorems formulated

We formulate all definitions and verify all theorems in the book. Selected examples and exercises are also formulated.

| Type       | Count |
| ---------- | ----- |
| Definition | 81    |
| Theorem    | 127   |
| Example    | 107   |
| Problem    | 134   |
#### Naming convention

- `def_C_N` / `thm_C_N` / `ex_C_S_N` / `prob_C_N` -- definition / theorem / example / problem, where `C` is the chapter, `S` is the section, and `N` is a number.  For example, `def_2_1` is Definition 2.1 in the textbook.

- Module like `thm_9_5_2` with an extra numeric suffix is a **task-owned decomposition module**. It is a helper lemma for the parent task (`thm_9_5`). 

---

### Some special terminology 

**Bridge.** A module that translates between three vocabularies: the textbook's conventions, the project's local definitions, and Mathlib's APIs. 

For examples: 
- `rs_stieltjes_measure_bridge` (Riemann–Stieltjes interface), 
- `gamma_beta_bridge`, 
- `dirichlet_simplex_bridge`. 
A bridge is an interface, not a workaround for a single proof. 

**Support layers.** The project distinguishes: 
- _task parent_ -- the module exposing the final statement for one textbook item 
- _proof-layer support_ -- large single-purpose proof machinery owned by one task, 
- _interface support_ -- the same as bridges as above, and 
- _shared support_ -- module that supports several tasks, e.g. `Support.IIDWord`. 

--- 

### Lean version

`leanprover/lean4:v4.31.0`

---

